// Lean compiler output
// Module: Init.Grind.Module.NatModuleNorm
// Imports: Init.Grind.Ordered.Linarith Init.Data.AC Init.Data.Int.DivMod.Lemmas Init.Data.Int.LemmasAux Init.Omega
use crate::r#gen::Init::Data::AC::{initialize_Init_Data_AC, runtime_initialize_Init_Data_AC};
use crate::r#gen::Init::Data::Int::DivMod::Lemmas::{
    initialize_Init_Data_Int_DivMod_Lemmas, runtime_initialize_Init_Data_Int_DivMod_Lemmas,
};
use crate::r#gen::Init::Data::Int::LemmasAux::{
    initialize_Init_Data_Int_LemmasAux, runtime_initialize_Init_Data_Int_LemmasAux,
};
use crate::r#gen::Init::Data::RArray::l_Lean_RArray_getImpl___redArg;
use crate::r#gen::Init::Grind::Ordered::Linarith::{
    initialize_Init_Grind_Ordered_Linarith, l_Lean_Grind_Linarith_Poly_combine,
    l_Lean_Grind_Linarith_Poly_mul, l_Lean_Grind_Linarith_instBEqPoly_beq,
    runtime_initialize_Init_Grind_Ordered_Linarith,
};
use crate::r#gen::Init::Omega::{initialize_Init_Omega, runtime_initialize_Init_Omega};
use crate::lean_imports_rs::Init::Data::Int::Basic::{
    lean_int_dec_lt, lean_nat_abs, lean_nat_to_int,
};
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_alloc_ctor, lean_apply_1, lean_apply_2, lean_apply_3,
    lean_box, lean_ctor_get, lean_ctor_set, lean_dec, lean_dec_ref, lean_dec_ref_known, lean_inc,
    lean_inc_ref, lean_io_result_is_error, lean_io_result_mk_ok, lean_obj_once, lean_obj_tag,
    lean_unsigned_to_nat,
};
static mut l_Lean_Grind_Linarith_Poly_denoteN___redArg___closed__0_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Grind_Linarith_Poly_denoteN___redArg___closed__0: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Grind_Linarith_Expr_toPolyN___closed__0_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Grind_Linarith_Expr_toPolyN___closed__0: *mut LeanObject = core::ptr::null_mut();
pub unsafe fn l_Lean_Grind_Linarith_Expr_denoteN___redArg(
    mut v_inst_192_: *mut LeanObject,
    mut v_ctx_193_: *mut LeanObject,
    mut v_x_194_: *mut LeanObject,
) -> *mut LeanObject {
    match lean_obj_tag(v_x_194_) {
        0 => {
            let mut v_toAddCommMonoid_195_: *mut LeanObject = core::ptr::null_mut();
            let mut v_toZero_196_: *mut LeanObject = core::ptr::null_mut();
            v_toAddCommMonoid_195_ = lean_ctor_get(v_inst_192_, 0);
            lean_inc_ref(v_toAddCommMonoid_195_);
            lean_dec_ref(v_inst_192_);
            v_toZero_196_ = lean_ctor_get(v_toAddCommMonoid_195_, 0);
            lean_inc(v_toZero_196_);
            lean_dec_ref(v_toAddCommMonoid_195_);
            return v_toZero_196_;
        }
        1 => {
            let mut v_i_197_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_198_: *mut LeanObject = core::ptr::null_mut();
            lean_dec_ref(v_inst_192_);
            v_i_197_ = lean_ctor_get(v_x_194_, 0);
            lean_inc(v_i_197_);
            lean_dec_ref_known(v_x_194_, 1);
            v___x_198_ = l_Lean_RArray_getImpl___redArg(v_ctx_193_, v_i_197_);
            lean_dec(v_i_197_);
            return v___x_198_;
        }
        2 => {
            let mut v_toAddCommMonoid_199_: *mut LeanObject = core::ptr::null_mut();
            let mut v_toAdd_200_: *mut LeanObject = core::ptr::null_mut();
            let mut v_a_201_: *mut LeanObject = core::ptr::null_mut();
            let mut v_b_202_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_203_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_204_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_205_: *mut LeanObject = core::ptr::null_mut();
            v_toAddCommMonoid_199_ = lean_ctor_get(v_inst_192_, 0);
            v_toAdd_200_ = lean_ctor_get(v_toAddCommMonoid_199_, 1);
            lean_inc(v_toAdd_200_);
            v_a_201_ = lean_ctor_get(v_x_194_, 0);
            lean_inc(v_a_201_);
            v_b_202_ = lean_ctor_get(v_x_194_, 1);
            lean_inc(v_b_202_);
            lean_dec_ref_known(v_x_194_, 2);
            lean_inc_ref(v_inst_192_);
            v___x_203_ =
                l_Lean_Grind_Linarith_Expr_denoteN___redArg(v_inst_192_, v_ctx_193_, v_a_201_);
            v___x_204_ =
                l_Lean_Grind_Linarith_Expr_denoteN___redArg(v_inst_192_, v_ctx_193_, v_b_202_);
            v___x_205_ = lean_apply_2(v_toAdd_200_, v___x_203_, v___x_204_);
            return v___x_205_;
        }
        5 => {
            let mut v_nsmul_206_: *mut LeanObject = core::ptr::null_mut();
            let mut v_k_207_: *mut LeanObject = core::ptr::null_mut();
            let mut v_a_208_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_209_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_210_: *mut LeanObject = core::ptr::null_mut();
            v_nsmul_206_ = lean_ctor_get(v_inst_192_, 1);
            lean_inc(v_nsmul_206_);
            v_k_207_ = lean_ctor_get(v_x_194_, 0);
            lean_inc(v_k_207_);
            v_a_208_ = lean_ctor_get(v_x_194_, 1);
            lean_inc(v_a_208_);
            lean_dec_ref_known(v_x_194_, 2);
            v___x_209_ =
                l_Lean_Grind_Linarith_Expr_denoteN___redArg(v_inst_192_, v_ctx_193_, v_a_208_);
            v___x_210_ = lean_apply_2(v_nsmul_206_, v_k_207_, v___x_209_);
            return v___x_210_;
        }
        _ => {
            let mut v_toAddCommMonoid_211_: *mut LeanObject = core::ptr::null_mut();
            let mut v_toZero_212_: *mut LeanObject = core::ptr::null_mut();
            v_toAddCommMonoid_211_ = lean_ctor_get(v_inst_192_, 0);
            lean_inc_ref(v_toAddCommMonoid_211_);
            lean_dec(v_x_194_);
            lean_dec_ref(v_inst_192_);
            v_toZero_212_ = lean_ctor_get(v_toAddCommMonoid_211_, 0);
            lean_inc(v_toZero_212_);
            lean_dec_ref(v_toAddCommMonoid_211_);
            return v_toZero_212_;
        }
    }
}
pub unsafe fn l_Lean_Grind_Linarith_Expr_denoteN___redArg___boxed(
    mut v_inst_213_: *mut LeanObject,
    mut v_ctx_214_: *mut LeanObject,
    mut v_x_215_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_216_: *mut LeanObject = core::ptr::null_mut();
    v_res_216_ = l_Lean_Grind_Linarith_Expr_denoteN___redArg(v_inst_213_, v_ctx_214_, v_x_215_);
    lean_dec_ref(v_ctx_214_);
    return v_res_216_;
}
pub unsafe fn l_Lean_Grind_Linarith_Expr_denoteN(
    mut v_00_u03b1_217_: *mut LeanObject,
    mut v_inst_218_: *mut LeanObject,
    mut v_ctx_219_: *mut LeanObject,
    mut v_x_220_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_221_: *mut LeanObject = core::ptr::null_mut();
    v___x_221_ = l_Lean_Grind_Linarith_Expr_denoteN___redArg(v_inst_218_, v_ctx_219_, v_x_220_);
    return v___x_221_;
}
pub unsafe fn l_Lean_Grind_Linarith_Expr_denoteN___boxed(
    mut v_00_u03b1_222_: *mut LeanObject,
    mut v_inst_223_: *mut LeanObject,
    mut v_ctx_224_: *mut LeanObject,
    mut v_x_225_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_226_: *mut LeanObject = core::ptr::null_mut();
    v_res_226_ =
        l_Lean_Grind_Linarith_Expr_denoteN(v_00_u03b1_222_, v_inst_223_, v_ctx_224_, v_x_225_);
    lean_dec_ref(v_ctx_224_);
    return v_res_226_;
}
pub unsafe fn _init_l_Lean_Grind_Linarith_Poly_denoteN___redArg___closed__0() -> *mut LeanObject {
    let mut v___x_227_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_228_: *mut LeanObject = core::ptr::null_mut();
    v___x_227_ = lean_unsigned_to_nat(0);
    v___x_228_ = lean_nat_to_int(v___x_227_);
    return v___x_228_;
}
pub unsafe fn l_Lean_Grind_Linarith_Poly_denoteN___redArg(
    mut v_inst_229_: *mut LeanObject,
    mut v_ctx_230_: *mut LeanObject,
    mut v_p_231_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_p_231_) == 0 {
        let mut v_toAddCommMonoid_232_: *mut LeanObject = core::ptr::null_mut();
        let mut v_toZero_233_: *mut LeanObject = core::ptr::null_mut();
        v_toAddCommMonoid_232_ = lean_ctor_get(v_inst_229_, 0);
        lean_inc_ref(v_toAddCommMonoid_232_);
        lean_dec_ref(v_inst_229_);
        v_toZero_233_ = lean_ctor_get(v_toAddCommMonoid_232_, 0);
        lean_inc(v_toZero_233_);
        lean_dec_ref(v_toAddCommMonoid_232_);
        return v_toZero_233_;
    } else {
        let mut v_toAddCommMonoid_234_: *mut LeanObject = core::ptr::null_mut();
        let mut v_nsmul_235_: *mut LeanObject = core::ptr::null_mut();
        let mut v_toZero_236_: *mut LeanObject = core::ptr::null_mut();
        let mut v_toAdd_237_: *mut LeanObject = core::ptr::null_mut();
        let mut v_k_238_: *mut LeanObject = core::ptr::null_mut();
        let mut v_v_239_: *mut LeanObject = core::ptr::null_mut();
        let mut v_p_240_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_241_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_242_: u8 = 0;
        v_toAddCommMonoid_234_ = lean_ctor_get(v_inst_229_, 0);
        v_nsmul_235_ = lean_ctor_get(v_inst_229_, 1);
        v_toZero_236_ = lean_ctor_get(v_toAddCommMonoid_234_, 0);
        v_toAdd_237_ = lean_ctor_get(v_toAddCommMonoid_234_, 1);
        lean_inc(v_toAdd_237_);
        v_k_238_ = lean_ctor_get(v_p_231_, 0);
        v_v_239_ = lean_ctor_get(v_p_231_, 1);
        v_p_240_ = lean_ctor_get(v_p_231_, 2);
        v___x_241_ = lean_obj_once(
            core::ptr::addr_of_mut!(l_Lean_Grind_Linarith_Poly_denoteN___redArg___closed__0),
            core::ptr::addr_of_mut!(l_Lean_Grind_Linarith_Poly_denoteN___redArg___closed__0_once),
            _init_l_Lean_Grind_Linarith_Poly_denoteN___redArg___closed__0,
        );
        v___x_242_ = lean_int_dec_lt(v_k_238_, v___x_241_);
        if v___x_242_ == 0 {
            let mut v___x_243_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_244_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_245_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_246_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_247_: *mut LeanObject = core::ptr::null_mut();
            v___x_243_ = lean_nat_abs(v_k_238_);
            v___x_244_ = l_Lean_RArray_getImpl___redArg(v_ctx_230_, v_v_239_);
            lean_inc(v_nsmul_235_);
            v___x_245_ = lean_apply_2(v_nsmul_235_, v___x_243_, v___x_244_);
            v___x_246_ =
                l_Lean_Grind_Linarith_Poly_denoteN___redArg(v_inst_229_, v_ctx_230_, v_p_240_);
            v___x_247_ = lean_apply_2(v_toAdd_237_, v___x_245_, v___x_246_);
            return v___x_247_;
        } else {
            lean_inc(v_toZero_236_);
            lean_dec(v_toAdd_237_);
            lean_dec_ref(v_inst_229_);
            return v_toZero_236_;
        }
    }
}
pub unsafe fn l_Lean_Grind_Linarith_Poly_denoteN___redArg___boxed(
    mut v_inst_248_: *mut LeanObject,
    mut v_ctx_249_: *mut LeanObject,
    mut v_p_250_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_251_: *mut LeanObject = core::ptr::null_mut();
    v_res_251_ = l_Lean_Grind_Linarith_Poly_denoteN___redArg(v_inst_248_, v_ctx_249_, v_p_250_);
    lean_dec(v_p_250_);
    lean_dec_ref(v_ctx_249_);
    return v_res_251_;
}
pub unsafe fn l_Lean_Grind_Linarith_Poly_denoteN(
    mut v_00_u03b1_252_: *mut LeanObject,
    mut v_inst_253_: *mut LeanObject,
    mut v_ctx_254_: *mut LeanObject,
    mut v_p_255_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_256_: *mut LeanObject = core::ptr::null_mut();
    v___x_256_ = l_Lean_Grind_Linarith_Poly_denoteN___redArg(v_inst_253_, v_ctx_254_, v_p_255_);
    return v___x_256_;
}
pub unsafe fn l_Lean_Grind_Linarith_Poly_denoteN___boxed(
    mut v_00_u03b1_257_: *mut LeanObject,
    mut v_inst_258_: *mut LeanObject,
    mut v_ctx_259_: *mut LeanObject,
    mut v_p_260_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_261_: *mut LeanObject = core::ptr::null_mut();
    v_res_261_ =
        l_Lean_Grind_Linarith_Poly_denoteN(v_00_u03b1_257_, v_inst_258_, v_ctx_259_, v_p_260_);
    lean_dec(v_p_260_);
    lean_dec_ref(v_ctx_259_);
    return v_res_261_;
}
pub unsafe fn l___private_Init_Grind_Module_NatModuleNorm_0__Lean_Grind_Linarith_Poly_denoteN_match__1_splitter___redArg(
    mut v_p_262_: *mut LeanObject,
    mut v_h__1_263_: *mut LeanObject,
    mut v_h__2_264_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_p_262_) == 0 {
        let mut v___x_265_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_266_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_264_);
        v___x_265_ = lean_box(0);
        v___x_266_ = lean_apply_1(v_h__1_263_, v___x_265_);
        return v___x_266_;
    } else {
        let mut v_k_267_: *mut LeanObject = core::ptr::null_mut();
        let mut v_v_268_: *mut LeanObject = core::ptr::null_mut();
        let mut v_p_269_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_270_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_263_);
        v_k_267_ = lean_ctor_get(v_p_262_, 0);
        lean_inc(v_k_267_);
        v_v_268_ = lean_ctor_get(v_p_262_, 1);
        lean_inc(v_v_268_);
        v_p_269_ = lean_ctor_get(v_p_262_, 2);
        lean_inc(v_p_269_);
        lean_dec_ref_known(v_p_262_, 3);
        v___x_270_ = lean_apply_3(v_h__2_264_, v_k_267_, v_v_268_, v_p_269_);
        return v___x_270_;
    }
}
pub unsafe fn l___private_Init_Grind_Module_NatModuleNorm_0__Lean_Grind_Linarith_Poly_denoteN_match__1_splitter(
    mut v_motive_271_: *mut LeanObject,
    mut v_p_272_: *mut LeanObject,
    mut v_h__1_273_: *mut LeanObject,
    mut v_h__2_274_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_p_272_) == 0 {
        let mut v___x_275_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_276_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_274_);
        v___x_275_ = lean_box(0);
        v___x_276_ = lean_apply_1(v_h__1_273_, v___x_275_);
        return v___x_276_;
    } else {
        let mut v_k_277_: *mut LeanObject = core::ptr::null_mut();
        let mut v_v_278_: *mut LeanObject = core::ptr::null_mut();
        let mut v_p_279_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_280_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_273_);
        v_k_277_ = lean_ctor_get(v_p_272_, 0);
        lean_inc(v_k_277_);
        v_v_278_ = lean_ctor_get(v_p_272_, 1);
        lean_inc(v_v_278_);
        v_p_279_ = lean_ctor_get(v_p_272_, 2);
        lean_inc(v_p_279_);
        lean_dec_ref_known(v_p_272_, 3);
        v___x_280_ = lean_apply_3(v_h__2_274_, v_k_277_, v_v_278_, v_p_279_);
        return v___x_280_;
    }
}
pub unsafe fn l___private_Init_Grind_Module_NatModuleNorm_0__Lean_Grind_Linarith_Poly_denote_match__1_splitter___redArg(
    mut v_p_281_: *mut LeanObject,
    mut v_h__1_282_: *mut LeanObject,
    mut v_h__2_283_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_p_281_) == 0 {
        let mut v___x_284_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_285_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_283_);
        v___x_284_ = lean_box(0);
        v___x_285_ = lean_apply_1(v_h__1_282_, v___x_284_);
        return v___x_285_;
    } else {
        let mut v_k_286_: *mut LeanObject = core::ptr::null_mut();
        let mut v_v_287_: *mut LeanObject = core::ptr::null_mut();
        let mut v_p_288_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_289_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_282_);
        v_k_286_ = lean_ctor_get(v_p_281_, 0);
        lean_inc(v_k_286_);
        v_v_287_ = lean_ctor_get(v_p_281_, 1);
        lean_inc(v_v_287_);
        v_p_288_ = lean_ctor_get(v_p_281_, 2);
        lean_inc(v_p_288_);
        lean_dec_ref_known(v_p_281_, 3);
        v___x_289_ = lean_apply_3(v_h__2_283_, v_k_286_, v_v_287_, v_p_288_);
        return v___x_289_;
    }
}
pub unsafe fn l___private_Init_Grind_Module_NatModuleNorm_0__Lean_Grind_Linarith_Poly_denote_match__1_splitter(
    mut v_motive_290_: *mut LeanObject,
    mut v_p_291_: *mut LeanObject,
    mut v_h__1_292_: *mut LeanObject,
    mut v_h__2_293_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_p_291_) == 0 {
        let mut v___x_294_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_295_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_293_);
        v___x_294_ = lean_box(0);
        v___x_295_ = lean_apply_1(v_h__1_292_, v___x_294_);
        return v___x_295_;
    } else {
        let mut v_k_296_: *mut LeanObject = core::ptr::null_mut();
        let mut v_v_297_: *mut LeanObject = core::ptr::null_mut();
        let mut v_p_298_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_299_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_292_);
        v_k_296_ = lean_ctor_get(v_p_291_, 0);
        lean_inc(v_k_296_);
        v_v_297_ = lean_ctor_get(v_p_291_, 1);
        lean_inc(v_v_297_);
        v_p_298_ = lean_ctor_get(v_p_291_, 2);
        lean_inc(v_p_298_);
        lean_dec_ref_known(v_p_291_, 3);
        v___x_299_ = lean_apply_3(v_h__2_293_, v_k_296_, v_v_297_, v_p_298_);
        return v___x_299_;
    }
}
pub unsafe fn l_Nat_cast___at___00Lean_Grind_Linarith_Expr_toPolyN_spec__0(
    mut v_a_300_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_301_: *mut LeanObject = core::ptr::null_mut();
    v___x_301_ = lean_nat_to_int(v_a_300_);
    return v___x_301_;
}
pub unsafe fn _init_l_Lean_Grind_Linarith_Expr_toPolyN___closed__0() -> *mut LeanObject {
    let mut v___x_302_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_303_: *mut LeanObject = core::ptr::null_mut();
    v___x_302_ = lean_unsigned_to_nat(1);
    v___x_303_ = lean_nat_to_int(v___x_302_);
    return v___x_303_;
}
pub unsafe fn l_Lean_Grind_Linarith_Expr_toPolyN(mut v_x_304_: *mut LeanObject) -> *mut LeanObject {
    match lean_obj_tag(v_x_304_) {
        0 => {
            let mut v___x_305_: *mut LeanObject = core::ptr::null_mut();
            v___x_305_ = lean_box(0);
            return v___x_305_;
        }
        1 => {
            let mut v_i_306_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_307_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_308_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_309_: *mut LeanObject = core::ptr::null_mut();
            v_i_306_ = lean_ctor_get(v_x_304_, 0);
            lean_inc(v_i_306_);
            lean_dec_ref_known(v_x_304_, 1);
            v___x_307_ = lean_obj_once(
                core::ptr::addr_of_mut!(l_Lean_Grind_Linarith_Expr_toPolyN___closed__0),
                core::ptr::addr_of_mut!(l_Lean_Grind_Linarith_Expr_toPolyN___closed__0_once),
                _init_l_Lean_Grind_Linarith_Expr_toPolyN___closed__0,
            );
            v___x_308_ = lean_box(0);
            v___x_309_ = lean_alloc_ctor(1, 3, (0) as u32);
            lean_ctor_set(v___x_309_, 0, v___x_307_);
            lean_ctor_set(v___x_309_, 1, v_i_306_);
            lean_ctor_set(v___x_309_, 2, v___x_308_);
            return v___x_309_;
        }
        2 => {
            let mut v_a_310_: *mut LeanObject = core::ptr::null_mut();
            let mut v_b_311_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_312_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_313_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_314_: *mut LeanObject = core::ptr::null_mut();
            v_a_310_ = lean_ctor_get(v_x_304_, 0);
            lean_inc(v_a_310_);
            v_b_311_ = lean_ctor_get(v_x_304_, 1);
            lean_inc(v_b_311_);
            lean_dec_ref_known(v_x_304_, 2);
            v___x_312_ = l_Lean_Grind_Linarith_Expr_toPolyN(v_a_310_);
            v___x_313_ = l_Lean_Grind_Linarith_Expr_toPolyN(v_b_311_);
            v___x_314_ = l_Lean_Grind_Linarith_Poly_combine(v___x_312_, v___x_313_);
            return v___x_314_;
        }
        5 => {
            let mut v_k_315_: *mut LeanObject = core::ptr::null_mut();
            let mut v_a_316_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_317_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_318_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_319_: *mut LeanObject = core::ptr::null_mut();
            v_k_315_ = lean_ctor_get(v_x_304_, 0);
            lean_inc(v_k_315_);
            v_a_316_ = lean_ctor_get(v_x_304_, 1);
            lean_inc(v_a_316_);
            lean_dec_ref_known(v_x_304_, 2);
            v___x_317_ = l_Lean_Grind_Linarith_Expr_toPolyN(v_a_316_);
            v___x_318_ = lean_nat_to_int(v_k_315_);
            v___x_319_ = l_Lean_Grind_Linarith_Poly_mul(v___x_317_, v___x_318_);
            lean_dec(v___x_318_);
            return v___x_319_;
        }
        _ => {
            let mut v___x_320_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_x_304_);
            v___x_320_ = lean_box(0);
            return v___x_320_;
        }
    }
}
pub unsafe fn l___private_Init_Grind_Module_NatModuleNorm_0__Lean_Grind_Linarith_Expr_denoteN_match__1_splitter___redArg(
    mut v_x_321_: *mut LeanObject,
    mut v_h__1_322_: *mut LeanObject,
    mut v_h__2_323_: *mut LeanObject,
    mut v_h__3_324_: *mut LeanObject,
    mut v_h__4_325_: *mut LeanObject,
    mut v_h__5_326_: *mut LeanObject,
    mut v_h__6_327_: *mut LeanObject,
    mut v_h__7_328_: *mut LeanObject,
) -> *mut LeanObject {
    match lean_obj_tag(v_x_321_) {
        0 => {
            let mut v___x_329_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_330_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__7_328_);
            lean_dec(v_h__6_327_);
            lean_dec(v_h__5_326_);
            lean_dec(v_h__3_324_);
            lean_dec(v_h__2_323_);
            lean_dec(v_h__1_322_);
            v___x_329_ = lean_box(0);
            v___x_330_ = lean_apply_1(v_h__4_325_, v___x_329_);
            return v___x_330_;
        }
        1 => {
            let mut v_i_331_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_332_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__7_328_);
            lean_dec(v_h__6_327_);
            lean_dec(v_h__4_325_);
            lean_dec(v_h__3_324_);
            lean_dec(v_h__2_323_);
            lean_dec(v_h__1_322_);
            v_i_331_ = lean_ctor_get(v_x_321_, 0);
            lean_inc(v_i_331_);
            lean_dec_ref_known(v_x_321_, 1);
            v___x_332_ = lean_apply_1(v_h__5_326_, v_i_331_);
            return v___x_332_;
        }
        2 => {
            let mut v_a_333_: *mut LeanObject = core::ptr::null_mut();
            let mut v_b_334_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_335_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__7_328_);
            lean_dec(v_h__5_326_);
            lean_dec(v_h__4_325_);
            lean_dec(v_h__3_324_);
            lean_dec(v_h__2_323_);
            lean_dec(v_h__1_322_);
            v_a_333_ = lean_ctor_get(v_x_321_, 0);
            lean_inc(v_a_333_);
            v_b_334_ = lean_ctor_get(v_x_321_, 1);
            lean_inc(v_b_334_);
            lean_dec_ref_known(v_x_321_, 2);
            v___x_335_ = lean_apply_2(v_h__6_327_, v_a_333_, v_b_334_);
            return v___x_335_;
        }
        3 => {
            let mut v_a_336_: *mut LeanObject = core::ptr::null_mut();
            let mut v_b_337_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_338_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__7_328_);
            lean_dec(v_h__6_327_);
            lean_dec(v_h__5_326_);
            lean_dec(v_h__4_325_);
            lean_dec(v_h__3_324_);
            lean_dec(v_h__2_323_);
            v_a_336_ = lean_ctor_get(v_x_321_, 0);
            lean_inc(v_a_336_);
            v_b_337_ = lean_ctor_get(v_x_321_, 1);
            lean_inc(v_b_337_);
            lean_dec_ref_known(v_x_321_, 2);
            v___x_338_ = lean_apply_2(v_h__1_322_, v_a_336_, v_b_337_);
            return v___x_338_;
        }
        4 => {
            let mut v_a_339_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_340_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__7_328_);
            lean_dec(v_h__6_327_);
            lean_dec(v_h__5_326_);
            lean_dec(v_h__4_325_);
            lean_dec(v_h__3_324_);
            lean_dec(v_h__1_322_);
            v_a_339_ = lean_ctor_get(v_x_321_, 0);
            lean_inc(v_a_339_);
            lean_dec_ref_known(v_x_321_, 1);
            v___x_340_ = lean_apply_1(v_h__2_323_, v_a_339_);
            return v___x_340_;
        }
        5 => {
            let mut v_k_341_: *mut LeanObject = core::ptr::null_mut();
            let mut v_a_342_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_343_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__6_327_);
            lean_dec(v_h__5_326_);
            lean_dec(v_h__4_325_);
            lean_dec(v_h__3_324_);
            lean_dec(v_h__2_323_);
            lean_dec(v_h__1_322_);
            v_k_341_ = lean_ctor_get(v_x_321_, 0);
            lean_inc(v_k_341_);
            v_a_342_ = lean_ctor_get(v_x_321_, 1);
            lean_inc(v_a_342_);
            lean_dec_ref_known(v_x_321_, 2);
            v___x_343_ = lean_apply_2(v_h__7_328_, v_k_341_, v_a_342_);
            return v___x_343_;
        }
        _ => {
            let mut v_k_344_: *mut LeanObject = core::ptr::null_mut();
            let mut v_a_345_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_346_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__7_328_);
            lean_dec(v_h__6_327_);
            lean_dec(v_h__5_326_);
            lean_dec(v_h__4_325_);
            lean_dec(v_h__2_323_);
            lean_dec(v_h__1_322_);
            v_k_344_ = lean_ctor_get(v_x_321_, 0);
            lean_inc(v_k_344_);
            v_a_345_ = lean_ctor_get(v_x_321_, 1);
            lean_inc(v_a_345_);
            lean_dec_ref_known(v_x_321_, 2);
            v___x_346_ = lean_apply_2(v_h__3_324_, v_k_344_, v_a_345_);
            return v___x_346_;
        }
    }
}
pub unsafe fn l___private_Init_Grind_Module_NatModuleNorm_0__Lean_Grind_Linarith_Expr_denoteN_match__1_splitter(
    mut v_motive_347_: *mut LeanObject,
    mut v_x_348_: *mut LeanObject,
    mut v_h__1_349_: *mut LeanObject,
    mut v_h__2_350_: *mut LeanObject,
    mut v_h__3_351_: *mut LeanObject,
    mut v_h__4_352_: *mut LeanObject,
    mut v_h__5_353_: *mut LeanObject,
    mut v_h__6_354_: *mut LeanObject,
    mut v_h__7_355_: *mut LeanObject,
) -> *mut LeanObject {
    match lean_obj_tag(v_x_348_) {
        0 => {
            let mut v___x_356_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_357_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__7_355_);
            lean_dec(v_h__6_354_);
            lean_dec(v_h__5_353_);
            lean_dec(v_h__3_351_);
            lean_dec(v_h__2_350_);
            lean_dec(v_h__1_349_);
            v___x_356_ = lean_box(0);
            v___x_357_ = lean_apply_1(v_h__4_352_, v___x_356_);
            return v___x_357_;
        }
        1 => {
            let mut v_i_358_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_359_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__7_355_);
            lean_dec(v_h__6_354_);
            lean_dec(v_h__4_352_);
            lean_dec(v_h__3_351_);
            lean_dec(v_h__2_350_);
            lean_dec(v_h__1_349_);
            v_i_358_ = lean_ctor_get(v_x_348_, 0);
            lean_inc(v_i_358_);
            lean_dec_ref_known(v_x_348_, 1);
            v___x_359_ = lean_apply_1(v_h__5_353_, v_i_358_);
            return v___x_359_;
        }
        2 => {
            let mut v_a_360_: *mut LeanObject = core::ptr::null_mut();
            let mut v_b_361_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_362_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__7_355_);
            lean_dec(v_h__5_353_);
            lean_dec(v_h__4_352_);
            lean_dec(v_h__3_351_);
            lean_dec(v_h__2_350_);
            lean_dec(v_h__1_349_);
            v_a_360_ = lean_ctor_get(v_x_348_, 0);
            lean_inc(v_a_360_);
            v_b_361_ = lean_ctor_get(v_x_348_, 1);
            lean_inc(v_b_361_);
            lean_dec_ref_known(v_x_348_, 2);
            v___x_362_ = lean_apply_2(v_h__6_354_, v_a_360_, v_b_361_);
            return v___x_362_;
        }
        3 => {
            let mut v_a_363_: *mut LeanObject = core::ptr::null_mut();
            let mut v_b_364_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_365_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__7_355_);
            lean_dec(v_h__6_354_);
            lean_dec(v_h__5_353_);
            lean_dec(v_h__4_352_);
            lean_dec(v_h__3_351_);
            lean_dec(v_h__2_350_);
            v_a_363_ = lean_ctor_get(v_x_348_, 0);
            lean_inc(v_a_363_);
            v_b_364_ = lean_ctor_get(v_x_348_, 1);
            lean_inc(v_b_364_);
            lean_dec_ref_known(v_x_348_, 2);
            v___x_365_ = lean_apply_2(v_h__1_349_, v_a_363_, v_b_364_);
            return v___x_365_;
        }
        4 => {
            let mut v_a_366_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_367_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__7_355_);
            lean_dec(v_h__6_354_);
            lean_dec(v_h__5_353_);
            lean_dec(v_h__4_352_);
            lean_dec(v_h__3_351_);
            lean_dec(v_h__1_349_);
            v_a_366_ = lean_ctor_get(v_x_348_, 0);
            lean_inc(v_a_366_);
            lean_dec_ref_known(v_x_348_, 1);
            v___x_367_ = lean_apply_1(v_h__2_350_, v_a_366_);
            return v___x_367_;
        }
        5 => {
            let mut v_k_368_: *mut LeanObject = core::ptr::null_mut();
            let mut v_a_369_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_370_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__6_354_);
            lean_dec(v_h__5_353_);
            lean_dec(v_h__4_352_);
            lean_dec(v_h__3_351_);
            lean_dec(v_h__2_350_);
            lean_dec(v_h__1_349_);
            v_k_368_ = lean_ctor_get(v_x_348_, 0);
            lean_inc(v_k_368_);
            v_a_369_ = lean_ctor_get(v_x_348_, 1);
            lean_inc(v_a_369_);
            lean_dec_ref_known(v_x_348_, 2);
            v___x_370_ = lean_apply_2(v_h__7_355_, v_k_368_, v_a_369_);
            return v___x_370_;
        }
        _ => {
            let mut v_k_371_: *mut LeanObject = core::ptr::null_mut();
            let mut v_a_372_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_373_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__7_355_);
            lean_dec(v_h__6_354_);
            lean_dec(v_h__5_353_);
            lean_dec(v_h__4_352_);
            lean_dec(v_h__2_350_);
            lean_dec(v_h__1_349_);
            v_k_371_ = lean_ctor_get(v_x_348_, 0);
            lean_inc(v_k_371_);
            v_a_372_ = lean_ctor_get(v_x_348_, 1);
            lean_inc(v_a_372_);
            lean_dec_ref_known(v_x_348_, 2);
            v___x_373_ = lean_apply_2(v_h__3_351_, v_k_371_, v_a_372_);
            return v___x_373_;
        }
    }
}
pub unsafe fn l_Lean_Grind_Linarith_eq__normN__cert(
    mut v_lhs_374_: *mut LeanObject,
    mut v_rhs_375_: *mut LeanObject,
) -> u8 {
    let mut v___x_376_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_377_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_378_: u8 = 0;
    v___x_376_ = l_Lean_Grind_Linarith_Expr_toPolyN(v_lhs_374_);
    v___x_377_ = l_Lean_Grind_Linarith_Expr_toPolyN(v_rhs_375_);
    v___x_378_ = l_Lean_Grind_Linarith_instBEqPoly_beq(v___x_376_, v___x_377_);
    lean_dec(v___x_377_);
    lean_dec(v___x_376_);
    return v___x_378_;
}
pub unsafe fn l_Lean_Grind_Linarith_eq__normN__cert___boxed(
    mut v_lhs_379_: *mut LeanObject,
    mut v_rhs_380_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_381_: u8 = 0;
    let mut v_r_382_: *mut LeanObject = core::ptr::null_mut();
    v_res_381_ = l_Lean_Grind_Linarith_eq__normN__cert(v_lhs_379_, v_rhs_380_);
    v_r_382_ = lean_box((v_res_381_) as usize);
    return v_r_382_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Init_Grind_Module_NatModuleNorm(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Init_Grind_Ordered_Linarith(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_AC(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Int_DivMod_Lemmas(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Int_LemmasAux(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Omega(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Init_Grind_Module_NatModuleNorm(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_meta_initialized = true;
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Init_Grind_Module_NatModuleNorm(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Init_Grind_Ordered_Linarith(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Data_AC(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Data_Int_DivMod_Lemmas(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Data_Int_LemmasAux(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Omega(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Grind_Module_NatModuleNorm(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Init_Grind_Module_NatModuleNorm(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Init_Grind_Module_NatModuleNorm(builtin);
}
