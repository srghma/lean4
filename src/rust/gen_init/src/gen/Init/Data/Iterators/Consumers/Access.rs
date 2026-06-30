// Lean compiler output
// Module: Init.Data.Iterators.Consumers.Access
// Imports: Init.Data.Iterators.Consumers.Monadic.Access Init.Data.Iterators.Consumers.Partial Init.Data.Iterators.Consumers.Total Init.Ext Init.WFExtrinsicFix
use crate::ffi::{lean_nat_dec_eq, lean_nat_sub};
use crate::r#gen::Init::Data::Iterators::Consumers::Monadic::Access::{
    initialize_Init_Data_Iterators_Consumers_Monadic_Access,
    runtime_initialize_Init_Data_Iterators_Consumers_Monadic_Access,
};
use crate::r#gen::Init::Data::Iterators::Consumers::Partial::{
    initialize_Init_Data_Iterators_Consumers_Partial,
    runtime_initialize_Init_Data_Iterators_Consumers_Partial,
};
use crate::r#gen::Init::Data::Iterators::Consumers::Total::{
    initialize_Init_Data_Iterators_Consumers_Total,
    runtime_initialize_Init_Data_Iterators_Consumers_Total,
};
use crate::r#gen::Init::Ext::{initialize_Init_Ext, runtime_initialize_Init_Ext};
use crate::r#gen::Init::WFExtrinsicFix::{
    initialize_Init_WFExtrinsicFix,
    l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___redArg,
    runtime_initialize_Init_WFExtrinsicFix,
};
pub unsafe fn l_Std_Iter_atIdxSlow_x3f___redArg___lam__0(
    mut v_inst_148_: *mut leanh::LeanObject,
    mut v_it_149_: *mut leanh::LeanObject,
    mut v_n_150_: *mut leanh::LeanObject,
    mut v_recur_151_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_152_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_152_ = leanh::lean_apply_1(v_inst_148_, v_it_149_);
    match leanh::lean_obj_tag(v___x_152_) {
        0 => {
            let mut v_it_153_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_out_154_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_zero_155_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_isZero_156_: u8 = 0;
            v_it_153_ = leanh::lean_ctor_get(v___x_152_, 0);
            leanh::lean_inc(v_it_153_);
            v_out_154_ = leanh::lean_ctor_get(v___x_152_, 1);
            leanh::lean_inc(v_out_154_);
            leanh::lean_dec_ref_known(v___x_152_, 2);
            v_zero_155_ = leanh::lean_unsigned_to_nat(0);
            v_isZero_156_ = lean_nat_dec_eq(v_n_150_, v_zero_155_);
            if v_isZero_156_ == 1 {
                let mut v___x_157_: *mut leanh::LeanObject = core::ptr::null_mut();
                leanh::lean_dec(v_it_153_);
                leanh::lean_dec_ref(v_recur_151_);
                leanh::lean_dec(v_n_150_);
                v___x_157_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_157_, 0, v_out_154_);
                return v___x_157_;
            } else {
                let mut v_one_158_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v_n_159_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_160_: *mut leanh::LeanObject = core::ptr::null_mut();
                leanh::lean_dec(v_out_154_);
                v_one_158_ = leanh::lean_unsigned_to_nat(1);
                v_n_159_ = lean_nat_sub(v_n_150_, v_one_158_);
                leanh::lean_dec(v_n_150_);
                v___x_160_ = leanh::lean_apply_3(
                    v_recur_151_,
                    v_it_153_,
                    v_n_159_,
                    leanh::lean_box(0),
                );
                return v___x_160_;
            }
        }
        1 => {
            let mut v_it_161_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_162_: *mut leanh::LeanObject = core::ptr::null_mut();
            v_it_161_ = leanh::lean_ctor_get(v___x_152_, 0);
            leanh::lean_inc(v_it_161_);
            leanh::lean_dec_ref_known(v___x_152_, 1);
            v___x_162_ = leanh::lean_apply_3(
                v_recur_151_,
                v_it_161_,
                v_n_150_,
                leanh::lean_box(0),
            );
            return v___x_162_;
        }
        _ => {
            let mut v___x_163_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec_ref(v_recur_151_);
            leanh::lean_dec(v_n_150_);
            v___x_163_ = leanh::lean_box(0);
            return v___x_163_;
        }
    }
}
pub unsafe fn l_Std_Iter_atIdxSlow_x3f___redArg(
    mut v_inst_164_: *mut leanh::LeanObject,
    mut v_n_165_: *mut leanh::LeanObject,
    mut v_it_166_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_167_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_168_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_167_ = leanh::lean_alloc_closure(
        l_Std_Iter_atIdxSlow_x3f___redArg___lam__0 as *mut core::ffi::c_void,
        4,
        1,
    );
    leanh::lean_closure_set(v___f_167_, 0, v_inst_164_);
    v___x_168_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___redArg(
        v___f_167_, v_it_166_, v_n_165_,
    );
    return v___x_168_;
}
pub unsafe fn l_Std_Iter_atIdxSlow_x3f(
    mut v_00_u03b1_169_: *mut leanh::LeanObject,
    mut v_00_u03b2_170_: *mut leanh::LeanObject,
    mut v_inst_171_: *mut leanh::LeanObject,
    mut v_n_172_: *mut leanh::LeanObject,
    mut v_it_173_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_174_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_174_ = l_Std_Iter_atIdxSlow_x3f___redArg(v_inst_171_, v_n_172_, v_it_173_);
    return v___x_174_;
}
pub unsafe fn l___private_Init_Data_Iterators_Consumers_Access_0__Std_Iter_atIdxSlow_x3f_match__3_splitter___redArg(
    mut v_x_175_: *mut leanh::LeanObject,
    mut v_h__1_176_: *mut leanh::LeanObject,
    mut v_h__2_177_: *mut leanh::LeanObject,
    mut v_h__3_178_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    match leanh::lean_obj_tag(v_x_175_) {
        0 => {
            let mut v_it_179_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_out_180_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_181_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__3_178_);
            leanh::lean_dec(v_h__2_177_);
            v_it_179_ = leanh::lean_ctor_get(v_x_175_, 0);
            leanh::lean_inc(v_it_179_);
            v_out_180_ = leanh::lean_ctor_get(v_x_175_, 1);
            leanh::lean_inc(v_out_180_);
            leanh::lean_dec_ref_known(v_x_175_, 2);
            v___x_181_ = leanh::lean_apply_3(
                v_h__1_176_,
                v_it_179_,
                v_out_180_,
                leanh::lean_box(0),
            );
            return v___x_181_;
        }
        1 => {
            let mut v_it_182_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_183_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__3_178_);
            leanh::lean_dec(v_h__1_176_);
            v_it_182_ = leanh::lean_ctor_get(v_x_175_, 0);
            leanh::lean_inc(v_it_182_);
            leanh::lean_dec_ref_known(v_x_175_, 1);
            v___x_183_ =
                leanh::lean_apply_2(v_h__2_177_, v_it_182_, leanh::lean_box(0));
            return v___x_183_;
        }
        _ => {
            let mut v___x_184_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__2_177_);
            leanh::lean_dec(v_h__1_176_);
            v___x_184_ = leanh::lean_apply_1(v_h__3_178_, leanh::lean_box(0));
            return v___x_184_;
        }
    }
}
pub unsafe fn l___private_Init_Data_Iterators_Consumers_Access_0__Std_Iter_atIdxSlow_x3f_match__3_splitter(
    mut v_00_u03b1_185_: *mut leanh::LeanObject,
    mut v_00_u03b2_186_: *mut leanh::LeanObject,
    mut v_inst_187_: *mut leanh::LeanObject,
    mut v_it_188_: *mut leanh::LeanObject,
    mut v_motive_189_: *mut leanh::LeanObject,
    mut v_x_190_: *mut leanh::LeanObject,
    mut v_h__1_191_: *mut leanh::LeanObject,
    mut v_h__2_192_: *mut leanh::LeanObject,
    mut v_h__3_193_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    match leanh::lean_obj_tag(v_x_190_) {
        0 => {
            let mut v_it_194_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_out_195_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_196_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__3_193_);
            leanh::lean_dec(v_h__2_192_);
            v_it_194_ = leanh::lean_ctor_get(v_x_190_, 0);
            leanh::lean_inc(v_it_194_);
            v_out_195_ = leanh::lean_ctor_get(v_x_190_, 1);
            leanh::lean_inc(v_out_195_);
            leanh::lean_dec_ref_known(v_x_190_, 2);
            v___x_196_ = leanh::lean_apply_3(
                v_h__1_191_,
                v_it_194_,
                v_out_195_,
                leanh::lean_box(0),
            );
            return v___x_196_;
        }
        1 => {
            let mut v_it_197_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_198_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__3_193_);
            leanh::lean_dec(v_h__1_191_);
            v_it_197_ = leanh::lean_ctor_get(v_x_190_, 0);
            leanh::lean_inc(v_it_197_);
            leanh::lean_dec_ref_known(v_x_190_, 1);
            v___x_198_ =
                leanh::lean_apply_2(v_h__2_192_, v_it_197_, leanh::lean_box(0));
            return v___x_198_;
        }
        _ => {
            let mut v___x_199_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__2_192_);
            leanh::lean_dec(v_h__1_191_);
            v___x_199_ = leanh::lean_apply_1(v_h__3_193_, leanh::lean_box(0));
            return v___x_199_;
        }
    }
}
pub unsafe fn l___private_Init_Data_Iterators_Consumers_Access_0__Std_Iter_atIdxSlow_x3f_match__3_splitter___boxed(
    mut v_00_u03b1_200_: *mut leanh::LeanObject,
    mut v_00_u03b2_201_: *mut leanh::LeanObject,
    mut v_inst_202_: *mut leanh::LeanObject,
    mut v_it_203_: *mut leanh::LeanObject,
    mut v_motive_204_: *mut leanh::LeanObject,
    mut v_x_205_: *mut leanh::LeanObject,
    mut v_h__1_206_: *mut leanh::LeanObject,
    mut v_h__2_207_: *mut leanh::LeanObject,
    mut v_h__3_208_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_209_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_209_ = l___private_Init_Data_Iterators_Consumers_Access_0__Std_Iter_atIdxSlow_x3f_match__3_splitter(v_00_u03b1_200_, v_00_u03b2_201_, v_inst_202_, v_it_203_, v_motive_204_, v_x_205_, v_h__1_206_, v_h__2_207_, v_h__3_208_);
    leanh::lean_dec(v_it_203_);
    leanh::lean_dec(v_inst_202_);
    return v_res_209_;
}
pub unsafe fn l___private_Init_Data_Iterators_Consumers_Access_0__Std_Iter_atIdxSlow_x3f_match__1_splitter___redArg(
    mut v_n_210_: *mut leanh::LeanObject,
    mut v_recur_211_: *mut leanh::LeanObject,
    mut v_h__1_212_: *mut leanh::LeanObject,
    mut v_h__2_213_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_zero_214_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isZero_215_: u8 = 0;
    v_zero_214_ = leanh::lean_unsigned_to_nat(0);
    v_isZero_215_ = lean_nat_dec_eq(v_n_210_, v_zero_214_);
    if v_isZero_215_ == 1 {
        let mut v___x_216_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__2_213_);
        v___x_216_ = leanh::lean_apply_1(v_h__1_212_, v_recur_211_);
        return v___x_216_;
    } else {
        let mut v_one_217_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_n_218_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_219_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__1_212_);
        v_one_217_ = leanh::lean_unsigned_to_nat(1);
        v_n_218_ = lean_nat_sub(v_n_210_, v_one_217_);
        v___x_219_ = leanh::lean_apply_2(v_h__2_213_, v_n_218_, v_recur_211_);
        return v___x_219_;
    }
}
pub unsafe fn l___private_Init_Data_Iterators_Consumers_Access_0__Std_Iter_atIdxSlow_x3f_match__1_splitter___redArg___boxed(
    mut v_n_220_: *mut leanh::LeanObject,
    mut v_recur_221_: *mut leanh::LeanObject,
    mut v_h__1_222_: *mut leanh::LeanObject,
    mut v_h__2_223_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_224_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_224_ = l___private_Init_Data_Iterators_Consumers_Access_0__Std_Iter_atIdxSlow_x3f_match__1_splitter___redArg(v_n_220_, v_recur_221_, v_h__1_222_, v_h__2_223_);
    leanh::lean_dec(v_n_220_);
    return v_res_224_;
}
pub unsafe fn l___private_Init_Data_Iterators_Consumers_Access_0__Std_Iter_atIdxSlow_x3f_match__1_splitter(
    mut v_00_u03b1_225_: *mut leanh::LeanObject,
    mut v_00_u03b2_226_: *mut leanh::LeanObject,
    mut v_inst_227_: *mut leanh::LeanObject,
    mut v_it_228_: *mut leanh::LeanObject,
    mut v_motive_229_: *mut leanh::LeanObject,
    mut v_n_230_: *mut leanh::LeanObject,
    mut v_recur_231_: *mut leanh::LeanObject,
    mut v_h__1_232_: *mut leanh::LeanObject,
    mut v_h__2_233_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_zero_234_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isZero_235_: u8 = 0;
    v_zero_234_ = leanh::lean_unsigned_to_nat(0);
    v_isZero_235_ = lean_nat_dec_eq(v_n_230_, v_zero_234_);
    if v_isZero_235_ == 1 {
        let mut v___x_236_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__2_233_);
        v___x_236_ = leanh::lean_apply_1(v_h__1_232_, v_recur_231_);
        return v___x_236_;
    } else {
        let mut v_one_237_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_n_238_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_239_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__1_232_);
        v_one_237_ = leanh::lean_unsigned_to_nat(1);
        v_n_238_ = lean_nat_sub(v_n_230_, v_one_237_);
        v___x_239_ = leanh::lean_apply_2(v_h__2_233_, v_n_238_, v_recur_231_);
        return v___x_239_;
    }
}
pub unsafe fn l___private_Init_Data_Iterators_Consumers_Access_0__Std_Iter_atIdxSlow_x3f_match__1_splitter___boxed(
    mut v_00_u03b1_240_: *mut leanh::LeanObject,
    mut v_00_u03b2_241_: *mut leanh::LeanObject,
    mut v_inst_242_: *mut leanh::LeanObject,
    mut v_it_243_: *mut leanh::LeanObject,
    mut v_motive_244_: *mut leanh::LeanObject,
    mut v_n_245_: *mut leanh::LeanObject,
    mut v_recur_246_: *mut leanh::LeanObject,
    mut v_h__1_247_: *mut leanh::LeanObject,
    mut v_h__2_248_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_249_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_249_ = l___private_Init_Data_Iterators_Consumers_Access_0__Std_Iter_atIdxSlow_x3f_match__1_splitter(v_00_u03b1_240_, v_00_u03b2_241_, v_inst_242_, v_it_243_, v_motive_244_, v_n_245_, v_recur_246_, v_h__1_247_, v_h__2_248_);
    leanh::lean_dec(v_n_245_);
    leanh::lean_dec(v_it_243_);
    leanh::lean_dec(v_inst_242_);
    return v_res_249_;
}
pub unsafe fn l_Std_Iter_Total_atIdxSlow_x3f___redArg(
    mut v_inst_250_: *mut leanh::LeanObject,
    mut v_n_251_: *mut leanh::LeanObject,
    mut v_it_252_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_253_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_253_ = l_Std_Iter_atIdxSlow_x3f___redArg(v_inst_250_, v_n_251_, v_it_252_);
    return v___x_253_;
}
pub unsafe fn l_Std_Iter_Total_atIdxSlow_x3f(
    mut v_00_u03b1_254_: *mut leanh::LeanObject,
    mut v_00_u03b2_255_: *mut leanh::LeanObject,
    mut v_inst_256_: *mut leanh::LeanObject,
    mut v_inst_257_: *mut leanh::LeanObject,
    mut v_n_258_: *mut leanh::LeanObject,
    mut v_it_259_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_260_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_260_ = l_Std_Iter_atIdxSlow_x3f___redArg(v_inst_256_, v_n_258_, v_it_259_);
    return v___x_260_;
}
pub unsafe fn l_Std_Iter_Partial_atIdxSlow_x3f___redArg(
    mut v_inst_261_: *mut leanh::LeanObject,
    mut v_n_262_: *mut leanh::LeanObject,
    mut v_it_263_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_264_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_264_ = l_Std_Iter_atIdxSlow_x3f___redArg(v_inst_261_, v_n_262_, v_it_263_);
    return v___x_264_;
}
pub unsafe fn l_Std_Iter_Partial_atIdxSlow_x3f(
    mut v_00_u03b1_265_: *mut leanh::LeanObject,
    mut v_00_u03b2_266_: *mut leanh::LeanObject,
    mut v_inst_267_: *mut leanh::LeanObject,
    mut v_n_268_: *mut leanh::LeanObject,
    mut v_it_269_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_270_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_270_ = l_Std_Iter_atIdxSlow_x3f___redArg(v_inst_267_, v_n_268_, v_it_269_);
    return v___x_270_;
}
pub unsafe fn l_Std_Iter_atIdx_x3f___redArg(
    mut v_inst_271_: *mut leanh::LeanObject,
    mut v_n_272_: *mut leanh::LeanObject,
    mut v_it_273_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_274_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_274_ = leanh::lean_apply_2(v_inst_271_, v_it_273_, v_n_272_);
    if leanh::lean_obj_tag(v___x_274_) == 0 {
        let mut v_out_275_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_276_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_out_275_ = leanh::lean_ctor_get(v___x_274_, 1);
        leanh::lean_inc(v_out_275_);
        leanh::lean_dec_ref_known(v___x_274_, 2);
        v___x_276_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
        leanh::lean_ctor_set(v___x_276_, 0, v_out_275_);
        return v___x_276_;
    } else {
        let mut v___x_277_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v___x_274_);
        v___x_277_ = leanh::lean_box(0);
        return v___x_277_;
    }
}
pub unsafe fn l_Std_Iter_atIdx_x3f(
    mut v_00_u03b1_278_: *mut leanh::LeanObject,
    mut v_00_u03b2_279_: *mut leanh::LeanObject,
    mut v_inst_280_: *mut leanh::LeanObject,
    mut v_inst_281_: *mut leanh::LeanObject,
    mut v_n_282_: *mut leanh::LeanObject,
    mut v_it_283_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_284_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_284_ = leanh::lean_apply_2(v_inst_281_, v_it_283_, v_n_282_);
    if leanh::lean_obj_tag(v___x_284_) == 0 {
        let mut v_out_285_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_286_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_out_285_ = leanh::lean_ctor_get(v___x_284_, 1);
        leanh::lean_inc(v_out_285_);
        leanh::lean_dec_ref_known(v___x_284_, 2);
        v___x_286_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
        leanh::lean_ctor_set(v___x_286_, 0, v_out_285_);
        return v___x_286_;
    } else {
        let mut v___x_287_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v___x_284_);
        v___x_287_ = leanh::lean_box(0);
        return v___x_287_;
    }
}
pub unsafe fn l_Std_Iter_atIdx_x3f___boxed(
    mut v_00_u03b1_288_: *mut leanh::LeanObject,
    mut v_00_u03b2_289_: *mut leanh::LeanObject,
    mut v_inst_290_: *mut leanh::LeanObject,
    mut v_inst_291_: *mut leanh::LeanObject,
    mut v_n_292_: *mut leanh::LeanObject,
    mut v_it_293_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_294_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_294_ = l_Std_Iter_atIdx_x3f(
        v_00_u03b1_288_,
        v_00_u03b2_289_,
        v_inst_290_,
        v_inst_291_,
        v_n_292_,
        v_it_293_,
    );
    leanh::lean_dec(v_inst_290_);
    return v_res_294_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Init_Data_Iterators_Consumers_Access(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Init_Data_Iterators_Consumers_Monadic_Access(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Iterators_Consumers_Partial(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Iterators_Consumers_Total(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Ext(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_WFExtrinsicFix(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Init_Data_Iterators_Consumers_Access(
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
pub unsafe fn initialize_Init_Data_Iterators_Consumers_Access(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Init_Data_Iterators_Consumers_Monadic_Access(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Iterators_Consumers_Partial(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Iterators_Consumers_Total(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_Ext(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_WFExtrinsicFix(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Iterators_Consumers_Access(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = meta_initialize_Init_Data_Iterators_Consumers_Access(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return initialize_Init_Data_Iterators_Consumers_Access(builtin);
}