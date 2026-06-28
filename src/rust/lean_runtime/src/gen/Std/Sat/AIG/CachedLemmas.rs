// Lean compiler output
// Module: Std.Sat.AIG.CachedLemmas
// Imports: Std.Sat.AIG.Cached Init.Data.Nat.Order Init.Data.Order.Lemmas
use crate::r#gen::Init::Data::Nat::Order::{
    initialize_Init_Data_Nat_Order, runtime_initialize_Init_Data_Nat_Order,
};
use crate::r#gen::Init::Data::Order::Lemmas::{
    initialize_Init_Data_Order_Lemmas, runtime_initialize_Init_Data_Order_Lemmas,
};
use crate::r#gen::Std::Sat::AIG::Cached::{
    initialize_Std_Sat_AIG_Cached, runtime_initialize_Std_Sat_AIG_Cached,
};
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_apply_1, lean_apply_2, lean_apply_3, lean_apply_5,
    lean_apply_6, lean_box, lean_ctor_get, lean_dec, lean_dec_ref, lean_dec_ref_known, lean_inc,
    lean_inc_ref, lean_io_result_is_error, lean_io_result_mk_ok, lean_obj_tag, lean_unbox,
};
pub unsafe fn l___private_Std_Sat_AIG_CachedLemmas_0__Std_Sat_AIG_toGraphviz_go_match__1_splitter___redArg(
    mut v_x_135_: *mut LeanObject,
    mut v_h__1_136_: *mut LeanObject,
    mut v_h__2_137_: *mut LeanObject,
    mut v_h__3_138_: *mut LeanObject,
) -> *mut LeanObject {
    match lean_obj_tag(v_x_135_) {
        0 => {
            let mut v___x_139_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__3_138_);
            lean_dec(v_h__2_137_);
            v___x_139_ = lean_apply_1(v_h__1_136_, lean_box(0));
            return v___x_139_;
        }
        1 => {
            let mut v_idx_140_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_141_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__3_138_);
            lean_dec(v_h__1_136_);
            v_idx_140_ = lean_ctor_get(v_x_135_, 0);
            lean_inc(v_idx_140_);
            lean_dec_ref_known(v_x_135_, 1);
            v___x_141_ = lean_apply_2(v_h__2_137_, v_idx_140_, lean_box(0));
            return v___x_141_;
        }
        _ => {
            let mut v_l_142_: *mut LeanObject = core::ptr::null_mut();
            let mut v_r_143_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_144_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__2_137_);
            lean_dec(v_h__1_136_);
            v_l_142_ = lean_ctor_get(v_x_135_, 0);
            lean_inc(v_l_142_);
            v_r_143_ = lean_ctor_get(v_x_135_, 1);
            lean_inc(v_r_143_);
            lean_dec_ref_known(v_x_135_, 2);
            v___x_144_ = lean_apply_3(v_h__3_138_, v_l_142_, v_r_143_, lean_box(0));
            return v___x_144_;
        }
    }
}
pub unsafe fn l___private_Std_Sat_AIG_CachedLemmas_0__Std_Sat_AIG_toGraphviz_go_match__1_splitter(
    mut v_00_u03b1_145_: *mut LeanObject,
    mut v_motive_146_: *mut LeanObject,
    mut v_x_147_: *mut LeanObject,
    mut v_h__1_148_: *mut LeanObject,
    mut v_h__2_149_: *mut LeanObject,
    mut v_h__3_150_: *mut LeanObject,
) -> *mut LeanObject {
    match lean_obj_tag(v_x_147_) {
        0 => {
            let mut v___x_151_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__3_150_);
            lean_dec(v_h__2_149_);
            v___x_151_ = lean_apply_1(v_h__1_148_, lean_box(0));
            return v___x_151_;
        }
        1 => {
            let mut v_idx_152_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_153_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__3_150_);
            lean_dec(v_h__1_148_);
            v_idx_152_ = lean_ctor_get(v_x_147_, 0);
            lean_inc(v_idx_152_);
            lean_dec_ref_known(v_x_147_, 1);
            v___x_153_ = lean_apply_2(v_h__2_149_, v_idx_152_, lean_box(0));
            return v___x_153_;
        }
        _ => {
            let mut v_l_154_: *mut LeanObject = core::ptr::null_mut();
            let mut v_r_155_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_156_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__2_149_);
            lean_dec(v_h__1_148_);
            v_l_154_ = lean_ctor_get(v_x_147_, 0);
            lean_inc(v_l_154_);
            v_r_155_ = lean_ctor_get(v_x_147_, 1);
            lean_inc(v_r_155_);
            lean_dec_ref_known(v_x_147_, 2);
            v___x_156_ = lean_apply_3(v_h__3_150_, v_l_154_, v_r_155_, lean_box(0));
            return v___x_156_;
        }
    }
}
pub unsafe fn l___private_Std_Sat_AIG_CachedLemmas_0__Std_Sat_AIG_mkAtomCached_match__3_splitter___redArg(
    mut v_aig_157_: *mut LeanObject,
    mut v_h__1_158_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_decls_159_: *mut LeanObject = core::ptr::null_mut();
    let mut v_cache_160_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_161_: *mut LeanObject = core::ptr::null_mut();
    v_decls_159_ = lean_ctor_get(v_aig_157_, 0);
    lean_inc_ref(v_decls_159_);
    v_cache_160_ = lean_ctor_get(v_aig_157_, 1);
    lean_inc_ref(v_cache_160_);
    lean_dec_ref(v_aig_157_);
    v___x_161_ = lean_apply_5(
        v_h__1_158_,
        v_decls_159_,
        v_cache_160_,
        lean_box(0),
        lean_box(0),
        lean_box(0),
    );
    return v___x_161_;
}
pub unsafe fn l___private_Std_Sat_AIG_CachedLemmas_0__Std_Sat_AIG_mkAtomCached_match__3_splitter(
    mut v_00_u03b1_162_: *mut LeanObject,
    mut v_inst_163_: *mut LeanObject,
    mut v_inst_164_: *mut LeanObject,
    mut v_motive_165_: *mut LeanObject,
    mut v_aig_166_: *mut LeanObject,
    mut v_h__1_167_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_decls_168_: *mut LeanObject = core::ptr::null_mut();
    let mut v_cache_169_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_170_: *mut LeanObject = core::ptr::null_mut();
    v_decls_168_ = lean_ctor_get(v_aig_166_, 0);
    lean_inc_ref(v_decls_168_);
    v_cache_169_ = lean_ctor_get(v_aig_166_, 1);
    lean_inc_ref(v_cache_169_);
    lean_dec_ref(v_aig_166_);
    v___x_170_ = lean_apply_5(
        v_h__1_167_,
        v_decls_168_,
        v_cache_169_,
        lean_box(0),
        lean_box(0),
        lean_box(0),
    );
    return v___x_170_;
}
pub unsafe fn l___private_Std_Sat_AIG_CachedLemmas_0__Std_Sat_AIG_mkAtomCached_match__3_splitter___boxed(
    mut v_00_u03b1_171_: *mut LeanObject,
    mut v_inst_172_: *mut LeanObject,
    mut v_inst_173_: *mut LeanObject,
    mut v_motive_174_: *mut LeanObject,
    mut v_aig_175_: *mut LeanObject,
    mut v_h__1_176_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_177_: *mut LeanObject = core::ptr::null_mut();
    v_res_177_ = l___private_Std_Sat_AIG_CachedLemmas_0__Std_Sat_AIG_mkAtomCached_match__3_splitter(
        v_00_u03b1_171_,
        v_inst_172_,
        v_inst_173_,
        v_motive_174_,
        v_aig_175_,
        v_h__1_176_,
    );
    lean_dec_ref(v_inst_173_);
    lean_dec_ref(v_inst_172_);
    return v_res_177_;
}
pub unsafe fn l___private_Std_Sat_AIG_CachedLemmas_0__Std_Sat_AIG_mkAtomCached_match__1_splitter___redArg(
    mut v_x_178_: *mut LeanObject,
    mut v_h__1_179_: *mut LeanObject,
    mut v_h__2_180_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_178_) == 0 {
        let mut v___x_181_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_182_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_179_);
        v___x_181_ = lean_box(0);
        v___x_182_ = lean_apply_1(v_h__2_180_, v___x_181_);
        return v___x_182_;
    } else {
        let mut v_val_183_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_184_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_180_);
        v_val_183_ = lean_ctor_get(v_x_178_, 0);
        lean_inc(v_val_183_);
        lean_dec_ref_known(v_x_178_, 1);
        v___x_184_ = lean_apply_1(v_h__1_179_, v_val_183_);
        return v___x_184_;
    }
}
pub unsafe fn l___private_Std_Sat_AIG_CachedLemmas_0__Std_Sat_AIG_mkAtomCached_match__1_splitter(
    mut v_00_u03b1_185_: *mut LeanObject,
    mut v_decls_186_: *mut LeanObject,
    mut v_decl_187_: *mut LeanObject,
    mut v_motive_188_: *mut LeanObject,
    mut v_x_189_: *mut LeanObject,
    mut v_h__1_190_: *mut LeanObject,
    mut v_h__2_191_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_189_) == 0 {
        let mut v___x_192_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_193_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_190_);
        v___x_192_ = lean_box(0);
        v___x_193_ = lean_apply_1(v_h__2_191_, v___x_192_);
        return v___x_193_;
    } else {
        let mut v_val_194_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_195_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_191_);
        v_val_194_ = lean_ctor_get(v_x_189_, 0);
        lean_inc(v_val_194_);
        lean_dec_ref_known(v_x_189_, 1);
        v___x_195_ = lean_apply_1(v_h__1_190_, v_val_194_);
        return v___x_195_;
    }
}
pub unsafe fn l___private_Std_Sat_AIG_CachedLemmas_0__Std_Sat_AIG_mkAtomCached_match__1_splitter___boxed(
    mut v_00_u03b1_196_: *mut LeanObject,
    mut v_decls_197_: *mut LeanObject,
    mut v_decl_198_: *mut LeanObject,
    mut v_motive_199_: *mut LeanObject,
    mut v_x_200_: *mut LeanObject,
    mut v_h__1_201_: *mut LeanObject,
    mut v_h__2_202_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_203_: *mut LeanObject = core::ptr::null_mut();
    v_res_203_ = l___private_Std_Sat_AIG_CachedLemmas_0__Std_Sat_AIG_mkAtomCached_match__1_splitter(
        v_00_u03b1_196_,
        v_decls_197_,
        v_decl_198_,
        v_motive_199_,
        v_x_200_,
        v_h__1_201_,
        v_h__2_202_,
    );
    lean_dec(v_decl_198_);
    lean_dec_ref(v_decls_197_);
    return v_res_203_;
}
pub unsafe fn l___private_Std_Sat_AIG_CachedLemmas_0__Std_Sat_AIG_mkGateCached_go_match__1_splitter___redArg(
    mut v_lhsVal_204_: *mut LeanObject,
    mut v_rhsVal_205_: *mut LeanObject,
    mut v_h__1_206_: *mut LeanObject,
    mut v_h__2_207_: *mut LeanObject,
    mut v_h__3_208_: *mut LeanObject,
    mut v_h__4_209_: *mut LeanObject,
    mut v_h__5_210_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_lhsVal_204_) == 1 {
        let mut v_val_211_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_212_: u8 = 0;
        lean_dec(v_h__5_210_);
        lean_dec(v_h__4_209_);
        v_val_211_ = lean_ctor_get(v_lhsVal_204_, 0);
        v___x_212_ = (lean_unbox(v_val_211_) as u8);
        if v___x_212_ == 0 {
            let mut v___x_213_: *mut LeanObject = core::ptr::null_mut();
            lean_dec_ref_known(v_lhsVal_204_, 1);
            lean_dec(v_h__3_208_);
            lean_dec(v_h__2_207_);
            v___x_213_ = lean_apply_1(v_h__1_206_, v_rhsVal_205_);
            return v___x_213_;
        } else {
            lean_dec(v_h__1_206_);
            if lean_obj_tag(v_rhsVal_205_) == 1 {
                let mut v_val_214_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_215_: u8 = 0;
                v_val_214_ = lean_ctor_get(v_rhsVal_205_, 0);
                v___x_215_ = (lean_unbox(v_val_214_) as u8);
                if v___x_215_ == 0 {
                    let mut v___x_216_: *mut LeanObject = core::ptr::null_mut();
                    lean_dec_ref_known(v_rhsVal_205_, 1);
                    lean_dec(v_h__3_208_);
                    v___x_216_ = lean_apply_2(v_h__2_207_, v_lhsVal_204_, lean_box(0));
                    return v___x_216_;
                } else {
                    let mut v___x_217_: *mut LeanObject = core::ptr::null_mut();
                    lean_dec_ref_known(v_lhsVal_204_, 1);
                    lean_dec(v_h__2_207_);
                    v___x_217_ = lean_apply_2(v_h__3_208_, v_rhsVal_205_, lean_box(0));
                    return v___x_217_;
                }
            } else {
                let mut v___x_218_: *mut LeanObject = core::ptr::null_mut();
                lean_dec_ref_known(v_lhsVal_204_, 1);
                lean_dec(v_h__2_207_);
                v___x_218_ = lean_apply_2(v_h__3_208_, v_rhsVal_205_, lean_box(0));
                return v___x_218_;
            }
        }
    } else {
        lean_dec(v_h__3_208_);
        lean_dec(v_h__1_206_);
        if lean_obj_tag(v_rhsVal_205_) == 1 {
            let mut v_val_219_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_220_: u8 = 0;
            lean_dec(v_h__5_210_);
            v_val_219_ = lean_ctor_get(v_rhsVal_205_, 0);
            lean_inc(v_val_219_);
            lean_dec_ref_known(v_rhsVal_205_, 1);
            v___x_220_ = (lean_unbox(v_val_219_) as u8);
            lean_dec(v_val_219_);
            if v___x_220_ == 0 {
                let mut v___x_221_: *mut LeanObject = core::ptr::null_mut();
                lean_dec(v_h__4_209_);
                v___x_221_ = lean_apply_2(v_h__2_207_, v_lhsVal_204_, lean_box(0));
                return v___x_221_;
            } else {
                let mut v___x_222_: *mut LeanObject = core::ptr::null_mut();
                lean_dec(v_h__2_207_);
                v___x_222_ = lean_apply_3(v_h__4_209_, v_lhsVal_204_, lean_box(0), lean_box(0));
                return v___x_222_;
            }
        } else {
            let mut v___x_223_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__4_209_);
            lean_dec(v_h__2_207_);
            v___x_223_ = lean_apply_6(
                v_h__5_210_,
                v_lhsVal_204_,
                v_rhsVal_205_,
                lean_box(0),
                lean_box(0),
                lean_box(0),
                lean_box(0),
            );
            return v___x_223_;
        }
    }
}
pub unsafe fn l___private_Std_Sat_AIG_CachedLemmas_0__Std_Sat_AIG_mkGateCached_go_match__1_splitter(
    mut v_motive_224_: *mut LeanObject,
    mut v_lhsVal_225_: *mut LeanObject,
    mut v_rhsVal_226_: *mut LeanObject,
    mut v_h__1_227_: *mut LeanObject,
    mut v_h__2_228_: *mut LeanObject,
    mut v_h__3_229_: *mut LeanObject,
    mut v_h__4_230_: *mut LeanObject,
    mut v_h__5_231_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_lhsVal_225_) == 1 {
        let mut v_val_232_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_233_: u8 = 0;
        lean_dec(v_h__5_231_);
        lean_dec(v_h__4_230_);
        v_val_232_ = lean_ctor_get(v_lhsVal_225_, 0);
        v___x_233_ = (lean_unbox(v_val_232_) as u8);
        if v___x_233_ == 0 {
            let mut v___x_234_: *mut LeanObject = core::ptr::null_mut();
            lean_dec_ref_known(v_lhsVal_225_, 1);
            lean_dec(v_h__3_229_);
            lean_dec(v_h__2_228_);
            v___x_234_ = lean_apply_1(v_h__1_227_, v_rhsVal_226_);
            return v___x_234_;
        } else {
            lean_dec(v_h__1_227_);
            if lean_obj_tag(v_rhsVal_226_) == 1 {
                let mut v_val_235_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_236_: u8 = 0;
                v_val_235_ = lean_ctor_get(v_rhsVal_226_, 0);
                v___x_236_ = (lean_unbox(v_val_235_) as u8);
                if v___x_236_ == 0 {
                    let mut v___x_237_: *mut LeanObject = core::ptr::null_mut();
                    lean_dec_ref_known(v_rhsVal_226_, 1);
                    lean_dec(v_h__3_229_);
                    v___x_237_ = lean_apply_2(v_h__2_228_, v_lhsVal_225_, lean_box(0));
                    return v___x_237_;
                } else {
                    let mut v___x_238_: *mut LeanObject = core::ptr::null_mut();
                    lean_dec_ref_known(v_lhsVal_225_, 1);
                    lean_dec(v_h__2_228_);
                    v___x_238_ = lean_apply_2(v_h__3_229_, v_rhsVal_226_, lean_box(0));
                    return v___x_238_;
                }
            } else {
                let mut v___x_239_: *mut LeanObject = core::ptr::null_mut();
                lean_dec_ref_known(v_lhsVal_225_, 1);
                lean_dec(v_h__2_228_);
                v___x_239_ = lean_apply_2(v_h__3_229_, v_rhsVal_226_, lean_box(0));
                return v___x_239_;
            }
        }
    } else {
        lean_dec(v_h__3_229_);
        lean_dec(v_h__1_227_);
        if lean_obj_tag(v_rhsVal_226_) == 1 {
            let mut v_val_240_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_241_: u8 = 0;
            lean_dec(v_h__5_231_);
            v_val_240_ = lean_ctor_get(v_rhsVal_226_, 0);
            lean_inc(v_val_240_);
            lean_dec_ref_known(v_rhsVal_226_, 1);
            v___x_241_ = (lean_unbox(v_val_240_) as u8);
            lean_dec(v_val_240_);
            if v___x_241_ == 0 {
                let mut v___x_242_: *mut LeanObject = core::ptr::null_mut();
                lean_dec(v_h__4_230_);
                v___x_242_ = lean_apply_2(v_h__2_228_, v_lhsVal_225_, lean_box(0));
                return v___x_242_;
            } else {
                let mut v___x_243_: *mut LeanObject = core::ptr::null_mut();
                lean_dec(v_h__2_228_);
                v___x_243_ = lean_apply_3(v_h__4_230_, v_lhsVal_225_, lean_box(0), lean_box(0));
                return v___x_243_;
            }
        } else {
            let mut v___x_244_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__4_230_);
            lean_dec(v_h__2_228_);
            v___x_244_ = lean_apply_6(
                v_h__5_231_,
                v_lhsVal_225_,
                v_rhsVal_226_,
                lean_box(0),
                lean_box(0),
                lean_box(0),
                lean_box(0),
            );
            return v___x_244_;
        }
    }
}
pub unsafe fn l___private_Std_Sat_AIG_CachedLemmas_0__Std_Sat_AIG_mkGateCached_go_match__4_splitter___redArg(
    mut v_aig_245_: *mut LeanObject,
    mut v_input_246_: *mut LeanObject,
    mut v_h__1_247_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_decls_248_: *mut LeanObject = core::ptr::null_mut();
    let mut v_cache_249_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_250_: *mut LeanObject = core::ptr::null_mut();
    v_decls_248_ = lean_ctor_get(v_aig_245_, 0);
    lean_inc_ref(v_decls_248_);
    v_cache_249_ = lean_ctor_get(v_aig_245_, 1);
    lean_inc_ref(v_cache_249_);
    lean_dec_ref(v_aig_245_);
    v___x_250_ = lean_apply_6(
        v_h__1_247_,
        v_decls_248_,
        v_cache_249_,
        lean_box(0),
        lean_box(0),
        lean_box(0),
        v_input_246_,
    );
    return v___x_250_;
}
pub unsafe fn l___private_Std_Sat_AIG_CachedLemmas_0__Std_Sat_AIG_mkGateCached_go_match__4_splitter(
    mut v_00_u03b1_251_: *mut LeanObject,
    mut v_inst_252_: *mut LeanObject,
    mut v_inst_253_: *mut LeanObject,
    mut v_motive_254_: *mut LeanObject,
    mut v_aig_255_: *mut LeanObject,
    mut v_input_256_: *mut LeanObject,
    mut v_h__1_257_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_decls_258_: *mut LeanObject = core::ptr::null_mut();
    let mut v_cache_259_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_260_: *mut LeanObject = core::ptr::null_mut();
    v_decls_258_ = lean_ctor_get(v_aig_255_, 0);
    lean_inc_ref(v_decls_258_);
    v_cache_259_ = lean_ctor_get(v_aig_255_, 1);
    lean_inc_ref(v_cache_259_);
    lean_dec_ref(v_aig_255_);
    v___x_260_ = lean_apply_6(
        v_h__1_257_,
        v_decls_258_,
        v_cache_259_,
        lean_box(0),
        lean_box(0),
        lean_box(0),
        v_input_256_,
    );
    return v___x_260_;
}
pub unsafe fn l___private_Std_Sat_AIG_CachedLemmas_0__Std_Sat_AIG_mkGateCached_go_match__4_splitter___boxed(
    mut v_00_u03b1_261_: *mut LeanObject,
    mut v_inst_262_: *mut LeanObject,
    mut v_inst_263_: *mut LeanObject,
    mut v_motive_264_: *mut LeanObject,
    mut v_aig_265_: *mut LeanObject,
    mut v_input_266_: *mut LeanObject,
    mut v_h__1_267_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_268_: *mut LeanObject = core::ptr::null_mut();
    v_res_268_ =
        l___private_Std_Sat_AIG_CachedLemmas_0__Std_Sat_AIG_mkGateCached_go_match__4_splitter(
            v_00_u03b1_261_,
            v_inst_262_,
            v_inst_263_,
            v_motive_264_,
            v_aig_265_,
            v_input_266_,
            v_h__1_267_,
        );
    lean_dec_ref(v_inst_263_);
    lean_dec_ref(v_inst_262_);
    return v_res_268_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Std_Sat_AIG_CachedLemmas(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Std_Sat_AIG_Cached(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Nat_Order(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Order_Lemmas(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Std_Sat_AIG_CachedLemmas(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_meta_initialized = true;
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Std_Sat_AIG_CachedLemmas(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Std_Sat_AIG_Cached(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Data_Nat_Order(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Data_Order_Lemmas(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Std_Sat_AIG_CachedLemmas(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Std_Sat_AIG_CachedLemmas(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Std_Sat_AIG_CachedLemmas(builtin);
}
