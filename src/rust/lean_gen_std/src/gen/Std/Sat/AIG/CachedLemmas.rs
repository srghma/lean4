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
pub unsafe fn l___private_Std_Sat_AIG_CachedLemmas_0__Std_Sat_AIG_toGraphviz_go_match__1_splitter___redArg(
    mut v_x_135_: *mut crate::leanh::LeanObject,
    mut v_h__1_136_: *mut crate::leanh::LeanObject,
    mut v_h__2_137_: *mut crate::leanh::LeanObject,
    mut v_h__3_138_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    match crate::leanh::lean_obj_tag(v_x_135_) {
        0 => {
            let mut v___x_139_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__3_138_);
            crate::leanh::lean_dec(v_h__2_137_);
            v___x_139_ = crate::leanh::lean_apply_1(v_h__1_136_, crate::leanh::lean_box(0));
            return v___x_139_;
        }
        1 => {
            let mut v_idx_140_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_141_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__3_138_);
            crate::leanh::lean_dec(v_h__1_136_);
            v_idx_140_ = crate::leanh::lean_ctor_get(v_x_135_, 0);
            crate::leanh::lean_inc(v_idx_140_);
            crate::leanh::lean_dec_ref_known(v_x_135_, 1);
            v___x_141_ =
                crate::leanh::lean_apply_2(v_h__2_137_, v_idx_140_, crate::leanh::lean_box(0));
            return v___x_141_;
        }
        _ => {
            let mut v_l_142_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_r_143_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_144_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__2_137_);
            crate::leanh::lean_dec(v_h__1_136_);
            v_l_142_ = crate::leanh::lean_ctor_get(v_x_135_, 0);
            crate::leanh::lean_inc(v_l_142_);
            v_r_143_ = crate::leanh::lean_ctor_get(v_x_135_, 1);
            crate::leanh::lean_inc(v_r_143_);
            crate::leanh::lean_dec_ref_known(v_x_135_, 2);
            v___x_144_ = crate::leanh::lean_apply_3(
                v_h__3_138_,
                v_l_142_,
                v_r_143_,
                crate::leanh::lean_box(0),
            );
            return v___x_144_;
        }
    }
}
pub unsafe fn l___private_Std_Sat_AIG_CachedLemmas_0__Std_Sat_AIG_toGraphviz_go_match__1_splitter(
    mut v_00_u03b1_145_: *mut crate::leanh::LeanObject,
    mut v_motive_146_: *mut crate::leanh::LeanObject,
    mut v_x_147_: *mut crate::leanh::LeanObject,
    mut v_h__1_148_: *mut crate::leanh::LeanObject,
    mut v_h__2_149_: *mut crate::leanh::LeanObject,
    mut v_h__3_150_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    match crate::leanh::lean_obj_tag(v_x_147_) {
        0 => {
            let mut v___x_151_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__3_150_);
            crate::leanh::lean_dec(v_h__2_149_);
            v___x_151_ = crate::leanh::lean_apply_1(v_h__1_148_, crate::leanh::lean_box(0));
            return v___x_151_;
        }
        1 => {
            let mut v_idx_152_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_153_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__3_150_);
            crate::leanh::lean_dec(v_h__1_148_);
            v_idx_152_ = crate::leanh::lean_ctor_get(v_x_147_, 0);
            crate::leanh::lean_inc(v_idx_152_);
            crate::leanh::lean_dec_ref_known(v_x_147_, 1);
            v___x_153_ =
                crate::leanh::lean_apply_2(v_h__2_149_, v_idx_152_, crate::leanh::lean_box(0));
            return v___x_153_;
        }
        _ => {
            let mut v_l_154_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_r_155_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_156_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__2_149_);
            crate::leanh::lean_dec(v_h__1_148_);
            v_l_154_ = crate::leanh::lean_ctor_get(v_x_147_, 0);
            crate::leanh::lean_inc(v_l_154_);
            v_r_155_ = crate::leanh::lean_ctor_get(v_x_147_, 1);
            crate::leanh::lean_inc(v_r_155_);
            crate::leanh::lean_dec_ref_known(v_x_147_, 2);
            v___x_156_ = crate::leanh::lean_apply_3(
                v_h__3_150_,
                v_l_154_,
                v_r_155_,
                crate::leanh::lean_box(0),
            );
            return v___x_156_;
        }
    }
}
pub unsafe fn l___private_Std_Sat_AIG_CachedLemmas_0__Std_Sat_AIG_mkAtomCached_match__3_splitter___redArg(
    mut v_aig_157_: *mut crate::leanh::LeanObject,
    mut v_h__1_158_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_decls_159_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_cache_160_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_161_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_decls_159_ = crate::leanh::lean_ctor_get(v_aig_157_, 0);
    crate::leanh::lean_inc_ref(v_decls_159_);
    v_cache_160_ = crate::leanh::lean_ctor_get(v_aig_157_, 1);
    crate::leanh::lean_inc_ref(v_cache_160_);
    crate::leanh::lean_dec_ref(v_aig_157_);
    v___x_161_ = crate::leanh::lean_apply_5(
        v_h__1_158_,
        v_decls_159_,
        v_cache_160_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
    );
    return v___x_161_;
}
pub unsafe fn l___private_Std_Sat_AIG_CachedLemmas_0__Std_Sat_AIG_mkAtomCached_match__3_splitter(
    mut v_00_u03b1_162_: *mut crate::leanh::LeanObject,
    mut v_inst_163_: *mut crate::leanh::LeanObject,
    mut v_inst_164_: *mut crate::leanh::LeanObject,
    mut v_motive_165_: *mut crate::leanh::LeanObject,
    mut v_aig_166_: *mut crate::leanh::LeanObject,
    mut v_h__1_167_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_decls_168_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_cache_169_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_170_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_decls_168_ = crate::leanh::lean_ctor_get(v_aig_166_, 0);
    crate::leanh::lean_inc_ref(v_decls_168_);
    v_cache_169_ = crate::leanh::lean_ctor_get(v_aig_166_, 1);
    crate::leanh::lean_inc_ref(v_cache_169_);
    crate::leanh::lean_dec_ref(v_aig_166_);
    v___x_170_ = crate::leanh::lean_apply_5(
        v_h__1_167_,
        v_decls_168_,
        v_cache_169_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
    );
    return v___x_170_;
}
pub unsafe fn l___private_Std_Sat_AIG_CachedLemmas_0__Std_Sat_AIG_mkAtomCached_match__3_splitter___boxed(
    mut v_00_u03b1_171_: *mut crate::leanh::LeanObject,
    mut v_inst_172_: *mut crate::leanh::LeanObject,
    mut v_inst_173_: *mut crate::leanh::LeanObject,
    mut v_motive_174_: *mut crate::leanh::LeanObject,
    mut v_aig_175_: *mut crate::leanh::LeanObject,
    mut v_h__1_176_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_177_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_177_ = l___private_Std_Sat_AIG_CachedLemmas_0__Std_Sat_AIG_mkAtomCached_match__3_splitter(
        v_00_u03b1_171_,
        v_inst_172_,
        v_inst_173_,
        v_motive_174_,
        v_aig_175_,
        v_h__1_176_,
    );
    crate::leanh::lean_dec_ref(v_inst_173_);
    crate::leanh::lean_dec_ref(v_inst_172_);
    return v_res_177_;
}
pub unsafe fn l___private_Std_Sat_AIG_CachedLemmas_0__Std_Sat_AIG_mkAtomCached_match__1_splitter___redArg(
    mut v_x_178_: *mut crate::leanh::LeanObject,
    mut v_h__1_179_: *mut crate::leanh::LeanObject,
    mut v_h__2_180_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_178_) == 0 {
        let mut v___x_181_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_182_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_179_);
        v___x_181_ = crate::leanh::lean_box(0);
        v___x_182_ = crate::leanh::lean_apply_1(v_h__2_180_, v___x_181_);
        return v___x_182_;
    } else {
        let mut v_val_183_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_184_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_180_);
        v_val_183_ = crate::leanh::lean_ctor_get(v_x_178_, 0);
        crate::leanh::lean_inc(v_val_183_);
        crate::leanh::lean_dec_ref_known(v_x_178_, 1);
        v___x_184_ = crate::leanh::lean_apply_1(v_h__1_179_, v_val_183_);
        return v___x_184_;
    }
}
pub unsafe fn l___private_Std_Sat_AIG_CachedLemmas_0__Std_Sat_AIG_mkAtomCached_match__1_splitter(
    mut v_00_u03b1_185_: *mut crate::leanh::LeanObject,
    mut v_decls_186_: *mut crate::leanh::LeanObject,
    mut v_decl_187_: *mut crate::leanh::LeanObject,
    mut v_motive_188_: *mut crate::leanh::LeanObject,
    mut v_x_189_: *mut crate::leanh::LeanObject,
    mut v_h__1_190_: *mut crate::leanh::LeanObject,
    mut v_h__2_191_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_189_) == 0 {
        let mut v___x_192_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_193_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_190_);
        v___x_192_ = crate::leanh::lean_box(0);
        v___x_193_ = crate::leanh::lean_apply_1(v_h__2_191_, v___x_192_);
        return v___x_193_;
    } else {
        let mut v_val_194_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_195_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_191_);
        v_val_194_ = crate::leanh::lean_ctor_get(v_x_189_, 0);
        crate::leanh::lean_inc(v_val_194_);
        crate::leanh::lean_dec_ref_known(v_x_189_, 1);
        v___x_195_ = crate::leanh::lean_apply_1(v_h__1_190_, v_val_194_);
        return v___x_195_;
    }
}
pub unsafe fn l___private_Std_Sat_AIG_CachedLemmas_0__Std_Sat_AIG_mkAtomCached_match__1_splitter___boxed(
    mut v_00_u03b1_196_: *mut crate::leanh::LeanObject,
    mut v_decls_197_: *mut crate::leanh::LeanObject,
    mut v_decl_198_: *mut crate::leanh::LeanObject,
    mut v_motive_199_: *mut crate::leanh::LeanObject,
    mut v_x_200_: *mut crate::leanh::LeanObject,
    mut v_h__1_201_: *mut crate::leanh::LeanObject,
    mut v_h__2_202_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_203_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_203_ = l___private_Std_Sat_AIG_CachedLemmas_0__Std_Sat_AIG_mkAtomCached_match__1_splitter(
        v_00_u03b1_196_,
        v_decls_197_,
        v_decl_198_,
        v_motive_199_,
        v_x_200_,
        v_h__1_201_,
        v_h__2_202_,
    );
    crate::leanh::lean_dec(v_decl_198_);
    crate::leanh::lean_dec_ref(v_decls_197_);
    return v_res_203_;
}
pub unsafe fn l___private_Std_Sat_AIG_CachedLemmas_0__Std_Sat_AIG_mkGateCached_go_match__1_splitter___redArg(
    mut v_lhsVal_204_: *mut crate::leanh::LeanObject,
    mut v_rhsVal_205_: *mut crate::leanh::LeanObject,
    mut v_h__1_206_: *mut crate::leanh::LeanObject,
    mut v_h__2_207_: *mut crate::leanh::LeanObject,
    mut v_h__3_208_: *mut crate::leanh::LeanObject,
    mut v_h__4_209_: *mut crate::leanh::LeanObject,
    mut v_h__5_210_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_lhsVal_204_) == 1 {
        let mut v_val_211_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_212_: u8 = 0;
        crate::leanh::lean_dec(v_h__5_210_);
        crate::leanh::lean_dec(v_h__4_209_);
        v_val_211_ = crate::leanh::lean_ctor_get(v_lhsVal_204_, 0);
        v___x_212_ = (crate::leanh::lean_unbox(v_val_211_) as u8);
        if v___x_212_ == 0 {
            let mut v___x_213_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec_ref_known(v_lhsVal_204_, 1);
            crate::leanh::lean_dec(v_h__3_208_);
            crate::leanh::lean_dec(v_h__2_207_);
            v___x_213_ = crate::leanh::lean_apply_1(v_h__1_206_, v_rhsVal_205_);
            return v___x_213_;
        } else {
            crate::leanh::lean_dec(v_h__1_206_);
            if crate::leanh::lean_obj_tag(v_rhsVal_205_) == 1 {
                let mut v_val_214_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_215_: u8 = 0;
                v_val_214_ = crate::leanh::lean_ctor_get(v_rhsVal_205_, 0);
                v___x_215_ = (crate::leanh::lean_unbox(v_val_214_) as u8);
                if v___x_215_ == 0 {
                    let mut v___x_216_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    crate::leanh::lean_dec_ref_known(v_rhsVal_205_, 1);
                    crate::leanh::lean_dec(v_h__3_208_);
                    v___x_216_ = crate::leanh::lean_apply_2(
                        v_h__2_207_,
                        v_lhsVal_204_,
                        crate::leanh::lean_box(0),
                    );
                    return v___x_216_;
                } else {
                    let mut v___x_217_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    crate::leanh::lean_dec_ref_known(v_lhsVal_204_, 1);
                    crate::leanh::lean_dec(v_h__2_207_);
                    v___x_217_ = crate::leanh::lean_apply_2(
                        v_h__3_208_,
                        v_rhsVal_205_,
                        crate::leanh::lean_box(0),
                    );
                    return v___x_217_;
                }
            } else {
                let mut v___x_218_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                crate::leanh::lean_dec_ref_known(v_lhsVal_204_, 1);
                crate::leanh::lean_dec(v_h__2_207_);
                v___x_218_ = crate::leanh::lean_apply_2(
                    v_h__3_208_,
                    v_rhsVal_205_,
                    crate::leanh::lean_box(0),
                );
                return v___x_218_;
            }
        }
    } else {
        crate::leanh::lean_dec(v_h__3_208_);
        crate::leanh::lean_dec(v_h__1_206_);
        if crate::leanh::lean_obj_tag(v_rhsVal_205_) == 1 {
            let mut v_val_219_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_220_: u8 = 0;
            crate::leanh::lean_dec(v_h__5_210_);
            v_val_219_ = crate::leanh::lean_ctor_get(v_rhsVal_205_, 0);
            crate::leanh::lean_inc(v_val_219_);
            crate::leanh::lean_dec_ref_known(v_rhsVal_205_, 1);
            v___x_220_ = (crate::leanh::lean_unbox(v_val_219_) as u8);
            crate::leanh::lean_dec(v_val_219_);
            if v___x_220_ == 0 {
                let mut v___x_221_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                crate::leanh::lean_dec(v_h__4_209_);
                v___x_221_ = crate::leanh::lean_apply_2(
                    v_h__2_207_,
                    v_lhsVal_204_,
                    crate::leanh::lean_box(0),
                );
                return v___x_221_;
            } else {
                let mut v___x_222_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                crate::leanh::lean_dec(v_h__2_207_);
                v___x_222_ = crate::leanh::lean_apply_3(
                    v_h__4_209_,
                    v_lhsVal_204_,
                    crate::leanh::lean_box(0),
                    crate::leanh::lean_box(0),
                );
                return v___x_222_;
            }
        } else {
            let mut v___x_223_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__4_209_);
            crate::leanh::lean_dec(v_h__2_207_);
            v___x_223_ = crate::leanh::lean_apply_6(
                v_h__5_210_,
                v_lhsVal_204_,
                v_rhsVal_205_,
                crate::leanh::lean_box(0),
                crate::leanh::lean_box(0),
                crate::leanh::lean_box(0),
                crate::leanh::lean_box(0),
            );
            return v___x_223_;
        }
    }
}
pub unsafe fn l___private_Std_Sat_AIG_CachedLemmas_0__Std_Sat_AIG_mkGateCached_go_match__1_splitter(
    mut v_motive_224_: *mut crate::leanh::LeanObject,
    mut v_lhsVal_225_: *mut crate::leanh::LeanObject,
    mut v_rhsVal_226_: *mut crate::leanh::LeanObject,
    mut v_h__1_227_: *mut crate::leanh::LeanObject,
    mut v_h__2_228_: *mut crate::leanh::LeanObject,
    mut v_h__3_229_: *mut crate::leanh::LeanObject,
    mut v_h__4_230_: *mut crate::leanh::LeanObject,
    mut v_h__5_231_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_lhsVal_225_) == 1 {
        let mut v_val_232_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_233_: u8 = 0;
        crate::leanh::lean_dec(v_h__5_231_);
        crate::leanh::lean_dec(v_h__4_230_);
        v_val_232_ = crate::leanh::lean_ctor_get(v_lhsVal_225_, 0);
        v___x_233_ = (crate::leanh::lean_unbox(v_val_232_) as u8);
        if v___x_233_ == 0 {
            let mut v___x_234_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec_ref_known(v_lhsVal_225_, 1);
            crate::leanh::lean_dec(v_h__3_229_);
            crate::leanh::lean_dec(v_h__2_228_);
            v___x_234_ = crate::leanh::lean_apply_1(v_h__1_227_, v_rhsVal_226_);
            return v___x_234_;
        } else {
            crate::leanh::lean_dec(v_h__1_227_);
            if crate::leanh::lean_obj_tag(v_rhsVal_226_) == 1 {
                let mut v_val_235_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_236_: u8 = 0;
                v_val_235_ = crate::leanh::lean_ctor_get(v_rhsVal_226_, 0);
                v___x_236_ = (crate::leanh::lean_unbox(v_val_235_) as u8);
                if v___x_236_ == 0 {
                    let mut v___x_237_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    crate::leanh::lean_dec_ref_known(v_rhsVal_226_, 1);
                    crate::leanh::lean_dec(v_h__3_229_);
                    v___x_237_ = crate::leanh::lean_apply_2(
                        v_h__2_228_,
                        v_lhsVal_225_,
                        crate::leanh::lean_box(0),
                    );
                    return v___x_237_;
                } else {
                    let mut v___x_238_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    crate::leanh::lean_dec_ref_known(v_lhsVal_225_, 1);
                    crate::leanh::lean_dec(v_h__2_228_);
                    v___x_238_ = crate::leanh::lean_apply_2(
                        v_h__3_229_,
                        v_rhsVal_226_,
                        crate::leanh::lean_box(0),
                    );
                    return v___x_238_;
                }
            } else {
                let mut v___x_239_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                crate::leanh::lean_dec_ref_known(v_lhsVal_225_, 1);
                crate::leanh::lean_dec(v_h__2_228_);
                v___x_239_ = crate::leanh::lean_apply_2(
                    v_h__3_229_,
                    v_rhsVal_226_,
                    crate::leanh::lean_box(0),
                );
                return v___x_239_;
            }
        }
    } else {
        crate::leanh::lean_dec(v_h__3_229_);
        crate::leanh::lean_dec(v_h__1_227_);
        if crate::leanh::lean_obj_tag(v_rhsVal_226_) == 1 {
            let mut v_val_240_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_241_: u8 = 0;
            crate::leanh::lean_dec(v_h__5_231_);
            v_val_240_ = crate::leanh::lean_ctor_get(v_rhsVal_226_, 0);
            crate::leanh::lean_inc(v_val_240_);
            crate::leanh::lean_dec_ref_known(v_rhsVal_226_, 1);
            v___x_241_ = (crate::leanh::lean_unbox(v_val_240_) as u8);
            crate::leanh::lean_dec(v_val_240_);
            if v___x_241_ == 0 {
                let mut v___x_242_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                crate::leanh::lean_dec(v_h__4_230_);
                v___x_242_ = crate::leanh::lean_apply_2(
                    v_h__2_228_,
                    v_lhsVal_225_,
                    crate::leanh::lean_box(0),
                );
                return v___x_242_;
            } else {
                let mut v___x_243_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                crate::leanh::lean_dec(v_h__2_228_);
                v___x_243_ = crate::leanh::lean_apply_3(
                    v_h__4_230_,
                    v_lhsVal_225_,
                    crate::leanh::lean_box(0),
                    crate::leanh::lean_box(0),
                );
                return v___x_243_;
            }
        } else {
            let mut v___x_244_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__4_230_);
            crate::leanh::lean_dec(v_h__2_228_);
            v___x_244_ = crate::leanh::lean_apply_6(
                v_h__5_231_,
                v_lhsVal_225_,
                v_rhsVal_226_,
                crate::leanh::lean_box(0),
                crate::leanh::lean_box(0),
                crate::leanh::lean_box(0),
                crate::leanh::lean_box(0),
            );
            return v___x_244_;
        }
    }
}
pub unsafe fn l___private_Std_Sat_AIG_CachedLemmas_0__Std_Sat_AIG_mkGateCached_go_match__4_splitter___redArg(
    mut v_aig_245_: *mut crate::leanh::LeanObject,
    mut v_input_246_: *mut crate::leanh::LeanObject,
    mut v_h__1_247_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_decls_248_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_cache_249_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_250_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_decls_248_ = crate::leanh::lean_ctor_get(v_aig_245_, 0);
    crate::leanh::lean_inc_ref(v_decls_248_);
    v_cache_249_ = crate::leanh::lean_ctor_get(v_aig_245_, 1);
    crate::leanh::lean_inc_ref(v_cache_249_);
    crate::leanh::lean_dec_ref(v_aig_245_);
    v___x_250_ = crate::leanh::lean_apply_6(
        v_h__1_247_,
        v_decls_248_,
        v_cache_249_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v_input_246_,
    );
    return v___x_250_;
}
pub unsafe fn l___private_Std_Sat_AIG_CachedLemmas_0__Std_Sat_AIG_mkGateCached_go_match__4_splitter(
    mut v_00_u03b1_251_: *mut crate::leanh::LeanObject,
    mut v_inst_252_: *mut crate::leanh::LeanObject,
    mut v_inst_253_: *mut crate::leanh::LeanObject,
    mut v_motive_254_: *mut crate::leanh::LeanObject,
    mut v_aig_255_: *mut crate::leanh::LeanObject,
    mut v_input_256_: *mut crate::leanh::LeanObject,
    mut v_h__1_257_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_decls_258_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_cache_259_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_260_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_decls_258_ = crate::leanh::lean_ctor_get(v_aig_255_, 0);
    crate::leanh::lean_inc_ref(v_decls_258_);
    v_cache_259_ = crate::leanh::lean_ctor_get(v_aig_255_, 1);
    crate::leanh::lean_inc_ref(v_cache_259_);
    crate::leanh::lean_dec_ref(v_aig_255_);
    v___x_260_ = crate::leanh::lean_apply_6(
        v_h__1_257_,
        v_decls_258_,
        v_cache_259_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v_input_256_,
    );
    return v___x_260_;
}
pub unsafe fn l___private_Std_Sat_AIG_CachedLemmas_0__Std_Sat_AIG_mkGateCached_go_match__4_splitter___boxed(
    mut v_00_u03b1_261_: *mut crate::leanh::LeanObject,
    mut v_inst_262_: *mut crate::leanh::LeanObject,
    mut v_inst_263_: *mut crate::leanh::LeanObject,
    mut v_motive_264_: *mut crate::leanh::LeanObject,
    mut v_aig_265_: *mut crate::leanh::LeanObject,
    mut v_input_266_: *mut crate::leanh::LeanObject,
    mut v_h__1_267_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_268_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
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
    crate::leanh::lean_dec_ref(v_inst_263_);
    crate::leanh::lean_dec_ref(v_inst_262_);
    return v_res_268_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Std_Sat_AIG_CachedLemmas(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Std_Sat_AIG_Cached(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Nat_Order(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Order_Lemmas(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Std_Sat_AIG_CachedLemmas(
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
pub unsafe fn initialize_Std_Sat_AIG_CachedLemmas(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Std_Sat_AIG_Cached(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Nat_Order(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Order_Lemmas(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Std_Sat_AIG_CachedLemmas(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Std_Sat_AIG_CachedLemmas(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Std_Sat_AIG_CachedLemmas(builtin);
}
