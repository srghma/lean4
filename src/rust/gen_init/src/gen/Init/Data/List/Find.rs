// Lean compiler output
// Module: Init.Data.List.Find
// Imports: Init.Data.List.Attach Init.Data.List.Attach Init.Data.Fin.Lemmas Init.Data.List.Impl Init.Data.List.Range Init.Data.List.Sublist Init.Data.List.TakeDrop Init.Data.Nat.Lemmas Init.Data.Prod Init.Omega
use crate::r#gen::Init::Data::Fin::Lemmas::{
    initialize_Init_Data_Fin_Lemmas, runtime_initialize_Init_Data_Fin_Lemmas,
};
use crate::r#gen::Init::Data::List::Attach::{
    initialize_Init_Data_List_Attach, runtime_initialize_Init_Data_List_Attach,
};
use crate::r#gen::Init::Data::List::Impl::{
    initialize_Init_Data_List_Impl, runtime_initialize_Init_Data_List_Impl,
};
use crate::r#gen::Init::Data::List::Range::{
    initialize_Init_Data_List_Range, runtime_initialize_Init_Data_List_Range,
};
use crate::r#gen::Init::Data::List::Sublist::{
    initialize_Init_Data_List_Sublist, runtime_initialize_Init_Data_List_Sublist,
};
use crate::r#gen::Init::Data::List::TakeDrop::{
    initialize_Init_Data_List_TakeDrop, runtime_initialize_Init_Data_List_TakeDrop,
};
use crate::r#gen::Init::Data::Nat::Lemmas::{
    initialize_Init_Data_Nat_Lemmas, runtime_initialize_Init_Data_Nat_Lemmas,
};
use crate::r#gen::Init::Data::Prod::{
    initialize_Init_Data_Prod, runtime_initialize_Init_Data_Prod,
};
use crate::r#gen::Init::Omega::{initialize_Init_Omega, runtime_initialize_Init_Omega};
pub unsafe fn l___private_Init_Data_List_Find_0__List_findSome_x3f_match__1_splitter___redArg(
    mut v_x_148_: *mut leanh::LeanObject,
    mut v_h__1_149_: *mut leanh::LeanObject,
    mut v_h__2_150_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_x_148_) == 0 {
        let mut v___x_151_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_152_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__1_149_);
        v___x_151_ = leanh::lean_box(0);
        v___x_152_ = leanh::lean_apply_1(v_h__2_150_, v___x_151_);
        return v___x_152_;
    } else {
        let mut v_val_153_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_154_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__2_150_);
        v_val_153_ = leanh::lean_ctor_get(v_x_148_, 0);
        leanh::lean_inc(v_val_153_);
        leanh::lean_dec_ref_known(v_x_148_, 1);
        v___x_154_ = leanh::lean_apply_1(v_h__1_149_, v_val_153_);
        return v___x_154_;
    }
}
pub unsafe fn l___private_Init_Data_List_Find_0__List_findSome_x3f_match__1_splitter(
    mut v_00_u03b2_155_: *mut leanh::LeanObject,
    mut v_motive_156_: *mut leanh::LeanObject,
    mut v_x_157_: *mut leanh::LeanObject,
    mut v_h__1_158_: *mut leanh::LeanObject,
    mut v_h__2_159_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_x_157_) == 0 {
        let mut v___x_160_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_161_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__1_158_);
        v___x_160_ = leanh::lean_box(0);
        v___x_161_ = leanh::lean_apply_1(v_h__2_159_, v___x_160_);
        return v___x_161_;
    } else {
        let mut v_val_162_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_163_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__2_159_);
        v_val_162_ = leanh::lean_ctor_get(v_x_157_, 0);
        leanh::lean_inc(v_val_162_);
        leanh::lean_dec_ref_known(v_x_157_, 1);
        v___x_163_ = leanh::lean_apply_1(v_h__1_158_, v_val_162_);
        return v___x_163_;
    }
}
pub unsafe fn l___private_Init_Data_List_Find_0__List_filter_match__1_splitter___redArg(
    mut v_x_164_: u8,
    mut v_h__1_165_: *mut leanh::LeanObject,
    mut v_h__2_166_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if v_x_164_ == 0 {
        let mut v___x_167_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_168_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__1_165_);
        v___x_167_ = leanh::lean_box(0);
        v___x_168_ = leanh::lean_apply_1(v_h__2_166_, v___x_167_);
        return v___x_168_;
    } else {
        let mut v___x_169_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_170_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__2_166_);
        v___x_169_ = leanh::lean_box(0);
        v___x_170_ = leanh::lean_apply_1(v_h__1_165_, v___x_169_);
        return v___x_170_;
    }
}
pub unsafe fn l___private_Init_Data_List_Find_0__List_filter_match__1_splitter___redArg___boxed(
    mut v_x_171_: *mut leanh::LeanObject,
    mut v_h__1_172_: *mut leanh::LeanObject,
    mut v_h__2_173_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_x_26__boxed_174_: u8 = 0;
    let mut v_res_175_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_x_26__boxed_174_ = (leanh::lean_unbox(v_x_171_) as u8);
    v_res_175_ = l___private_Init_Data_List_Find_0__List_filter_match__1_splitter___redArg(
        v_x_26__boxed_174_,
        v_h__1_172_,
        v_h__2_173_,
    );
    return v_res_175_;
}
pub unsafe fn l___private_Init_Data_List_Find_0__List_filter_match__1_splitter(
    mut v_motive_176_: *mut leanh::LeanObject,
    mut v_x_177_: u8,
    mut v_h__1_178_: *mut leanh::LeanObject,
    mut v_h__2_179_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if v_x_177_ == 0 {
        let mut v___x_180_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_181_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__1_178_);
        v___x_180_ = leanh::lean_box(0);
        v___x_181_ = leanh::lean_apply_1(v_h__2_179_, v___x_180_);
        return v___x_181_;
    } else {
        let mut v___x_182_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_183_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__2_179_);
        v___x_182_ = leanh::lean_box(0);
        v___x_183_ = leanh::lean_apply_1(v_h__1_178_, v___x_182_);
        return v___x_183_;
    }
}
pub unsafe fn l___private_Init_Data_List_Find_0__List_filter_match__1_splitter___boxed(
    mut v_motive_184_: *mut leanh::LeanObject,
    mut v_x_185_: *mut leanh::LeanObject,
    mut v_h__1_186_: *mut leanh::LeanObject,
    mut v_h__2_187_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_x_37__boxed_188_: u8 = 0;
    let mut v_res_189_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_x_37__boxed_188_ = (leanh::lean_unbox(v_x_185_) as u8);
    v_res_189_ = l___private_Init_Data_List_Find_0__List_filter_match__1_splitter(
        v_motive_184_,
        v_x_37__boxed_188_,
        v_h__1_186_,
        v_h__2_187_,
    );
    return v_res_189_;
}
pub unsafe fn l___private_Init_Data_List_Find_0__List_filterMap_match__1_splitter___redArg(
    mut v_x_190_: *mut leanh::LeanObject,
    mut v_h__1_191_: *mut leanh::LeanObject,
    mut v_h__2_192_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_x_190_) == 0 {
        let mut v___x_193_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_194_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__2_192_);
        v___x_193_ = leanh::lean_box(0);
        v___x_194_ = leanh::lean_apply_1(v_h__1_191_, v___x_193_);
        return v___x_194_;
    } else {
        let mut v_val_195_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_196_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__1_191_);
        v_val_195_ = leanh::lean_ctor_get(v_x_190_, 0);
        leanh::lean_inc(v_val_195_);
        leanh::lean_dec_ref_known(v_x_190_, 1);
        v___x_196_ = leanh::lean_apply_1(v_h__2_192_, v_val_195_);
        return v___x_196_;
    }
}
pub unsafe fn l___private_Init_Data_List_Find_0__List_filterMap_match__1_splitter(
    mut v_00_u03b2_197_: *mut leanh::LeanObject,
    mut v_motive_198_: *mut leanh::LeanObject,
    mut v_x_199_: *mut leanh::LeanObject,
    mut v_h__1_200_: *mut leanh::LeanObject,
    mut v_h__2_201_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_x_199_) == 0 {
        let mut v___x_202_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_203_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__2_201_);
        v___x_202_ = leanh::lean_box(0);
        v___x_203_ = leanh::lean_apply_1(v_h__1_200_, v___x_202_);
        return v___x_203_;
    } else {
        let mut v_val_204_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_205_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__1_200_);
        v_val_204_ = leanh::lean_ctor_get(v_x_199_, 0);
        leanh::lean_inc(v_val_204_);
        leanh::lean_dec_ref_known(v_x_199_, 1);
        v___x_205_ = leanh::lean_apply_1(v_h__2_201_, v_val_204_);
        return v___x_205_;
    }
}
pub unsafe fn l___private_Init_Data_List_Find_0__List_findIdx_go_match__1_splitter___redArg(
    mut v_x_206_: *mut leanh::LeanObject,
    mut v_x_207_: *mut leanh::LeanObject,
    mut v_h__1_208_: *mut leanh::LeanObject,
    mut v_h__2_209_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_x_206_) == 0 {
        let mut v___x_210_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__2_209_);
        v___x_210_ = leanh::lean_apply_1(v_h__1_208_, v_x_207_);
        return v___x_210_;
    } else {
        let mut v_head_211_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_tail_212_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_213_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__1_208_);
        v_head_211_ = leanh::lean_ctor_get(v_x_206_, 0);
        leanh::lean_inc(v_head_211_);
        v_tail_212_ = leanh::lean_ctor_get(v_x_206_, 1);
        leanh::lean_inc(v_tail_212_);
        leanh::lean_dec_ref_known(v_x_206_, 2);
        v___x_213_ = leanh::lean_apply_3(v_h__2_209_, v_head_211_, v_tail_212_, v_x_207_);
        return v___x_213_;
    }
}
pub unsafe fn l___private_Init_Data_List_Find_0__List_findIdx_go_match__1_splitter(
    mut v_00_u03b1_214_: *mut leanh::LeanObject,
    mut v_motive_215_: *mut leanh::LeanObject,
    mut v_x_216_: *mut leanh::LeanObject,
    mut v_x_217_: *mut leanh::LeanObject,
    mut v_h__1_218_: *mut leanh::LeanObject,
    mut v_h__2_219_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_x_216_) == 0 {
        let mut v___x_220_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__2_219_);
        v___x_220_ = leanh::lean_apply_1(v_h__1_218_, v_x_217_);
        return v___x_220_;
    } else {
        let mut v_head_221_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_tail_222_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_223_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__1_218_);
        v_head_221_ = leanh::lean_ctor_get(v_x_216_, 0);
        leanh::lean_inc(v_head_221_);
        v_tail_222_ = leanh::lean_ctor_get(v_x_216_, 1);
        leanh::lean_inc(v_tail_222_);
        leanh::lean_dec_ref_known(v_x_216_, 2);
        v___x_223_ = leanh::lean_apply_3(v_h__2_219_, v_head_221_, v_tail_222_, v_x_217_);
        return v___x_223_;
    }
}
pub unsafe fn l___private_Init_Data_List_Find_0__List_of__findIdx_x3f__eq__some_match__1_splitter___redArg(
    mut v_x_224_: *mut leanh::LeanObject,
    mut v_h__1_225_: *mut leanh::LeanObject,
    mut v_h__2_226_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_x_224_) == 0 {
        let mut v___x_227_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_228_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__1_225_);
        v___x_227_ = leanh::lean_box(0);
        v___x_228_ = leanh::lean_apply_1(v_h__2_226_, v___x_227_);
        return v___x_228_;
    } else {
        let mut v_val_229_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_230_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__2_226_);
        v_val_229_ = leanh::lean_ctor_get(v_x_224_, 0);
        leanh::lean_inc(v_val_229_);
        leanh::lean_dec_ref_known(v_x_224_, 1);
        v___x_230_ = leanh::lean_apply_1(v_h__1_225_, v_val_229_);
        return v___x_230_;
    }
}
pub unsafe fn l___private_Init_Data_List_Find_0__List_of__findIdx_x3f__eq__some_match__1_splitter(
    mut v_00_u03b1_231_: *mut leanh::LeanObject,
    mut v_motive_232_: *mut leanh::LeanObject,
    mut v_x_233_: *mut leanh::LeanObject,
    mut v_h__1_234_: *mut leanh::LeanObject,
    mut v_h__2_235_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_x_233_) == 0 {
        let mut v___x_236_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_237_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__1_234_);
        v___x_236_ = leanh::lean_box(0);
        v___x_237_ = leanh::lean_apply_1(v_h__2_235_, v___x_236_);
        return v___x_237_;
    } else {
        let mut v_val_238_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_239_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__2_235_);
        v_val_238_ = leanh::lean_ctor_get(v_x_233_, 0);
        leanh::lean_inc(v_val_238_);
        leanh::lean_dec_ref_known(v_x_233_, 1);
        v___x_239_ = leanh::lean_apply_1(v_h__1_234_, v_val_238_);
        return v___x_239_;
    }
}
pub unsafe fn l___private_Init_Data_List_Find_0__List_findFinIdx_x3f_go_match__1_splitter___redArg(
    mut v_x_240_: *mut leanh::LeanObject,
    mut v_x_241_: *mut leanh::LeanObject,
    mut v_h__1_242_: *mut leanh::LeanObject,
    mut v_h__2_243_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_x_240_) == 0 {
        let mut v___x_244_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__2_243_);
        v___x_244_ = leanh::lean_apply_2(v_h__1_242_, v_x_241_, leanh::lean_box(0));
        return v___x_244_;
    } else {
        let mut v_head_245_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_tail_246_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_247_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__1_242_);
        v_head_245_ = leanh::lean_ctor_get(v_x_240_, 0);
        leanh::lean_inc(v_head_245_);
        v_tail_246_ = leanh::lean_ctor_get(v_x_240_, 1);
        leanh::lean_inc(v_tail_246_);
        leanh::lean_dec_ref_known(v_x_240_, 2);
        v___x_247_ = leanh::lean_apply_4(
            v_h__2_243_,
            v_head_245_,
            v_tail_246_,
            v_x_241_,
            leanh::lean_box(0),
        );
        return v___x_247_;
    }
}
pub unsafe fn l___private_Init_Data_List_Find_0__List_findFinIdx_x3f_go_match__1_splitter(
    mut v_00_u03b1_248_: *mut leanh::LeanObject,
    mut v_l_249_: *mut leanh::LeanObject,
    mut v_motive_250_: *mut leanh::LeanObject,
    mut v_x_251_: *mut leanh::LeanObject,
    mut v_x_252_: *mut leanh::LeanObject,
    mut v_x_253_: *mut leanh::LeanObject,
    mut v_h__1_254_: *mut leanh::LeanObject,
    mut v_h__2_255_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_x_251_) == 0 {
        let mut v___x_256_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__2_255_);
        v___x_256_ = leanh::lean_apply_2(v_h__1_254_, v_x_252_, leanh::lean_box(0));
        return v___x_256_;
    } else {
        let mut v_head_257_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_tail_258_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_259_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__1_254_);
        v_head_257_ = leanh::lean_ctor_get(v_x_251_, 0);
        leanh::lean_inc(v_head_257_);
        v_tail_258_ = leanh::lean_ctor_get(v_x_251_, 1);
        leanh::lean_inc(v_tail_258_);
        leanh::lean_dec_ref_known(v_x_251_, 2);
        v___x_259_ = leanh::lean_apply_4(
            v_h__2_255_,
            v_head_257_,
            v_tail_258_,
            v_x_252_,
            leanh::lean_box(0),
        );
        return v___x_259_;
    }
}
pub unsafe fn l___private_Init_Data_List_Find_0__List_findFinIdx_x3f_go_match__1_splitter___boxed(
    mut v_00_u03b1_260_: *mut leanh::LeanObject,
    mut v_l_261_: *mut leanh::LeanObject,
    mut v_motive_262_: *mut leanh::LeanObject,
    mut v_x_263_: *mut leanh::LeanObject,
    mut v_x_264_: *mut leanh::LeanObject,
    mut v_x_265_: *mut leanh::LeanObject,
    mut v_h__1_266_: *mut leanh::LeanObject,
    mut v_h__2_267_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_268_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_268_ = l___private_Init_Data_List_Find_0__List_findFinIdx_x3f_go_match__1_splitter(
        v_00_u03b1_260_,
        v_l_261_,
        v_motive_262_,
        v_x_263_,
        v_x_264_,
        v_x_265_,
        v_h__1_266_,
        v_h__2_267_,
    );
    leanh::lean_dec(v_l_261_);
    return v_res_268_;
}
pub unsafe fn l___private_Init_Data_List_Find_0__Option_pmap__or_match__1_splitter___redArg(
    mut v_o_269_: *mut leanh::LeanObject,
    mut v_h__1_270_: *mut leanh::LeanObject,
    mut v_h__2_271_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_o_269_) == 0 {
        let mut v___x_272_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__2_271_);
        v___x_272_ = leanh::lean_apply_1(v_h__1_270_, leanh::lean_box(0));
        return v___x_272_;
    } else {
        let mut v_val_273_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_274_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__1_270_);
        v_val_273_ = leanh::lean_ctor_get(v_o_269_, 0);
        leanh::lean_inc(v_val_273_);
        leanh::lean_dec_ref_known(v_o_269_, 1);
        v___x_274_ = leanh::lean_apply_2(v_h__2_271_, v_val_273_, leanh::lean_box(0));
        return v___x_274_;
    }
}
pub unsafe fn l___private_Init_Data_List_Find_0__Option_pmap__or_match__1_splitter(
    mut v_00_u03b1_275_: *mut leanh::LeanObject,
    mut v_p_276_: *mut leanh::LeanObject,
    mut v_o_x27_277_: *mut leanh::LeanObject,
    mut v_motive_278_: *mut leanh::LeanObject,
    mut v_o_279_: *mut leanh::LeanObject,
    mut v_h_280_: *mut leanh::LeanObject,
    mut v_h__1_281_: *mut leanh::LeanObject,
    mut v_h__2_282_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_o_279_) == 0 {
        let mut v___x_283_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__2_282_);
        v___x_283_ = leanh::lean_apply_1(v_h__1_281_, leanh::lean_box(0));
        return v___x_283_;
    } else {
        let mut v_val_284_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_285_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__1_281_);
        v_val_284_ = leanh::lean_ctor_get(v_o_279_, 0);
        leanh::lean_inc(v_val_284_);
        leanh::lean_dec_ref_known(v_o_279_, 1);
        v___x_285_ = leanh::lean_apply_2(v_h__2_282_, v_val_284_, leanh::lean_box(0));
        return v___x_285_;
    }
}
pub unsafe fn l___private_Init_Data_List_Find_0__Option_pmap__or_match__1_splitter___boxed(
    mut v_00_u03b1_286_: *mut leanh::LeanObject,
    mut v_p_287_: *mut leanh::LeanObject,
    mut v_o_x27_288_: *mut leanh::LeanObject,
    mut v_motive_289_: *mut leanh::LeanObject,
    mut v_o_290_: *mut leanh::LeanObject,
    mut v_h_291_: *mut leanh::LeanObject,
    mut v_h__1_292_: *mut leanh::LeanObject,
    mut v_h__2_293_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_294_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_294_ = l___private_Init_Data_List_Find_0__Option_pmap__or_match__1_splitter(
        v_00_u03b1_286_,
        v_p_287_,
        v_o_x27_288_,
        v_motive_289_,
        v_o_290_,
        v_h_291_,
        v_h__1_292_,
        v_h__2_293_,
    );
    leanh::lean_dec(v_o_x27_288_);
    return v_res_294_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Init_Data_List_Find(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Init_Data_List_Attach(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_List_Attach(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Fin_Lemmas(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_List_Impl(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_List_Range(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_List_Sublist(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_List_TakeDrop(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Nat_Lemmas(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Prod(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Omega(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Init_Data_List_Find(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_meta_initialized = true;
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Init_Data_List_Find(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Init_Data_List_Attach(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_Data_List_Attach(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Fin_Lemmas(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_Data_List_Impl(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_Data_List_Range(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_Data_List_Sublist(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_Data_List_TakeDrop(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Nat_Lemmas(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Prod(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_Omega(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_List_Find(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = meta_initialize_Init_Data_List_Find(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return initialize_Init_Data_List_Find(builtin);
}