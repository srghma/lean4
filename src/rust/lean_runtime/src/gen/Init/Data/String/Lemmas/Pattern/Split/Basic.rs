// Lean compiler output
// Module: Init.Data.String.Lemmas.Pattern.Split.Basic
// Imports: Init.Data.String.Lemmas.Pattern.Basic Init.Data.String.Slice Init.Data.String.Search Init.Data.String.Slice Init.Data.String.Search Init.Data.Option.Lemmas Init.Data.String.Termination Init.Data.String.Lemmas.Order Init.ByCases Init.Data.Order.Lemmas Init.Data.String.OrderInstances Init.Data.Iterators.Lemmas.Basic Init.Data.Iterators.Lemmas.Consumers.Collect Init.Data.Iterators.Lemmas.Combinators.FilterMap Init.Data.String.Lemmas.IsEmpty
use crate::r#gen::Init::ByCases::{initialize_Init_ByCases, runtime_initialize_Init_ByCases};
use crate::r#gen::Init::Data::Iterators::Lemmas::Basic::{
    initialize_Init_Data_Iterators_Lemmas_Basic,
    runtime_initialize_Init_Data_Iterators_Lemmas_Basic,
};
use crate::r#gen::Init::Data::Iterators::Lemmas::Combinators::FilterMap::{
    initialize_Init_Data_Iterators_Lemmas_Combinators_FilterMap,
    runtime_initialize_Init_Data_Iterators_Lemmas_Combinators_FilterMap,
};
use crate::r#gen::Init::Data::Iterators::Lemmas::Consumers::Collect::{
    initialize_Init_Data_Iterators_Lemmas_Consumers_Collect,
    runtime_initialize_Init_Data_Iterators_Lemmas_Consumers_Collect,
};
use crate::r#gen::Init::Data::Option::Lemmas::{
    initialize_Init_Data_Option_Lemmas, runtime_initialize_Init_Data_Option_Lemmas,
};
use crate::r#gen::Init::Data::Order::Lemmas::{
    initialize_Init_Data_Order_Lemmas, runtime_initialize_Init_Data_Order_Lemmas,
};
use crate::r#gen::Init::Data::String::Lemmas::IsEmpty::{
    initialize_Init_Data_String_Lemmas_IsEmpty, runtime_initialize_Init_Data_String_Lemmas_IsEmpty,
};
use crate::r#gen::Init::Data::String::Lemmas::Order::{
    initialize_Init_Data_String_Lemmas_Order, runtime_initialize_Init_Data_String_Lemmas_Order,
};
use crate::r#gen::Init::Data::String::Lemmas::Pattern::Basic::{
    initialize_Init_Data_String_Lemmas_Pattern_Basic,
    runtime_initialize_Init_Data_String_Lemmas_Pattern_Basic,
};
use crate::r#gen::Init::Data::String::OrderInstances::{
    initialize_Init_Data_String_OrderInstances, runtime_initialize_Init_Data_String_OrderInstances,
};
use crate::r#gen::Init::Data::String::Search::{
    initialize_Init_Data_String_Search, runtime_initialize_Init_Data_String_Search,
};
use crate::r#gen::Init::Data::String::Slice::{
    initialize_Init_Data_String_Slice, runtime_initialize_Init_Data_String_Slice,
};
use crate::r#gen::Init::Data::String::Subslice::l_String_Slice_subslice_x21;
use crate::r#gen::Init::Data::String::Termination::{
    initialize_Init_Data_String_Termination, runtime_initialize_Init_Data_String_Termination,
};
use crate::lean_imports_rs::Init::Prelude::lean_nat_sub;
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_alloc_ctor, lean_apply_1, lean_apply_2, lean_apply_3,
    lean_apply_5, lean_box, lean_ctor_get, lean_ctor_set, lean_dec, lean_dec_ref,
    lean_dec_ref_known, lean_inc, lean_inc_ref, lean_io_result_is_error, lean_io_result_mk_ok,
    lean_is_exclusive, lean_obj_tag,
};
pub unsafe fn l___private_Init_Data_String_Lemmas_Pattern_Split_Basic_0__String_Slice_Pattern_Model_split_match__1_splitter___redArg(
    mut v_x_164_: *mut LeanObject,
    mut v_h__1_165_: *mut LeanObject,
    mut v_h__2_166_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_164_) == 0 {
        let mut v___x_167_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_165_);
        v___x_167_ = lean_apply_1(v_h__2_166_, lean_box(0));
        return v___x_167_;
    } else {
        let mut v_val_168_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_169_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_166_);
        v_val_168_ = lean_ctor_get(v_x_164_, 0);
        lean_inc(v_val_168_);
        lean_dec_ref_known(v_x_164_, 1);
        v___x_169_ = lean_apply_2(v_h__1_165_, v_val_168_, lean_box(0));
        return v___x_169_;
    }
}
pub unsafe fn l___private_Init_Data_String_Lemmas_Pattern_Split_Basic_0__String_Slice_Pattern_Model_split_match__1_splitter(
    mut v_s_170_: *mut LeanObject,
    mut v_motive_171_: *mut LeanObject,
    mut v_x_172_: *mut LeanObject,
    mut v_h__1_173_: *mut LeanObject,
    mut v_h__2_174_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_172_) == 0 {
        let mut v___x_175_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_173_);
        v___x_175_ = lean_apply_1(v_h__2_174_, lean_box(0));
        return v___x_175_;
    } else {
        let mut v_val_176_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_177_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_174_);
        v_val_176_ = lean_ctor_get(v_x_172_, 0);
        lean_inc(v_val_176_);
        lean_dec_ref_known(v_x_172_, 1);
        v___x_177_ = lean_apply_2(v_h__1_173_, v_val_176_, lean_box(0));
        return v___x_177_;
    }
}
pub unsafe fn l___private_Init_Data_String_Lemmas_Pattern_Split_Basic_0__String_Slice_Pattern_Model_split_match__1_splitter___boxed(
    mut v_s_178_: *mut LeanObject,
    mut v_motive_179_: *mut LeanObject,
    mut v_x_180_: *mut LeanObject,
    mut v_h__1_181_: *mut LeanObject,
    mut v_h__2_182_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_183_: *mut LeanObject = core::ptr::null_mut();
    v_res_183_ = l___private_Init_Data_String_Lemmas_Pattern_Split_Basic_0__String_Slice_Pattern_Model_split_match__1_splitter(v_s_178_, v_motive_179_, v_x_180_, v_h__1_181_, v_h__2_182_);
    lean_dec_ref(v_s_178_);
    return v_res_183_;
}
pub unsafe fn l___private_Init_Data_String_Lemmas_Pattern_Split_Basic_0__String_Slice_Pattern_Model_splitFromSteps(
    mut v_s_184_: *mut LeanObject,
    mut v_currPos_185_: *mut LeanObject,
    mut v_l_186_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_startInclusive_187_: *mut LeanObject = core::ptr::null_mut();
    let mut v_endExclusive_188_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_189_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_190_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_191_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_192_: *mut LeanObject = core::ptr::null_mut();
    let mut v_head_193_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_194_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_196_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_198_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_199_: u8 = 0;
    let mut v_startPos_200_: *mut LeanObject = core::ptr::null_mut();
    let mut v_endPos_201_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_202_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_203_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_205_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_206_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_207_: u8 = 0;
    let mut v_unused_208_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_l_186_) == 0 {
                    v_startInclusive_187_ = lean_ctor_get(v_s_184_, 1);
                    v_endExclusive_188_ = lean_ctor_get(v_s_184_, 2);
                    v___x_189_ = lean_nat_sub(v_endExclusive_188_, v_startInclusive_187_);
                    v___x_190_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v___x_190_, 0, v_currPos_185_);
                    lean_ctor_set(v___x_190_, 1, v___x_189_);
                    v___x_191_ = lean_box(0);
                    v___x_192_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v___x_192_, 0, v___x_190_);
                    lean_ctor_set(v___x_192_, 1, v___x_191_);
                    return v___x_192_;
                } else {
                    v_head_193_ = lean_ctor_get(v_l_186_, 0);
                    if lean_obj_tag(v_head_193_) == 0 {
                        v_tail_194_ = lean_ctor_get(v_l_186_, 1);
                        lean_inc(v_tail_194_);
                        lean_dec_ref_known(v_l_186_, 2);
                        v_l_186_ = v_tail_194_;
                        state = 0;
                        continue;
                    } else {
                        lean_inc_ref(v_head_193_);
                        v_tail_196_ = lean_ctor_get(v_l_186_, 1);
                        v_isSharedCheck_207_ = (!lean_is_exclusive(v_l_186_)) as u8;
                        if v_isSharedCheck_207_ == 0 {
                            v_unused_208_ = lean_ctor_get(v_l_186_, 0);
                            lean_dec(v_unused_208_);
                            v___x_198_ = v_l_186_;
                            v_isShared_199_ = v_isSharedCheck_207_;
                            state = 1;
                            continue;
                        } else {
                            lean_inc(v_tail_196_);
                            lean_dec(v_l_186_);
                            v___x_198_ = lean_box(0);
                            v_isShared_199_ = v_isSharedCheck_207_;
                            state = 1;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v_startPos_200_ = lean_ctor_get(v_head_193_, 0);
                lean_inc(v_startPos_200_);
                v_endPos_201_ = lean_ctor_get(v_head_193_, 1);
                lean_inc(v_endPos_201_);
                lean_dec_ref_known(v_head_193_, 2);
                v___x_202_ = l_String_Slice_subslice_x21(v_s_184_, v_currPos_185_, v_startPos_200_);
                v___x_203_ = l___private_Init_Data_String_Lemmas_Pattern_Split_Basic_0__String_Slice_Pattern_Model_splitFromSteps(v_s_184_, v_endPos_201_, v_tail_196_);
                if v_isShared_199_ == 0 {
                    lean_ctor_set(v___x_198_, 1, v___x_203_);
                    lean_ctor_set(v___x_198_, 0, v___x_202_);
                    v___x_205_ = v___x_198_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_206_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_206_, 0, v___x_202_);
                    lean_ctor_set(v_reuseFailAlloc_206_, 1, v___x_203_);
                    v___x_205_ = v_reuseFailAlloc_206_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_205_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_String_Lemmas_Pattern_Split_Basic_0__String_Slice_Pattern_Model_splitFromSteps___boxed(
    mut v_s_209_: *mut LeanObject,
    mut v_currPos_210_: *mut LeanObject,
    mut v_l_211_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_212_: *mut LeanObject = core::ptr::null_mut();
    v_res_212_ = l___private_Init_Data_String_Lemmas_Pattern_Split_Basic_0__String_Slice_Pattern_Model_splitFromSteps(v_s_209_, v_currPos_210_, v_l_211_);
    lean_dec_ref(v_s_209_);
    return v_res_212_;
}
pub unsafe fn l___private_Init_Data_String_Lemmas_Pattern_Split_Basic_0__String_Slice_Pattern_Model_splitFromSteps_match__1_splitter___redArg(
    mut v_l_213_: *mut LeanObject,
    mut v_h__1_214_: *mut LeanObject,
    mut v_h__2_215_: *mut LeanObject,
    mut v_h__3_216_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_l_213_) == 0 {
        let mut v___x_217_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_218_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__3_216_);
        lean_dec(v_h__2_215_);
        v___x_217_ = lean_box(0);
        v___x_218_ = lean_apply_1(v_h__1_214_, v___x_217_);
        return v___x_218_;
    } else {
        let mut v_head_219_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_214_);
        v_head_219_ = lean_ctor_get(v_l_213_, 0);
        lean_inc(v_head_219_);
        if lean_obj_tag(v_head_219_) == 0 {
            let mut v_tail_220_: *mut LeanObject = core::ptr::null_mut();
            let mut v_startPos_221_: *mut LeanObject = core::ptr::null_mut();
            let mut v_endPos_222_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_223_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__3_216_);
            v_tail_220_ = lean_ctor_get(v_l_213_, 1);
            lean_inc(v_tail_220_);
            lean_dec_ref_known(v_l_213_, 2);
            v_startPos_221_ = lean_ctor_get(v_head_219_, 0);
            lean_inc(v_startPos_221_);
            v_endPos_222_ = lean_ctor_get(v_head_219_, 1);
            lean_inc(v_endPos_222_);
            lean_dec_ref_known(v_head_219_, 2);
            v___x_223_ = lean_apply_3(v_h__2_215_, v_startPos_221_, v_endPos_222_, v_tail_220_);
            return v___x_223_;
        } else {
            let mut v_tail_224_: *mut LeanObject = core::ptr::null_mut();
            let mut v_startPos_225_: *mut LeanObject = core::ptr::null_mut();
            let mut v_endPos_226_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_227_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__2_215_);
            v_tail_224_ = lean_ctor_get(v_l_213_, 1);
            lean_inc(v_tail_224_);
            lean_dec_ref_known(v_l_213_, 2);
            v_startPos_225_ = lean_ctor_get(v_head_219_, 0);
            lean_inc(v_startPos_225_);
            v_endPos_226_ = lean_ctor_get(v_head_219_, 1);
            lean_inc(v_endPos_226_);
            lean_dec_ref_known(v_head_219_, 2);
            v___x_227_ = lean_apply_3(v_h__3_216_, v_startPos_225_, v_endPos_226_, v_tail_224_);
            return v___x_227_;
        }
    }
}
pub unsafe fn l___private_Init_Data_String_Lemmas_Pattern_Split_Basic_0__String_Slice_Pattern_Model_splitFromSteps_match__1_splitter(
    mut v_s_228_: *mut LeanObject,
    mut v_motive_229_: *mut LeanObject,
    mut v_l_230_: *mut LeanObject,
    mut v_h__1_231_: *mut LeanObject,
    mut v_h__2_232_: *mut LeanObject,
    mut v_h__3_233_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_l_230_) == 0 {
        let mut v___x_234_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_235_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__3_233_);
        lean_dec(v_h__2_232_);
        v___x_234_ = lean_box(0);
        v___x_235_ = lean_apply_1(v_h__1_231_, v___x_234_);
        return v___x_235_;
    } else {
        let mut v_head_236_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_231_);
        v_head_236_ = lean_ctor_get(v_l_230_, 0);
        lean_inc(v_head_236_);
        if lean_obj_tag(v_head_236_) == 0 {
            let mut v_tail_237_: *mut LeanObject = core::ptr::null_mut();
            let mut v_startPos_238_: *mut LeanObject = core::ptr::null_mut();
            let mut v_endPos_239_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_240_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__3_233_);
            v_tail_237_ = lean_ctor_get(v_l_230_, 1);
            lean_inc(v_tail_237_);
            lean_dec_ref_known(v_l_230_, 2);
            v_startPos_238_ = lean_ctor_get(v_head_236_, 0);
            lean_inc(v_startPos_238_);
            v_endPos_239_ = lean_ctor_get(v_head_236_, 1);
            lean_inc(v_endPos_239_);
            lean_dec_ref_known(v_head_236_, 2);
            v___x_240_ = lean_apply_3(v_h__2_232_, v_startPos_238_, v_endPos_239_, v_tail_237_);
            return v___x_240_;
        } else {
            let mut v_tail_241_: *mut LeanObject = core::ptr::null_mut();
            let mut v_startPos_242_: *mut LeanObject = core::ptr::null_mut();
            let mut v_endPos_243_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_244_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__2_232_);
            v_tail_241_ = lean_ctor_get(v_l_230_, 1);
            lean_inc(v_tail_241_);
            lean_dec_ref_known(v_l_230_, 2);
            v_startPos_242_ = lean_ctor_get(v_head_236_, 0);
            lean_inc(v_startPos_242_);
            v_endPos_243_ = lean_ctor_get(v_head_236_, 1);
            lean_inc(v_endPos_243_);
            lean_dec_ref_known(v_head_236_, 2);
            v___x_244_ = lean_apply_3(v_h__3_233_, v_startPos_242_, v_endPos_243_, v_tail_241_);
            return v___x_244_;
        }
    }
}
pub unsafe fn l___private_Init_Data_String_Lemmas_Pattern_Split_Basic_0__String_Slice_Pattern_Model_splitFromSteps_match__1_splitter___boxed(
    mut v_s_245_: *mut LeanObject,
    mut v_motive_246_: *mut LeanObject,
    mut v_l_247_: *mut LeanObject,
    mut v_h__1_248_: *mut LeanObject,
    mut v_h__2_249_: *mut LeanObject,
    mut v_h__3_250_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_251_: *mut LeanObject = core::ptr::null_mut();
    v_res_251_ = l___private_Init_Data_String_Lemmas_Pattern_Split_Basic_0__String_Slice_Pattern_Model_splitFromSteps_match__1_splitter(v_s_245_, v_motive_246_, v_l_247_, v_h__1_248_, v_h__2_249_, v_h__3_250_);
    lean_dec_ref(v_s_245_);
    return v_res_251_;
}
pub unsafe fn l___private_Init_Data_String_Lemmas_Pattern_Split_Basic_0__String_Slice_SplitIterator_instIteratorIdSubslice_match__3_splitter___redArg(
    mut v_x_252_: *mut LeanObject,
    mut v_h__1_253_: *mut LeanObject,
    mut v_h__2_254_: *mut LeanObject,
    mut v_h__3_255_: *mut LeanObject,
    mut v_h__4_256_: *mut LeanObject,
) -> *mut LeanObject {
    match lean_obj_tag(v_x_252_) {
        0 => {
            let mut v_out_257_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__4_256_);
            lean_dec(v_h__3_255_);
            v_out_257_ = lean_ctor_get(v_x_252_, 1);
            lean_inc(v_out_257_);
            if lean_obj_tag(v_out_257_) == 0 {
                let mut v_it_258_: *mut LeanObject = core::ptr::null_mut();
                let mut v_startPos_259_: *mut LeanObject = core::ptr::null_mut();
                let mut v_endPos_260_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_261_: *mut LeanObject = core::ptr::null_mut();
                lean_dec(v_h__1_253_);
                v_it_258_ = lean_ctor_get(v_x_252_, 0);
                lean_inc(v_it_258_);
                lean_dec_ref_known(v_x_252_, 2);
                v_startPos_259_ = lean_ctor_get(v_out_257_, 0);
                lean_inc(v_startPos_259_);
                v_endPos_260_ = lean_ctor_get(v_out_257_, 1);
                lean_inc(v_endPos_260_);
                lean_dec_ref_known(v_out_257_, 2);
                v___x_261_ = lean_apply_5(
                    v_h__2_254_,
                    v_it_258_,
                    v_startPos_259_,
                    v_endPos_260_,
                    lean_box(0),
                    lean_box(0),
                );
                return v___x_261_;
            } else {
                let mut v_it_262_: *mut LeanObject = core::ptr::null_mut();
                let mut v_startPos_263_: *mut LeanObject = core::ptr::null_mut();
                let mut v_endPos_264_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_265_: *mut LeanObject = core::ptr::null_mut();
                lean_dec(v_h__2_254_);
                v_it_262_ = lean_ctor_get(v_x_252_, 0);
                lean_inc(v_it_262_);
                lean_dec_ref_known(v_x_252_, 2);
                v_startPos_263_ = lean_ctor_get(v_out_257_, 0);
                lean_inc(v_startPos_263_);
                v_endPos_264_ = lean_ctor_get(v_out_257_, 1);
                lean_inc(v_endPos_264_);
                lean_dec_ref_known(v_out_257_, 2);
                v___x_265_ = lean_apply_5(
                    v_h__1_253_,
                    v_it_262_,
                    v_startPos_263_,
                    v_endPos_264_,
                    lean_box(0),
                    lean_box(0),
                );
                return v___x_265_;
            }
        }
        1 => {
            let mut v_it_266_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_267_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__4_256_);
            lean_dec(v_h__2_254_);
            lean_dec(v_h__1_253_);
            v_it_266_ = lean_ctor_get(v_x_252_, 0);
            lean_inc(v_it_266_);
            lean_dec_ref_known(v_x_252_, 1);
            v___x_267_ = lean_apply_3(v_h__3_255_, v_it_266_, lean_box(0), lean_box(0));
            return v___x_267_;
        }
        _ => {
            let mut v___x_268_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__3_255_);
            lean_dec(v_h__2_254_);
            lean_dec(v_h__1_253_);
            v___x_268_ = lean_apply_2(v_h__4_256_, lean_box(0), lean_box(0));
            return v___x_268_;
        }
    }
}
pub unsafe fn l___private_Init_Data_String_Lemmas_Pattern_Split_Basic_0__String_Slice_SplitIterator_instIteratorIdSubslice_match__3_splitter(
    mut v_00_u03c3_269_: *mut LeanObject,
    mut v_inst_270_: *mut LeanObject,
    mut v_s_271_: *mut LeanObject,
    mut v_searcher_272_: *mut LeanObject,
    mut v_motive_273_: *mut LeanObject,
    mut v_x_274_: *mut LeanObject,
    mut v_h__1_275_: *mut LeanObject,
    mut v_h__2_276_: *mut LeanObject,
    mut v_h__3_277_: *mut LeanObject,
    mut v_h__4_278_: *mut LeanObject,
) -> *mut LeanObject {
    match lean_obj_tag(v_x_274_) {
        0 => {
            let mut v_out_279_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__4_278_);
            lean_dec(v_h__3_277_);
            v_out_279_ = lean_ctor_get(v_x_274_, 1);
            lean_inc(v_out_279_);
            if lean_obj_tag(v_out_279_) == 0 {
                let mut v_it_280_: *mut LeanObject = core::ptr::null_mut();
                let mut v_startPos_281_: *mut LeanObject = core::ptr::null_mut();
                let mut v_endPos_282_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_283_: *mut LeanObject = core::ptr::null_mut();
                lean_dec(v_h__1_275_);
                v_it_280_ = lean_ctor_get(v_x_274_, 0);
                lean_inc(v_it_280_);
                lean_dec_ref_known(v_x_274_, 2);
                v_startPos_281_ = lean_ctor_get(v_out_279_, 0);
                lean_inc(v_startPos_281_);
                v_endPos_282_ = lean_ctor_get(v_out_279_, 1);
                lean_inc(v_endPos_282_);
                lean_dec_ref_known(v_out_279_, 2);
                v___x_283_ = lean_apply_5(
                    v_h__2_276_,
                    v_it_280_,
                    v_startPos_281_,
                    v_endPos_282_,
                    lean_box(0),
                    lean_box(0),
                );
                return v___x_283_;
            } else {
                let mut v_it_284_: *mut LeanObject = core::ptr::null_mut();
                let mut v_startPos_285_: *mut LeanObject = core::ptr::null_mut();
                let mut v_endPos_286_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_287_: *mut LeanObject = core::ptr::null_mut();
                lean_dec(v_h__2_276_);
                v_it_284_ = lean_ctor_get(v_x_274_, 0);
                lean_inc(v_it_284_);
                lean_dec_ref_known(v_x_274_, 2);
                v_startPos_285_ = lean_ctor_get(v_out_279_, 0);
                lean_inc(v_startPos_285_);
                v_endPos_286_ = lean_ctor_get(v_out_279_, 1);
                lean_inc(v_endPos_286_);
                lean_dec_ref_known(v_out_279_, 2);
                v___x_287_ = lean_apply_5(
                    v_h__1_275_,
                    v_it_284_,
                    v_startPos_285_,
                    v_endPos_286_,
                    lean_box(0),
                    lean_box(0),
                );
                return v___x_287_;
            }
        }
        1 => {
            let mut v_it_288_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_289_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__4_278_);
            lean_dec(v_h__2_276_);
            lean_dec(v_h__1_275_);
            v_it_288_ = lean_ctor_get(v_x_274_, 0);
            lean_inc(v_it_288_);
            lean_dec_ref_known(v_x_274_, 1);
            v___x_289_ = lean_apply_3(v_h__3_277_, v_it_288_, lean_box(0), lean_box(0));
            return v___x_289_;
        }
        _ => {
            let mut v___x_290_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__3_277_);
            lean_dec(v_h__2_276_);
            lean_dec(v_h__1_275_);
            v___x_290_ = lean_apply_2(v_h__4_278_, lean_box(0), lean_box(0));
            return v___x_290_;
        }
    }
}
pub unsafe fn l___private_Init_Data_String_Lemmas_Pattern_Split_Basic_0__String_Slice_SplitIterator_instIteratorIdSubslice_match__3_splitter___boxed(
    mut v_00_u03c3_291_: *mut LeanObject,
    mut v_inst_292_: *mut LeanObject,
    mut v_s_293_: *mut LeanObject,
    mut v_searcher_294_: *mut LeanObject,
    mut v_motive_295_: *mut LeanObject,
    mut v_x_296_: *mut LeanObject,
    mut v_h__1_297_: *mut LeanObject,
    mut v_h__2_298_: *mut LeanObject,
    mut v_h__3_299_: *mut LeanObject,
    mut v_h__4_300_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_301_: *mut LeanObject = core::ptr::null_mut();
    v_res_301_ = l___private_Init_Data_String_Lemmas_Pattern_Split_Basic_0__String_Slice_SplitIterator_instIteratorIdSubslice_match__3_splitter(v_00_u03c3_291_, v_inst_292_, v_s_293_, v_searcher_294_, v_motive_295_, v_x_296_, v_h__1_297_, v_h__2_298_, v_h__3_299_, v_h__4_300_);
    lean_dec(v_searcher_294_);
    lean_dec_ref(v_s_293_);
    lean_dec(v_inst_292_);
    return v_res_301_;
}
pub unsafe fn l___private_Init_Data_String_Lemmas_Pattern_Split_Basic_0__Std_Iter_toArray__eq__match__step_match__1_splitter___redArg(
    mut v_x_302_: *mut LeanObject,
    mut v_h__1_303_: *mut LeanObject,
    mut v_h__2_304_: *mut LeanObject,
    mut v_h__3_305_: *mut LeanObject,
) -> *mut LeanObject {
    match lean_obj_tag(v_x_302_) {
        0 => {
            let mut v_it_306_: *mut LeanObject = core::ptr::null_mut();
            let mut v_out_307_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_308_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__3_305_);
            lean_dec(v_h__2_304_);
            v_it_306_ = lean_ctor_get(v_x_302_, 0);
            lean_inc(v_it_306_);
            v_out_307_ = lean_ctor_get(v_x_302_, 1);
            lean_inc(v_out_307_);
            lean_dec_ref_known(v_x_302_, 2);
            v___x_308_ = lean_apply_2(v_h__1_303_, v_it_306_, v_out_307_);
            return v___x_308_;
        }
        1 => {
            let mut v_it_309_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_310_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__3_305_);
            lean_dec(v_h__1_303_);
            v_it_309_ = lean_ctor_get(v_x_302_, 0);
            lean_inc(v_it_309_);
            lean_dec_ref_known(v_x_302_, 1);
            v___x_310_ = lean_apply_1(v_h__2_304_, v_it_309_);
            return v___x_310_;
        }
        _ => {
            let mut v___x_311_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_312_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__2_304_);
            lean_dec(v_h__1_303_);
            v___x_311_ = lean_box(0);
            v___x_312_ = lean_apply_1(v_h__3_305_, v___x_311_);
            return v___x_312_;
        }
    }
}
pub unsafe fn l___private_Init_Data_String_Lemmas_Pattern_Split_Basic_0__Std_Iter_toArray__eq__match__step_match__1_splitter(
    mut v_00_u03b1_313_: *mut LeanObject,
    mut v_00_u03b2_314_: *mut LeanObject,
    mut v_motive_315_: *mut LeanObject,
    mut v_x_316_: *mut LeanObject,
    mut v_h__1_317_: *mut LeanObject,
    mut v_h__2_318_: *mut LeanObject,
    mut v_h__3_319_: *mut LeanObject,
) -> *mut LeanObject {
    match lean_obj_tag(v_x_316_) {
        0 => {
            let mut v_it_320_: *mut LeanObject = core::ptr::null_mut();
            let mut v_out_321_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_322_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__3_319_);
            lean_dec(v_h__2_318_);
            v_it_320_ = lean_ctor_get(v_x_316_, 0);
            lean_inc(v_it_320_);
            v_out_321_ = lean_ctor_get(v_x_316_, 1);
            lean_inc(v_out_321_);
            lean_dec_ref_known(v_x_316_, 2);
            v___x_322_ = lean_apply_2(v_h__1_317_, v_it_320_, v_out_321_);
            return v___x_322_;
        }
        1 => {
            let mut v_it_323_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_324_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__3_319_);
            lean_dec(v_h__1_317_);
            v_it_323_ = lean_ctor_get(v_x_316_, 0);
            lean_inc(v_it_323_);
            lean_dec_ref_known(v_x_316_, 1);
            v___x_324_ = lean_apply_1(v_h__2_318_, v_it_323_);
            return v___x_324_;
        }
        _ => {
            let mut v___x_325_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_326_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__2_318_);
            lean_dec(v_h__1_317_);
            v___x_325_ = lean_box(0);
            v___x_326_ = lean_apply_1(v_h__3_319_, v___x_325_);
            return v___x_326_;
        }
    }
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Init_Data_String_Lemmas_Pattern_Split_Basic(
    builtin: u8,
) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Init_Data_String_Lemmas_Pattern_Basic(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_String_Slice(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_String_Search(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Option_Lemmas(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_String_Termination(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_String_Lemmas_Order(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_ByCases(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Order_Lemmas(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_String_OrderInstances(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Iterators_Lemmas_Basic(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Iterators_Lemmas_Consumers_Collect(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Iterators_Lemmas_Combinators_FilterMap(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_String_Lemmas_IsEmpty(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Init_Data_String_Lemmas_Pattern_Split_Basic(
    builtin: u8,
) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_meta_initialized = true;
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Init_Data_String_Lemmas_Pattern_Split_Basic(
    builtin: u8,
) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Init_Data_String_Lemmas_Pattern_Basic(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Data_String_Slice(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Data_String_Search(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Data_Option_Lemmas(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Data_String_Termination(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Data_String_Lemmas_Order(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_ByCases(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Data_Order_Lemmas(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Data_String_OrderInstances(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Data_Iterators_Lemmas_Basic(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Data_Iterators_Lemmas_Consumers_Collect(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Data_Iterators_Lemmas_Combinators_FilterMap(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Data_String_Lemmas_IsEmpty(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_String_Lemmas_Pattern_Split_Basic(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Init_Data_String_Lemmas_Pattern_Split_Basic(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Init_Data_String_Lemmas_Pattern_Split_Basic(builtin);
}
