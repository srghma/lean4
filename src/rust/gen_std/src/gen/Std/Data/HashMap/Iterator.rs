// Lean compiler output
// Module: Std.Data.HashMap.Iterator
// Imports: Std.Data.DHashMap.Iterator Std.Data.HashMap.Basic Std.Data.HashMap.Raw Init.Data.Iterators.Combinators.FilterMap
use crate::r#gen::Init::Data::Iterators::Combinators::FilterMap::{
    initialize_Init_Data_Iterators_Combinators_FilterMap,
    runtime_initialize_Init_Data_Iterators_Combinators_FilterMap,
};
use crate::r#gen::Std::Data::DHashMap::Iterator::{
    initialize_Std_Data_DHashMap_Iterator, runtime_initialize_Std_Data_DHashMap_Iterator,
};
use crate::r#gen::Std::Data::HashMap::Basic::{
    initialize_Std_Data_HashMap_Basic, runtime_initialize_Std_Data_HashMap_Basic,
};
use crate::r#gen::Std::Data::HashMap::Raw::{
    initialize_Std_Data_HashMap_Raw, runtime_initialize_Std_Data_HashMap_Raw,
};
pub unsafe fn l_Std_HashMap_Raw_iter___redArg(
    mut v_m_193_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_buckets_194_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_196_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_197_: u8 = 0;
    let mut v___x_198_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_200_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_201_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_202_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_203_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_204_: u8 = 0;
    let mut v_unused_205_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_buckets_194_ = leanh::lean_ctor_get(v_m_193_, 1);
                v_isSharedCheck_204_ = (!leanh::lean_is_exclusive(v_m_193_)) as u8;
                if v_isSharedCheck_204_ == 0 {
                    v_unused_205_ = leanh::lean_ctor_get(v_m_193_, 0);
                    leanh::lean_dec(v_unused_205_);
                    v___x_196_ = v_m_193_;
                    v_isShared_197_ = v_isSharedCheck_204_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_buckets_194_);
                    leanh::lean_dec(v_m_193_);
                    v___x_196_ = leanh::lean_box(0);
                    v_isShared_197_ = v_isSharedCheck_204_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_198_ = leanh::lean_unsigned_to_nat(0);
                if v_isShared_197_ == 0 {
                    leanh::lean_ctor_set(v___x_196_, 1, v___x_198_);
                    leanh::lean_ctor_set(v___x_196_, 0, v_buckets_194_);
                    v___x_200_ = v___x_196_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_203_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_203_, 0, v_buckets_194_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_203_, 1, v___x_198_);
                    v___x_200_ = v_reuseFailAlloc_203_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_201_ = leanh::lean_box(0);
                v___x_202_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_202_, 0, v___x_200_);
                leanh::lean_ctor_set(v___x_202_, 1, v___x_201_);
                return v___x_202_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_HashMap_Raw_iter(
    mut v_00_u03b1_206_: *mut leanh::LeanObject,
    mut v_00_u03b2_207_: *mut leanh::LeanObject,
    mut v_m_208_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_buckets_209_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_211_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_212_: u8 = 0;
    let mut v___x_213_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_215_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_216_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_217_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_218_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_219_: u8 = 0;
    let mut v_unused_220_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_buckets_209_ = leanh::lean_ctor_get(v_m_208_, 1);
                v_isSharedCheck_219_ = (!leanh::lean_is_exclusive(v_m_208_)) as u8;
                if v_isSharedCheck_219_ == 0 {
                    v_unused_220_ = leanh::lean_ctor_get(v_m_208_, 0);
                    leanh::lean_dec(v_unused_220_);
                    v___x_211_ = v_m_208_;
                    v_isShared_212_ = v_isSharedCheck_219_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_buckets_209_);
                    leanh::lean_dec(v_m_208_);
                    v___x_211_ = leanh::lean_box(0);
                    v_isShared_212_ = v_isSharedCheck_219_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_213_ = leanh::lean_unsigned_to_nat(0);
                if v_isShared_212_ == 0 {
                    leanh::lean_ctor_set(v___x_211_, 1, v___x_213_);
                    leanh::lean_ctor_set(v___x_211_, 0, v_buckets_209_);
                    v___x_215_ = v___x_211_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_218_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_218_, 0, v_buckets_209_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_218_, 1, v___x_213_);
                    v___x_215_ = v_reuseFailAlloc_218_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_216_ = leanh::lean_box(0);
                v___x_217_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_217_, 0, v___x_215_);
                leanh::lean_ctor_set(v___x_217_, 1, v___x_216_);
                return v___x_217_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_HashMap_Raw_keysIter___redArg(
    mut v_m_221_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_buckets_222_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_224_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_225_: u8 = 0;
    let mut v___x_226_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_228_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_229_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_230_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_231_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_232_: u8 = 0;
    let mut v_unused_233_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_buckets_222_ = leanh::lean_ctor_get(v_m_221_, 1);
                v_isSharedCheck_232_ = (!leanh::lean_is_exclusive(v_m_221_)) as u8;
                if v_isSharedCheck_232_ == 0 {
                    v_unused_233_ = leanh::lean_ctor_get(v_m_221_, 0);
                    leanh::lean_dec(v_unused_233_);
                    v___x_224_ = v_m_221_;
                    v_isShared_225_ = v_isSharedCheck_232_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_buckets_222_);
                    leanh::lean_dec(v_m_221_);
                    v___x_224_ = leanh::lean_box(0);
                    v_isShared_225_ = v_isSharedCheck_232_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_226_ = leanh::lean_unsigned_to_nat(0);
                if v_isShared_225_ == 0 {
                    leanh::lean_ctor_set(v___x_224_, 1, v___x_226_);
                    leanh::lean_ctor_set(v___x_224_, 0, v_buckets_222_);
                    v___x_228_ = v___x_224_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_231_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_231_, 0, v_buckets_222_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_231_, 1, v___x_226_);
                    v___x_228_ = v_reuseFailAlloc_231_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_229_ = leanh::lean_box(0);
                v___x_230_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_230_, 0, v___x_228_);
                leanh::lean_ctor_set(v___x_230_, 1, v___x_229_);
                return v___x_230_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_HashMap_Raw_keysIter(
    mut v_00_u03b1_234_: *mut leanh::LeanObject,
    mut v_00_u03b2_235_: *mut leanh::LeanObject,
    mut v_m_236_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_buckets_237_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_239_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_240_: u8 = 0;
    let mut v___x_241_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_243_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_244_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_245_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_246_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_247_: u8 = 0;
    let mut v_unused_248_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_buckets_237_ = leanh::lean_ctor_get(v_m_236_, 1);
                v_isSharedCheck_247_ = (!leanh::lean_is_exclusive(v_m_236_)) as u8;
                if v_isSharedCheck_247_ == 0 {
                    v_unused_248_ = leanh::lean_ctor_get(v_m_236_, 0);
                    leanh::lean_dec(v_unused_248_);
                    v___x_239_ = v_m_236_;
                    v_isShared_240_ = v_isSharedCheck_247_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_buckets_237_);
                    leanh::lean_dec(v_m_236_);
                    v___x_239_ = leanh::lean_box(0);
                    v_isShared_240_ = v_isSharedCheck_247_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_241_ = leanh::lean_unsigned_to_nat(0);
                if v_isShared_240_ == 0 {
                    leanh::lean_ctor_set(v___x_239_, 1, v___x_241_);
                    leanh::lean_ctor_set(v___x_239_, 0, v_buckets_237_);
                    v___x_243_ = v___x_239_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_246_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_246_, 0, v_buckets_237_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_246_, 1, v___x_241_);
                    v___x_243_ = v_reuseFailAlloc_246_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_244_ = leanh::lean_box(0);
                v___x_245_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_245_, 0, v___x_243_);
                leanh::lean_ctor_set(v___x_245_, 1, v___x_244_);
                return v___x_245_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_HashMap_Raw_valuesIter___redArg(
    mut v_m_249_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_buckets_250_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_252_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_253_: u8 = 0;
    let mut v___x_254_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_256_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_257_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_258_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_259_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_260_: u8 = 0;
    let mut v_unused_261_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_buckets_250_ = leanh::lean_ctor_get(v_m_249_, 1);
                v_isSharedCheck_260_ = (!leanh::lean_is_exclusive(v_m_249_)) as u8;
                if v_isSharedCheck_260_ == 0 {
                    v_unused_261_ = leanh::lean_ctor_get(v_m_249_, 0);
                    leanh::lean_dec(v_unused_261_);
                    v___x_252_ = v_m_249_;
                    v_isShared_253_ = v_isSharedCheck_260_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_buckets_250_);
                    leanh::lean_dec(v_m_249_);
                    v___x_252_ = leanh::lean_box(0);
                    v_isShared_253_ = v_isSharedCheck_260_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_254_ = leanh::lean_unsigned_to_nat(0);
                if v_isShared_253_ == 0 {
                    leanh::lean_ctor_set(v___x_252_, 1, v___x_254_);
                    leanh::lean_ctor_set(v___x_252_, 0, v_buckets_250_);
                    v___x_256_ = v___x_252_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_259_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_259_, 0, v_buckets_250_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_259_, 1, v___x_254_);
                    v___x_256_ = v_reuseFailAlloc_259_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_257_ = leanh::lean_box(0);
                v___x_258_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_258_, 0, v___x_256_);
                leanh::lean_ctor_set(v___x_258_, 1, v___x_257_);
                return v___x_258_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_HashMap_Raw_valuesIter(
    mut v_00_u03b1_262_: *mut leanh::LeanObject,
    mut v_00_u03b2_263_: *mut leanh::LeanObject,
    mut v_m_264_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_buckets_265_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_267_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_268_: u8 = 0;
    let mut v___x_269_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_271_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_272_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_273_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_274_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_275_: u8 = 0;
    let mut v_unused_276_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_buckets_265_ = leanh::lean_ctor_get(v_m_264_, 1);
                v_isSharedCheck_275_ = (!leanh::lean_is_exclusive(v_m_264_)) as u8;
                if v_isSharedCheck_275_ == 0 {
                    v_unused_276_ = leanh::lean_ctor_get(v_m_264_, 0);
                    leanh::lean_dec(v_unused_276_);
                    v___x_267_ = v_m_264_;
                    v_isShared_268_ = v_isSharedCheck_275_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_buckets_265_);
                    leanh::lean_dec(v_m_264_);
                    v___x_267_ = leanh::lean_box(0);
                    v_isShared_268_ = v_isSharedCheck_275_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_269_ = leanh::lean_unsigned_to_nat(0);
                if v_isShared_268_ == 0 {
                    leanh::lean_ctor_set(v___x_267_, 1, v___x_269_);
                    leanh::lean_ctor_set(v___x_267_, 0, v_buckets_265_);
                    v___x_271_ = v___x_267_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_274_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_274_, 0, v_buckets_265_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_274_, 1, v___x_269_);
                    v___x_271_ = v_reuseFailAlloc_274_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_272_ = leanh::lean_box(0);
                v___x_273_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_273_, 0, v___x_271_);
                leanh::lean_ctor_set(v___x_273_, 1, v___x_272_);
                return v___x_273_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_HashMap_iter___redArg(
    mut v_m_277_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_buckets_278_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_280_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_281_: u8 = 0;
    let mut v___x_282_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_284_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_285_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_286_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_287_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_288_: u8 = 0;
    let mut v_unused_289_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_buckets_278_ = leanh::lean_ctor_get(v_m_277_, 1);
                v_isSharedCheck_288_ = (!leanh::lean_is_exclusive(v_m_277_)) as u8;
                if v_isSharedCheck_288_ == 0 {
                    v_unused_289_ = leanh::lean_ctor_get(v_m_277_, 0);
                    leanh::lean_dec(v_unused_289_);
                    v___x_280_ = v_m_277_;
                    v_isShared_281_ = v_isSharedCheck_288_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_buckets_278_);
                    leanh::lean_dec(v_m_277_);
                    v___x_280_ = leanh::lean_box(0);
                    v_isShared_281_ = v_isSharedCheck_288_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_282_ = leanh::lean_unsigned_to_nat(0);
                if v_isShared_281_ == 0 {
                    leanh::lean_ctor_set(v___x_280_, 1, v___x_282_);
                    leanh::lean_ctor_set(v___x_280_, 0, v_buckets_278_);
                    v___x_284_ = v___x_280_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_287_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_287_, 0, v_buckets_278_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_287_, 1, v___x_282_);
                    v___x_284_ = v_reuseFailAlloc_287_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_285_ = leanh::lean_box(0);
                v___x_286_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_286_, 0, v___x_284_);
                leanh::lean_ctor_set(v___x_286_, 1, v___x_285_);
                return v___x_286_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_HashMap_iter(
    mut v_00_u03b1_290_: *mut leanh::LeanObject,
    mut v_00_u03b2_291_: *mut leanh::LeanObject,
    mut v_inst_292_: *mut leanh::LeanObject,
    mut v_inst_293_: *mut leanh::LeanObject,
    mut v_m_294_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_buckets_295_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_297_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_298_: u8 = 0;
    let mut v___x_299_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_301_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_302_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_303_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_304_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_305_: u8 = 0;
    let mut v_unused_306_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_buckets_295_ = leanh::lean_ctor_get(v_m_294_, 1);
                v_isSharedCheck_305_ = (!leanh::lean_is_exclusive(v_m_294_)) as u8;
                if v_isSharedCheck_305_ == 0 {
                    v_unused_306_ = leanh::lean_ctor_get(v_m_294_, 0);
                    leanh::lean_dec(v_unused_306_);
                    v___x_297_ = v_m_294_;
                    v_isShared_298_ = v_isSharedCheck_305_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_buckets_295_);
                    leanh::lean_dec(v_m_294_);
                    v___x_297_ = leanh::lean_box(0);
                    v_isShared_298_ = v_isSharedCheck_305_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_299_ = leanh::lean_unsigned_to_nat(0);
                if v_isShared_298_ == 0 {
                    leanh::lean_ctor_set(v___x_297_, 1, v___x_299_);
                    leanh::lean_ctor_set(v___x_297_, 0, v_buckets_295_);
                    v___x_301_ = v___x_297_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_304_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_304_, 0, v_buckets_295_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_304_, 1, v___x_299_);
                    v___x_301_ = v_reuseFailAlloc_304_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_302_ = leanh::lean_box(0);
                v___x_303_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_303_, 0, v___x_301_);
                leanh::lean_ctor_set(v___x_303_, 1, v___x_302_);
                return v___x_303_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_HashMap_iter___boxed(
    mut v_00_u03b1_307_: *mut leanh::LeanObject,
    mut v_00_u03b2_308_: *mut leanh::LeanObject,
    mut v_inst_309_: *mut leanh::LeanObject,
    mut v_inst_310_: *mut leanh::LeanObject,
    mut v_m_311_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_312_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_312_ = l_Std_HashMap_iter(
        v_00_u03b1_307_,
        v_00_u03b2_308_,
        v_inst_309_,
        v_inst_310_,
        v_m_311_,
    );
    leanh::lean_dec_ref(v_inst_310_);
    leanh::lean_dec_ref(v_inst_309_);
    return v_res_312_;
}
pub unsafe fn l_Std_HashMap_keysIter___redArg(
    mut v_m_313_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_buckets_314_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_316_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_317_: u8 = 0;
    let mut v___x_318_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_320_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_321_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_322_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_323_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_324_: u8 = 0;
    let mut v_unused_325_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_buckets_314_ = leanh::lean_ctor_get(v_m_313_, 1);
                v_isSharedCheck_324_ = (!leanh::lean_is_exclusive(v_m_313_)) as u8;
                if v_isSharedCheck_324_ == 0 {
                    v_unused_325_ = leanh::lean_ctor_get(v_m_313_, 0);
                    leanh::lean_dec(v_unused_325_);
                    v___x_316_ = v_m_313_;
                    v_isShared_317_ = v_isSharedCheck_324_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_buckets_314_);
                    leanh::lean_dec(v_m_313_);
                    v___x_316_ = leanh::lean_box(0);
                    v_isShared_317_ = v_isSharedCheck_324_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_318_ = leanh::lean_unsigned_to_nat(0);
                if v_isShared_317_ == 0 {
                    leanh::lean_ctor_set(v___x_316_, 1, v___x_318_);
                    leanh::lean_ctor_set(v___x_316_, 0, v_buckets_314_);
                    v___x_320_ = v___x_316_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_323_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_323_, 0, v_buckets_314_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_323_, 1, v___x_318_);
                    v___x_320_ = v_reuseFailAlloc_323_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_321_ = leanh::lean_box(0);
                v___x_322_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_322_, 0, v___x_320_);
                leanh::lean_ctor_set(v___x_322_, 1, v___x_321_);
                return v___x_322_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_HashMap_keysIter(
    mut v_00_u03b1_326_: *mut leanh::LeanObject,
    mut v_00_u03b2_327_: *mut leanh::LeanObject,
    mut v_inst_328_: *mut leanh::LeanObject,
    mut v_inst_329_: *mut leanh::LeanObject,
    mut v_m_330_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_buckets_331_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_333_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_334_: u8 = 0;
    let mut v___x_335_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_337_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_338_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_339_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_340_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_341_: u8 = 0;
    let mut v_unused_342_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_buckets_331_ = leanh::lean_ctor_get(v_m_330_, 1);
                v_isSharedCheck_341_ = (!leanh::lean_is_exclusive(v_m_330_)) as u8;
                if v_isSharedCheck_341_ == 0 {
                    v_unused_342_ = leanh::lean_ctor_get(v_m_330_, 0);
                    leanh::lean_dec(v_unused_342_);
                    v___x_333_ = v_m_330_;
                    v_isShared_334_ = v_isSharedCheck_341_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_buckets_331_);
                    leanh::lean_dec(v_m_330_);
                    v___x_333_ = leanh::lean_box(0);
                    v_isShared_334_ = v_isSharedCheck_341_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_335_ = leanh::lean_unsigned_to_nat(0);
                if v_isShared_334_ == 0 {
                    leanh::lean_ctor_set(v___x_333_, 1, v___x_335_);
                    leanh::lean_ctor_set(v___x_333_, 0, v_buckets_331_);
                    v___x_337_ = v___x_333_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_340_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_340_, 0, v_buckets_331_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_340_, 1, v___x_335_);
                    v___x_337_ = v_reuseFailAlloc_340_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_338_ = leanh::lean_box(0);
                v___x_339_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_339_, 0, v___x_337_);
                leanh::lean_ctor_set(v___x_339_, 1, v___x_338_);
                return v___x_339_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_HashMap_keysIter___boxed(
    mut v_00_u03b1_343_: *mut leanh::LeanObject,
    mut v_00_u03b2_344_: *mut leanh::LeanObject,
    mut v_inst_345_: *mut leanh::LeanObject,
    mut v_inst_346_: *mut leanh::LeanObject,
    mut v_m_347_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_348_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_348_ = l_Std_HashMap_keysIter(
        v_00_u03b1_343_,
        v_00_u03b2_344_,
        v_inst_345_,
        v_inst_346_,
        v_m_347_,
    );
    leanh::lean_dec_ref(v_inst_346_);
    leanh::lean_dec_ref(v_inst_345_);
    return v_res_348_;
}
pub unsafe fn l_Std_HashMap_valuesIter___redArg(
    mut v_m_349_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_buckets_350_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_352_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_353_: u8 = 0;
    let mut v___x_354_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_356_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_357_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_358_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_359_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_360_: u8 = 0;
    let mut v_unused_361_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_buckets_350_ = leanh::lean_ctor_get(v_m_349_, 1);
                v_isSharedCheck_360_ = (!leanh::lean_is_exclusive(v_m_349_)) as u8;
                if v_isSharedCheck_360_ == 0 {
                    v_unused_361_ = leanh::lean_ctor_get(v_m_349_, 0);
                    leanh::lean_dec(v_unused_361_);
                    v___x_352_ = v_m_349_;
                    v_isShared_353_ = v_isSharedCheck_360_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_buckets_350_);
                    leanh::lean_dec(v_m_349_);
                    v___x_352_ = leanh::lean_box(0);
                    v_isShared_353_ = v_isSharedCheck_360_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_354_ = leanh::lean_unsigned_to_nat(0);
                if v_isShared_353_ == 0 {
                    leanh::lean_ctor_set(v___x_352_, 1, v___x_354_);
                    leanh::lean_ctor_set(v___x_352_, 0, v_buckets_350_);
                    v___x_356_ = v___x_352_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_359_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_359_, 0, v_buckets_350_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_359_, 1, v___x_354_);
                    v___x_356_ = v_reuseFailAlloc_359_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_357_ = leanh::lean_box(0);
                v___x_358_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_358_, 0, v___x_356_);
                leanh::lean_ctor_set(v___x_358_, 1, v___x_357_);
                return v___x_358_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_HashMap_valuesIter(
    mut v_00_u03b1_362_: *mut leanh::LeanObject,
    mut v_00_u03b2_363_: *mut leanh::LeanObject,
    mut v_inst_364_: *mut leanh::LeanObject,
    mut v_inst_365_: *mut leanh::LeanObject,
    mut v_m_366_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_buckets_367_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_369_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_370_: u8 = 0;
    let mut v___x_371_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_373_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_374_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_375_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_376_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_377_: u8 = 0;
    let mut v_unused_378_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_buckets_367_ = leanh::lean_ctor_get(v_m_366_, 1);
                v_isSharedCheck_377_ = (!leanh::lean_is_exclusive(v_m_366_)) as u8;
                if v_isSharedCheck_377_ == 0 {
                    v_unused_378_ = leanh::lean_ctor_get(v_m_366_, 0);
                    leanh::lean_dec(v_unused_378_);
                    v___x_369_ = v_m_366_;
                    v_isShared_370_ = v_isSharedCheck_377_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_buckets_367_);
                    leanh::lean_dec(v_m_366_);
                    v___x_369_ = leanh::lean_box(0);
                    v_isShared_370_ = v_isSharedCheck_377_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_371_ = leanh::lean_unsigned_to_nat(0);
                if v_isShared_370_ == 0 {
                    leanh::lean_ctor_set(v___x_369_, 1, v___x_371_);
                    leanh::lean_ctor_set(v___x_369_, 0, v_buckets_367_);
                    v___x_373_ = v___x_369_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_376_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_376_, 0, v_buckets_367_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_376_, 1, v___x_371_);
                    v___x_373_ = v_reuseFailAlloc_376_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_374_ = leanh::lean_box(0);
                v___x_375_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_375_, 0, v___x_373_);
                leanh::lean_ctor_set(v___x_375_, 1, v___x_374_);
                return v___x_375_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_HashMap_valuesIter___boxed(
    mut v_00_u03b1_379_: *mut leanh::LeanObject,
    mut v_00_u03b2_380_: *mut leanh::LeanObject,
    mut v_inst_381_: *mut leanh::LeanObject,
    mut v_inst_382_: *mut leanh::LeanObject,
    mut v_m_383_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_384_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_384_ = l_Std_HashMap_valuesIter(
        v_00_u03b1_379_,
        v_00_u03b2_380_,
        v_inst_381_,
        v_inst_382_,
        v_m_383_,
    );
    leanh::lean_dec_ref(v_inst_382_);
    leanh::lean_dec_ref(v_inst_381_);
    return v_res_384_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Std_Data_HashMap_Iterator(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Std_Data_DHashMap_Iterator(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Std_Data_HashMap_Basic(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Std_Data_HashMap_Raw(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Iterators_Combinators_FilterMap(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Std_Data_HashMap_Iterator(
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
pub unsafe fn initialize_Std_Data_HashMap_Iterator(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Std_Data_DHashMap_Iterator(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Std_Data_HashMap_Basic(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Std_Data_HashMap_Raw(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Iterators_Combinators_FilterMap(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Std_Data_HashMap_Iterator(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = meta_initialize_Std_Data_HashMap_Iterator(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return initialize_Std_Data_HashMap_Iterator(builtin);
}