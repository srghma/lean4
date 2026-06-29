// Lean compiler output
// Module: Std.Data.DHashMap.Iterator
// Imports: Std.Data.Iterators.Producers.Array Init.Data.Iterators.Combinators.FlatMap Std.Data.DHashMap.Basic Std.Data.DHashMap.Internal.AssocList.Iterator Init.Data.Iterators.Combinators.FilterMap
use crate::r#gen::Init::Data::Iterators::Combinators::FilterMap::{
    initialize_Init_Data_Iterators_Combinators_FilterMap,
    runtime_initialize_Init_Data_Iterators_Combinators_FilterMap,
};
use crate::r#gen::Init::Data::Iterators::Combinators::FlatMap::{
    initialize_Init_Data_Iterators_Combinators_FlatMap,
    runtime_initialize_Init_Data_Iterators_Combinators_FlatMap,
};
use crate::r#gen::Std::Data::DHashMap::Basic::{
    initialize_Std_Data_DHashMap_Basic, runtime_initialize_Std_Data_DHashMap_Basic,
};
use crate::r#gen::Std::Data::DHashMap::Internal::AssocList::Iterator::{
    initialize_Std_Data_DHashMap_Internal_AssocList_Iterator,
    runtime_initialize_Std_Data_DHashMap_Internal_AssocList_Iterator,
};
use crate::r#gen::Std::Data::Iterators::Producers::Array::{
    initialize_Std_Data_Iterators_Producers_Array,
    runtime_initialize_Std_Data_Iterators_Producers_Array,
};
pub unsafe fn l_Std_DHashMap_Raw_iter___redArg(
    mut v_m_193_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_buckets_194_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_196_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_197_: u8 = 0;
    let mut v___x_198_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_200_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_201_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_202_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_203_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_204_: u8 = 0;
    let mut v_unused_205_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_buckets_194_ = crate::leanh::lean_ctor_get(v_m_193_, 1);
                v_isSharedCheck_204_ = (!crate::leanh::lean_is_exclusive(v_m_193_)) as u8;
                if v_isSharedCheck_204_ == 0 {
                    v_unused_205_ = crate::leanh::lean_ctor_get(v_m_193_, 0);
                    crate::leanh::lean_dec(v_unused_205_);
                    v___x_196_ = v_m_193_;
                    v_isShared_197_ = v_isSharedCheck_204_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_buckets_194_);
                    crate::leanh::lean_dec(v_m_193_);
                    v___x_196_ = crate::leanh::lean_box(0);
                    v_isShared_197_ = v_isSharedCheck_204_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_198_ = crate::leanh::lean_unsigned_to_nat(0);
                if v_isShared_197_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_196_, 1, v___x_198_);
                    crate::leanh::lean_ctor_set(v___x_196_, 0, v_buckets_194_);
                    v___x_200_ = v___x_196_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_203_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_203_, 0, v_buckets_194_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_203_, 1, v___x_198_);
                    v___x_200_ = v_reuseFailAlloc_203_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_201_ = crate::leanh::lean_box(0);
                v___x_202_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_202_, 0, v___x_200_);
                crate::leanh::lean_ctor_set(v___x_202_, 1, v___x_201_);
                return v___x_202_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Raw_iter(
    mut v_00_u03b1_206_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_207_: *mut crate::leanh::LeanObject,
    mut v_m_208_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_buckets_209_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_211_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_212_: u8 = 0;
    let mut v___x_213_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_215_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_216_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_217_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_218_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_219_: u8 = 0;
    let mut v_unused_220_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_buckets_209_ = crate::leanh::lean_ctor_get(v_m_208_, 1);
                v_isSharedCheck_219_ = (!crate::leanh::lean_is_exclusive(v_m_208_)) as u8;
                if v_isSharedCheck_219_ == 0 {
                    v_unused_220_ = crate::leanh::lean_ctor_get(v_m_208_, 0);
                    crate::leanh::lean_dec(v_unused_220_);
                    v___x_211_ = v_m_208_;
                    v_isShared_212_ = v_isSharedCheck_219_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_buckets_209_);
                    crate::leanh::lean_dec(v_m_208_);
                    v___x_211_ = crate::leanh::lean_box(0);
                    v_isShared_212_ = v_isSharedCheck_219_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_213_ = crate::leanh::lean_unsigned_to_nat(0);
                if v_isShared_212_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_211_, 1, v___x_213_);
                    crate::leanh::lean_ctor_set(v___x_211_, 0, v_buckets_209_);
                    v___x_215_ = v___x_211_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_218_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_218_, 0, v_buckets_209_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_218_, 1, v___x_213_);
                    v___x_215_ = v_reuseFailAlloc_218_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_216_ = crate::leanh::lean_box(0);
                v___x_217_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_217_, 0, v___x_215_);
                crate::leanh::lean_ctor_set(v___x_217_, 1, v___x_216_);
                return v___x_217_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Raw_keysIter___redArg(
    mut v_m_221_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_buckets_222_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_224_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_225_: u8 = 0;
    let mut v___x_226_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_228_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_229_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_230_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_231_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_232_: u8 = 0;
    let mut v_unused_233_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_buckets_222_ = crate::leanh::lean_ctor_get(v_m_221_, 1);
                v_isSharedCheck_232_ = (!crate::leanh::lean_is_exclusive(v_m_221_)) as u8;
                if v_isSharedCheck_232_ == 0 {
                    v_unused_233_ = crate::leanh::lean_ctor_get(v_m_221_, 0);
                    crate::leanh::lean_dec(v_unused_233_);
                    v___x_224_ = v_m_221_;
                    v_isShared_225_ = v_isSharedCheck_232_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_buckets_222_);
                    crate::leanh::lean_dec(v_m_221_);
                    v___x_224_ = crate::leanh::lean_box(0);
                    v_isShared_225_ = v_isSharedCheck_232_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_226_ = crate::leanh::lean_unsigned_to_nat(0);
                if v_isShared_225_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_224_, 1, v___x_226_);
                    crate::leanh::lean_ctor_set(v___x_224_, 0, v_buckets_222_);
                    v___x_228_ = v___x_224_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_231_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_231_, 0, v_buckets_222_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_231_, 1, v___x_226_);
                    v___x_228_ = v_reuseFailAlloc_231_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_229_ = crate::leanh::lean_box(0);
                v___x_230_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_230_, 0, v___x_228_);
                crate::leanh::lean_ctor_set(v___x_230_, 1, v___x_229_);
                return v___x_230_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Raw_keysIter(
    mut v_00_u03b1_234_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_235_: *mut crate::leanh::LeanObject,
    mut v_m_236_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_buckets_237_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_239_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_240_: u8 = 0;
    let mut v___x_241_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_243_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_244_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_245_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_246_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_247_: u8 = 0;
    let mut v_unused_248_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_buckets_237_ = crate::leanh::lean_ctor_get(v_m_236_, 1);
                v_isSharedCheck_247_ = (!crate::leanh::lean_is_exclusive(v_m_236_)) as u8;
                if v_isSharedCheck_247_ == 0 {
                    v_unused_248_ = crate::leanh::lean_ctor_get(v_m_236_, 0);
                    crate::leanh::lean_dec(v_unused_248_);
                    v___x_239_ = v_m_236_;
                    v_isShared_240_ = v_isSharedCheck_247_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_buckets_237_);
                    crate::leanh::lean_dec(v_m_236_);
                    v___x_239_ = crate::leanh::lean_box(0);
                    v_isShared_240_ = v_isSharedCheck_247_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_241_ = crate::leanh::lean_unsigned_to_nat(0);
                if v_isShared_240_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_239_, 1, v___x_241_);
                    crate::leanh::lean_ctor_set(v___x_239_, 0, v_buckets_237_);
                    v___x_243_ = v___x_239_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_246_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_246_, 0, v_buckets_237_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_246_, 1, v___x_241_);
                    v___x_243_ = v_reuseFailAlloc_246_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_244_ = crate::leanh::lean_box(0);
                v___x_245_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_245_, 0, v___x_243_);
                crate::leanh::lean_ctor_set(v___x_245_, 1, v___x_244_);
                return v___x_245_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Raw_valuesIter___redArg(
    mut v_m_249_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_buckets_250_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_252_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_253_: u8 = 0;
    let mut v___x_254_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_256_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_257_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_258_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_259_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_260_: u8 = 0;
    let mut v_unused_261_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_buckets_250_ = crate::leanh::lean_ctor_get(v_m_249_, 1);
                v_isSharedCheck_260_ = (!crate::leanh::lean_is_exclusive(v_m_249_)) as u8;
                if v_isSharedCheck_260_ == 0 {
                    v_unused_261_ = crate::leanh::lean_ctor_get(v_m_249_, 0);
                    crate::leanh::lean_dec(v_unused_261_);
                    v___x_252_ = v_m_249_;
                    v_isShared_253_ = v_isSharedCheck_260_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_buckets_250_);
                    crate::leanh::lean_dec(v_m_249_);
                    v___x_252_ = crate::leanh::lean_box(0);
                    v_isShared_253_ = v_isSharedCheck_260_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_254_ = crate::leanh::lean_unsigned_to_nat(0);
                if v_isShared_253_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_252_, 1, v___x_254_);
                    crate::leanh::lean_ctor_set(v___x_252_, 0, v_buckets_250_);
                    v___x_256_ = v___x_252_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_259_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_259_, 0, v_buckets_250_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_259_, 1, v___x_254_);
                    v___x_256_ = v_reuseFailAlloc_259_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_257_ = crate::leanh::lean_box(0);
                v___x_258_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_258_, 0, v___x_256_);
                crate::leanh::lean_ctor_set(v___x_258_, 1, v___x_257_);
                return v___x_258_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Raw_valuesIter(
    mut v_00_u03b1_262_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_263_: *mut crate::leanh::LeanObject,
    mut v_m_264_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_buckets_265_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_267_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_268_: u8 = 0;
    let mut v___x_269_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_271_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_272_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_273_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_274_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_275_: u8 = 0;
    let mut v_unused_276_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_buckets_265_ = crate::leanh::lean_ctor_get(v_m_264_, 1);
                v_isSharedCheck_275_ = (!crate::leanh::lean_is_exclusive(v_m_264_)) as u8;
                if v_isSharedCheck_275_ == 0 {
                    v_unused_276_ = crate::leanh::lean_ctor_get(v_m_264_, 0);
                    crate::leanh::lean_dec(v_unused_276_);
                    v___x_267_ = v_m_264_;
                    v_isShared_268_ = v_isSharedCheck_275_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_buckets_265_);
                    crate::leanh::lean_dec(v_m_264_);
                    v___x_267_ = crate::leanh::lean_box(0);
                    v_isShared_268_ = v_isSharedCheck_275_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_269_ = crate::leanh::lean_unsigned_to_nat(0);
                if v_isShared_268_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_267_, 1, v___x_269_);
                    crate::leanh::lean_ctor_set(v___x_267_, 0, v_buckets_265_);
                    v___x_271_ = v___x_267_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_274_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_274_, 0, v_buckets_265_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_274_, 1, v___x_269_);
                    v___x_271_ = v_reuseFailAlloc_274_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_272_ = crate::leanh::lean_box(0);
                v___x_273_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_273_, 0, v___x_271_);
                crate::leanh::lean_ctor_set(v___x_273_, 1, v___x_272_);
                return v___x_273_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_iter___redArg(
    mut v_m_277_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_buckets_278_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_280_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_281_: u8 = 0;
    let mut v___x_282_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_284_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_285_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_286_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_287_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_288_: u8 = 0;
    let mut v_unused_289_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_buckets_278_ = crate::leanh::lean_ctor_get(v_m_277_, 1);
                v_isSharedCheck_288_ = (!crate::leanh::lean_is_exclusive(v_m_277_)) as u8;
                if v_isSharedCheck_288_ == 0 {
                    v_unused_289_ = crate::leanh::lean_ctor_get(v_m_277_, 0);
                    crate::leanh::lean_dec(v_unused_289_);
                    v___x_280_ = v_m_277_;
                    v_isShared_281_ = v_isSharedCheck_288_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_buckets_278_);
                    crate::leanh::lean_dec(v_m_277_);
                    v___x_280_ = crate::leanh::lean_box(0);
                    v_isShared_281_ = v_isSharedCheck_288_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_282_ = crate::leanh::lean_unsigned_to_nat(0);
                if v_isShared_281_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_280_, 1, v___x_282_);
                    crate::leanh::lean_ctor_set(v___x_280_, 0, v_buckets_278_);
                    v___x_284_ = v___x_280_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_287_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_287_, 0, v_buckets_278_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_287_, 1, v___x_282_);
                    v___x_284_ = v_reuseFailAlloc_287_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_285_ = crate::leanh::lean_box(0);
                v___x_286_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_286_, 0, v___x_284_);
                crate::leanh::lean_ctor_set(v___x_286_, 1, v___x_285_);
                return v___x_286_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_iter(
    mut v_00_u03b1_290_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_291_: *mut crate::leanh::LeanObject,
    mut v_inst_292_: *mut crate::leanh::LeanObject,
    mut v_inst_293_: *mut crate::leanh::LeanObject,
    mut v_m_294_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_buckets_295_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_297_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_298_: u8 = 0;
    let mut v___x_299_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_301_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_302_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_303_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_304_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_305_: u8 = 0;
    let mut v_unused_306_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_buckets_295_ = crate::leanh::lean_ctor_get(v_m_294_, 1);
                v_isSharedCheck_305_ = (!crate::leanh::lean_is_exclusive(v_m_294_)) as u8;
                if v_isSharedCheck_305_ == 0 {
                    v_unused_306_ = crate::leanh::lean_ctor_get(v_m_294_, 0);
                    crate::leanh::lean_dec(v_unused_306_);
                    v___x_297_ = v_m_294_;
                    v_isShared_298_ = v_isSharedCheck_305_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_buckets_295_);
                    crate::leanh::lean_dec(v_m_294_);
                    v___x_297_ = crate::leanh::lean_box(0);
                    v_isShared_298_ = v_isSharedCheck_305_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_299_ = crate::leanh::lean_unsigned_to_nat(0);
                if v_isShared_298_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_297_, 1, v___x_299_);
                    crate::leanh::lean_ctor_set(v___x_297_, 0, v_buckets_295_);
                    v___x_301_ = v___x_297_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_304_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_304_, 0, v_buckets_295_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_304_, 1, v___x_299_);
                    v___x_301_ = v_reuseFailAlloc_304_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_302_ = crate::leanh::lean_box(0);
                v___x_303_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_303_, 0, v___x_301_);
                crate::leanh::lean_ctor_set(v___x_303_, 1, v___x_302_);
                return v___x_303_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_iter___boxed(
    mut v_00_u03b1_307_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_308_: *mut crate::leanh::LeanObject,
    mut v_inst_309_: *mut crate::leanh::LeanObject,
    mut v_inst_310_: *mut crate::leanh::LeanObject,
    mut v_m_311_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_312_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_312_ = l_Std_DHashMap_iter(
        v_00_u03b1_307_,
        v_00_u03b2_308_,
        v_inst_309_,
        v_inst_310_,
        v_m_311_,
    );
    crate::leanh::lean_dec_ref(v_inst_310_);
    crate::leanh::lean_dec_ref(v_inst_309_);
    return v_res_312_;
}
pub unsafe fn l_Std_DHashMap_keysIter___redArg(
    mut v_m_313_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_buckets_314_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_316_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_317_: u8 = 0;
    let mut v___x_318_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_320_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_321_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_322_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_323_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_324_: u8 = 0;
    let mut v_unused_325_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_buckets_314_ = crate::leanh::lean_ctor_get(v_m_313_, 1);
                v_isSharedCheck_324_ = (!crate::leanh::lean_is_exclusive(v_m_313_)) as u8;
                if v_isSharedCheck_324_ == 0 {
                    v_unused_325_ = crate::leanh::lean_ctor_get(v_m_313_, 0);
                    crate::leanh::lean_dec(v_unused_325_);
                    v___x_316_ = v_m_313_;
                    v_isShared_317_ = v_isSharedCheck_324_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_buckets_314_);
                    crate::leanh::lean_dec(v_m_313_);
                    v___x_316_ = crate::leanh::lean_box(0);
                    v_isShared_317_ = v_isSharedCheck_324_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_318_ = crate::leanh::lean_unsigned_to_nat(0);
                if v_isShared_317_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_316_, 1, v___x_318_);
                    crate::leanh::lean_ctor_set(v___x_316_, 0, v_buckets_314_);
                    v___x_320_ = v___x_316_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_323_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_323_, 0, v_buckets_314_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_323_, 1, v___x_318_);
                    v___x_320_ = v_reuseFailAlloc_323_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_321_ = crate::leanh::lean_box(0);
                v___x_322_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_322_, 0, v___x_320_);
                crate::leanh::lean_ctor_set(v___x_322_, 1, v___x_321_);
                return v___x_322_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_keysIter(
    mut v_00_u03b1_326_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_327_: *mut crate::leanh::LeanObject,
    mut v_inst_328_: *mut crate::leanh::LeanObject,
    mut v_inst_329_: *mut crate::leanh::LeanObject,
    mut v_m_330_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_buckets_331_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_333_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_334_: u8 = 0;
    let mut v___x_335_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_337_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_338_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_339_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_340_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_341_: u8 = 0;
    let mut v_unused_342_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_buckets_331_ = crate::leanh::lean_ctor_get(v_m_330_, 1);
                v_isSharedCheck_341_ = (!crate::leanh::lean_is_exclusive(v_m_330_)) as u8;
                if v_isSharedCheck_341_ == 0 {
                    v_unused_342_ = crate::leanh::lean_ctor_get(v_m_330_, 0);
                    crate::leanh::lean_dec(v_unused_342_);
                    v___x_333_ = v_m_330_;
                    v_isShared_334_ = v_isSharedCheck_341_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_buckets_331_);
                    crate::leanh::lean_dec(v_m_330_);
                    v___x_333_ = crate::leanh::lean_box(0);
                    v_isShared_334_ = v_isSharedCheck_341_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_335_ = crate::leanh::lean_unsigned_to_nat(0);
                if v_isShared_334_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_333_, 1, v___x_335_);
                    crate::leanh::lean_ctor_set(v___x_333_, 0, v_buckets_331_);
                    v___x_337_ = v___x_333_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_340_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_340_, 0, v_buckets_331_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_340_, 1, v___x_335_);
                    v___x_337_ = v_reuseFailAlloc_340_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_338_ = crate::leanh::lean_box(0);
                v___x_339_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_339_, 0, v___x_337_);
                crate::leanh::lean_ctor_set(v___x_339_, 1, v___x_338_);
                return v___x_339_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_keysIter___boxed(
    mut v_00_u03b1_343_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_344_: *mut crate::leanh::LeanObject,
    mut v_inst_345_: *mut crate::leanh::LeanObject,
    mut v_inst_346_: *mut crate::leanh::LeanObject,
    mut v_m_347_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_348_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_348_ = l_Std_DHashMap_keysIter(
        v_00_u03b1_343_,
        v_00_u03b2_344_,
        v_inst_345_,
        v_inst_346_,
        v_m_347_,
    );
    crate::leanh::lean_dec_ref(v_inst_346_);
    crate::leanh::lean_dec_ref(v_inst_345_);
    return v_res_348_;
}
pub unsafe fn l_Std_DHashMap_valuesIter___redArg(
    mut v_m_349_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_buckets_350_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_352_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_353_: u8 = 0;
    let mut v___x_354_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_356_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_357_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_358_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_359_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_360_: u8 = 0;
    let mut v_unused_361_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_buckets_350_ = crate::leanh::lean_ctor_get(v_m_349_, 1);
                v_isSharedCheck_360_ = (!crate::leanh::lean_is_exclusive(v_m_349_)) as u8;
                if v_isSharedCheck_360_ == 0 {
                    v_unused_361_ = crate::leanh::lean_ctor_get(v_m_349_, 0);
                    crate::leanh::lean_dec(v_unused_361_);
                    v___x_352_ = v_m_349_;
                    v_isShared_353_ = v_isSharedCheck_360_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_buckets_350_);
                    crate::leanh::lean_dec(v_m_349_);
                    v___x_352_ = crate::leanh::lean_box(0);
                    v_isShared_353_ = v_isSharedCheck_360_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_354_ = crate::leanh::lean_unsigned_to_nat(0);
                if v_isShared_353_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_352_, 1, v___x_354_);
                    crate::leanh::lean_ctor_set(v___x_352_, 0, v_buckets_350_);
                    v___x_356_ = v___x_352_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_359_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_359_, 0, v_buckets_350_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_359_, 1, v___x_354_);
                    v___x_356_ = v_reuseFailAlloc_359_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_357_ = crate::leanh::lean_box(0);
                v___x_358_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_358_, 0, v___x_356_);
                crate::leanh::lean_ctor_set(v___x_358_, 1, v___x_357_);
                return v___x_358_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_valuesIter(
    mut v_00_u03b1_362_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_363_: *mut crate::leanh::LeanObject,
    mut v_inst_364_: *mut crate::leanh::LeanObject,
    mut v_inst_365_: *mut crate::leanh::LeanObject,
    mut v_m_366_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_buckets_367_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_369_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_370_: u8 = 0;
    let mut v___x_371_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_373_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_374_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_375_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_376_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_377_: u8 = 0;
    let mut v_unused_378_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_buckets_367_ = crate::leanh::lean_ctor_get(v_m_366_, 1);
                v_isSharedCheck_377_ = (!crate::leanh::lean_is_exclusive(v_m_366_)) as u8;
                if v_isSharedCheck_377_ == 0 {
                    v_unused_378_ = crate::leanh::lean_ctor_get(v_m_366_, 0);
                    crate::leanh::lean_dec(v_unused_378_);
                    v___x_369_ = v_m_366_;
                    v_isShared_370_ = v_isSharedCheck_377_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_buckets_367_);
                    crate::leanh::lean_dec(v_m_366_);
                    v___x_369_ = crate::leanh::lean_box(0);
                    v_isShared_370_ = v_isSharedCheck_377_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_371_ = crate::leanh::lean_unsigned_to_nat(0);
                if v_isShared_370_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_369_, 1, v___x_371_);
                    crate::leanh::lean_ctor_set(v___x_369_, 0, v_buckets_367_);
                    v___x_373_ = v___x_369_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_376_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_376_, 0, v_buckets_367_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_376_, 1, v___x_371_);
                    v___x_373_ = v_reuseFailAlloc_376_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_374_ = crate::leanh::lean_box(0);
                v___x_375_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_375_, 0, v___x_373_);
                crate::leanh::lean_ctor_set(v___x_375_, 1, v___x_374_);
                return v___x_375_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_valuesIter___boxed(
    mut v_00_u03b1_379_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_380_: *mut crate::leanh::LeanObject,
    mut v_inst_381_: *mut crate::leanh::LeanObject,
    mut v_inst_382_: *mut crate::leanh::LeanObject,
    mut v_m_383_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_384_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_384_ = l_Std_DHashMap_valuesIter(
        v_00_u03b1_379_,
        v_00_u03b2_380_,
        v_inst_381_,
        v_inst_382_,
        v_m_383_,
    );
    crate::leanh::lean_dec_ref(v_inst_382_);
    crate::leanh::lean_dec_ref(v_inst_381_);
    return v_res_384_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Std_Data_DHashMap_Iterator(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Std_Data_Iterators_Producers_Array(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Iterators_Combinators_FlatMap(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Std_Data_DHashMap_Basic(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Std_Data_DHashMap_Internal_AssocList_Iterator(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Iterators_Combinators_FilterMap(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Std_Data_DHashMap_Iterator(
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
pub unsafe fn initialize_Std_Data_DHashMap_Iterator(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Std_Data_Iterators_Producers_Array(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Iterators_Combinators_FlatMap(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Std_Data_DHashMap_Basic(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Std_Data_DHashMap_Internal_AssocList_Iterator(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Iterators_Combinators_FilterMap(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Std_Data_DHashMap_Iterator(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Std_Data_DHashMap_Iterator(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Std_Data_DHashMap_Iterator(builtin);
}
