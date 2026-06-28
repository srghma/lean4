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
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_alloc_ctor, lean_box, lean_ctor_get, lean_ctor_set,
    lean_dec, lean_dec_ref, lean_inc, lean_io_result_is_error, lean_io_result_mk_ok,
    lean_is_exclusive, lean_unsigned_to_nat,
};
pub unsafe fn l_Std_HashMap_Raw_iter___redArg(mut v_m_193_: *mut LeanObject) -> *mut LeanObject {
    let mut v_buckets_194_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_196_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_197_: u8 = 0;
    let mut v___x_198_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_200_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_201_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_202_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_203_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_204_: u8 = 0;
    let mut v_unused_205_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_buckets_194_ = lean_ctor_get(v_m_193_, 1);
                v_isSharedCheck_204_ = (!lean_is_exclusive(v_m_193_)) as u8;
                if v_isSharedCheck_204_ == 0 {
                    v_unused_205_ = lean_ctor_get(v_m_193_, 0);
                    lean_dec(v_unused_205_);
                    v___x_196_ = v_m_193_;
                    v_isShared_197_ = v_isSharedCheck_204_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_buckets_194_);
                    lean_dec(v_m_193_);
                    v___x_196_ = lean_box(0);
                    v_isShared_197_ = v_isSharedCheck_204_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_198_ = lean_unsigned_to_nat(0);
                if v_isShared_197_ == 0 {
                    lean_ctor_set(v___x_196_, 1, v___x_198_);
                    lean_ctor_set(v___x_196_, 0, v_buckets_194_);
                    v___x_200_ = v___x_196_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_203_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_203_, 0, v_buckets_194_);
                    lean_ctor_set(v_reuseFailAlloc_203_, 1, v___x_198_);
                    v___x_200_ = v_reuseFailAlloc_203_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_201_ = lean_box(0);
                v___x_202_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_202_, 0, v___x_200_);
                lean_ctor_set(v___x_202_, 1, v___x_201_);
                return v___x_202_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_HashMap_Raw_iter(
    mut v_00_u03b1_206_: *mut LeanObject,
    mut v_00_u03b2_207_: *mut LeanObject,
    mut v_m_208_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_buckets_209_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_211_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_212_: u8 = 0;
    let mut v___x_213_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_215_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_216_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_217_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_218_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_219_: u8 = 0;
    let mut v_unused_220_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_buckets_209_ = lean_ctor_get(v_m_208_, 1);
                v_isSharedCheck_219_ = (!lean_is_exclusive(v_m_208_)) as u8;
                if v_isSharedCheck_219_ == 0 {
                    v_unused_220_ = lean_ctor_get(v_m_208_, 0);
                    lean_dec(v_unused_220_);
                    v___x_211_ = v_m_208_;
                    v_isShared_212_ = v_isSharedCheck_219_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_buckets_209_);
                    lean_dec(v_m_208_);
                    v___x_211_ = lean_box(0);
                    v_isShared_212_ = v_isSharedCheck_219_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_213_ = lean_unsigned_to_nat(0);
                if v_isShared_212_ == 0 {
                    lean_ctor_set(v___x_211_, 1, v___x_213_);
                    lean_ctor_set(v___x_211_, 0, v_buckets_209_);
                    v___x_215_ = v___x_211_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_218_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_218_, 0, v_buckets_209_);
                    lean_ctor_set(v_reuseFailAlloc_218_, 1, v___x_213_);
                    v___x_215_ = v_reuseFailAlloc_218_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_216_ = lean_box(0);
                v___x_217_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_217_, 0, v___x_215_);
                lean_ctor_set(v___x_217_, 1, v___x_216_);
                return v___x_217_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_HashMap_Raw_keysIter___redArg(
    mut v_m_221_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_buckets_222_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_224_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_225_: u8 = 0;
    let mut v___x_226_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_228_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_229_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_230_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_231_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_232_: u8 = 0;
    let mut v_unused_233_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_buckets_222_ = lean_ctor_get(v_m_221_, 1);
                v_isSharedCheck_232_ = (!lean_is_exclusive(v_m_221_)) as u8;
                if v_isSharedCheck_232_ == 0 {
                    v_unused_233_ = lean_ctor_get(v_m_221_, 0);
                    lean_dec(v_unused_233_);
                    v___x_224_ = v_m_221_;
                    v_isShared_225_ = v_isSharedCheck_232_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_buckets_222_);
                    lean_dec(v_m_221_);
                    v___x_224_ = lean_box(0);
                    v_isShared_225_ = v_isSharedCheck_232_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_226_ = lean_unsigned_to_nat(0);
                if v_isShared_225_ == 0 {
                    lean_ctor_set(v___x_224_, 1, v___x_226_);
                    lean_ctor_set(v___x_224_, 0, v_buckets_222_);
                    v___x_228_ = v___x_224_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_231_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_231_, 0, v_buckets_222_);
                    lean_ctor_set(v_reuseFailAlloc_231_, 1, v___x_226_);
                    v___x_228_ = v_reuseFailAlloc_231_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_229_ = lean_box(0);
                v___x_230_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_230_, 0, v___x_228_);
                lean_ctor_set(v___x_230_, 1, v___x_229_);
                return v___x_230_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_HashMap_Raw_keysIter(
    mut v_00_u03b1_234_: *mut LeanObject,
    mut v_00_u03b2_235_: *mut LeanObject,
    mut v_m_236_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_buckets_237_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_239_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_240_: u8 = 0;
    let mut v___x_241_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_243_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_244_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_245_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_246_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_247_: u8 = 0;
    let mut v_unused_248_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_buckets_237_ = lean_ctor_get(v_m_236_, 1);
                v_isSharedCheck_247_ = (!lean_is_exclusive(v_m_236_)) as u8;
                if v_isSharedCheck_247_ == 0 {
                    v_unused_248_ = lean_ctor_get(v_m_236_, 0);
                    lean_dec(v_unused_248_);
                    v___x_239_ = v_m_236_;
                    v_isShared_240_ = v_isSharedCheck_247_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_buckets_237_);
                    lean_dec(v_m_236_);
                    v___x_239_ = lean_box(0);
                    v_isShared_240_ = v_isSharedCheck_247_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_241_ = lean_unsigned_to_nat(0);
                if v_isShared_240_ == 0 {
                    lean_ctor_set(v___x_239_, 1, v___x_241_);
                    lean_ctor_set(v___x_239_, 0, v_buckets_237_);
                    v___x_243_ = v___x_239_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_246_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_246_, 0, v_buckets_237_);
                    lean_ctor_set(v_reuseFailAlloc_246_, 1, v___x_241_);
                    v___x_243_ = v_reuseFailAlloc_246_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_244_ = lean_box(0);
                v___x_245_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_245_, 0, v___x_243_);
                lean_ctor_set(v___x_245_, 1, v___x_244_);
                return v___x_245_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_HashMap_Raw_valuesIter___redArg(
    mut v_m_249_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_buckets_250_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_252_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_253_: u8 = 0;
    let mut v___x_254_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_256_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_257_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_258_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_259_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_260_: u8 = 0;
    let mut v_unused_261_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_buckets_250_ = lean_ctor_get(v_m_249_, 1);
                v_isSharedCheck_260_ = (!lean_is_exclusive(v_m_249_)) as u8;
                if v_isSharedCheck_260_ == 0 {
                    v_unused_261_ = lean_ctor_get(v_m_249_, 0);
                    lean_dec(v_unused_261_);
                    v___x_252_ = v_m_249_;
                    v_isShared_253_ = v_isSharedCheck_260_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_buckets_250_);
                    lean_dec(v_m_249_);
                    v___x_252_ = lean_box(0);
                    v_isShared_253_ = v_isSharedCheck_260_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_254_ = lean_unsigned_to_nat(0);
                if v_isShared_253_ == 0 {
                    lean_ctor_set(v___x_252_, 1, v___x_254_);
                    lean_ctor_set(v___x_252_, 0, v_buckets_250_);
                    v___x_256_ = v___x_252_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_259_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_259_, 0, v_buckets_250_);
                    lean_ctor_set(v_reuseFailAlloc_259_, 1, v___x_254_);
                    v___x_256_ = v_reuseFailAlloc_259_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_257_ = lean_box(0);
                v___x_258_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_258_, 0, v___x_256_);
                lean_ctor_set(v___x_258_, 1, v___x_257_);
                return v___x_258_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_HashMap_Raw_valuesIter(
    mut v_00_u03b1_262_: *mut LeanObject,
    mut v_00_u03b2_263_: *mut LeanObject,
    mut v_m_264_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_buckets_265_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_267_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_268_: u8 = 0;
    let mut v___x_269_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_271_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_272_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_273_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_274_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_275_: u8 = 0;
    let mut v_unused_276_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_buckets_265_ = lean_ctor_get(v_m_264_, 1);
                v_isSharedCheck_275_ = (!lean_is_exclusive(v_m_264_)) as u8;
                if v_isSharedCheck_275_ == 0 {
                    v_unused_276_ = lean_ctor_get(v_m_264_, 0);
                    lean_dec(v_unused_276_);
                    v___x_267_ = v_m_264_;
                    v_isShared_268_ = v_isSharedCheck_275_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_buckets_265_);
                    lean_dec(v_m_264_);
                    v___x_267_ = lean_box(0);
                    v_isShared_268_ = v_isSharedCheck_275_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_269_ = lean_unsigned_to_nat(0);
                if v_isShared_268_ == 0 {
                    lean_ctor_set(v___x_267_, 1, v___x_269_);
                    lean_ctor_set(v___x_267_, 0, v_buckets_265_);
                    v___x_271_ = v___x_267_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_274_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_274_, 0, v_buckets_265_);
                    lean_ctor_set(v_reuseFailAlloc_274_, 1, v___x_269_);
                    v___x_271_ = v_reuseFailAlloc_274_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_272_ = lean_box(0);
                v___x_273_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_273_, 0, v___x_271_);
                lean_ctor_set(v___x_273_, 1, v___x_272_);
                return v___x_273_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_HashMap_iter___redArg(mut v_m_277_: *mut LeanObject) -> *mut LeanObject {
    let mut v_buckets_278_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_280_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_281_: u8 = 0;
    let mut v___x_282_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_284_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_285_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_286_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_287_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_288_: u8 = 0;
    let mut v_unused_289_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_buckets_278_ = lean_ctor_get(v_m_277_, 1);
                v_isSharedCheck_288_ = (!lean_is_exclusive(v_m_277_)) as u8;
                if v_isSharedCheck_288_ == 0 {
                    v_unused_289_ = lean_ctor_get(v_m_277_, 0);
                    lean_dec(v_unused_289_);
                    v___x_280_ = v_m_277_;
                    v_isShared_281_ = v_isSharedCheck_288_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_buckets_278_);
                    lean_dec(v_m_277_);
                    v___x_280_ = lean_box(0);
                    v_isShared_281_ = v_isSharedCheck_288_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_282_ = lean_unsigned_to_nat(0);
                if v_isShared_281_ == 0 {
                    lean_ctor_set(v___x_280_, 1, v___x_282_);
                    lean_ctor_set(v___x_280_, 0, v_buckets_278_);
                    v___x_284_ = v___x_280_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_287_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_287_, 0, v_buckets_278_);
                    lean_ctor_set(v_reuseFailAlloc_287_, 1, v___x_282_);
                    v___x_284_ = v_reuseFailAlloc_287_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_285_ = lean_box(0);
                v___x_286_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_286_, 0, v___x_284_);
                lean_ctor_set(v___x_286_, 1, v___x_285_);
                return v___x_286_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_HashMap_iter(
    mut v_00_u03b1_290_: *mut LeanObject,
    mut v_00_u03b2_291_: *mut LeanObject,
    mut v_inst_292_: *mut LeanObject,
    mut v_inst_293_: *mut LeanObject,
    mut v_m_294_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_buckets_295_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_297_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_298_: u8 = 0;
    let mut v___x_299_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_301_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_302_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_303_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_304_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_305_: u8 = 0;
    let mut v_unused_306_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_buckets_295_ = lean_ctor_get(v_m_294_, 1);
                v_isSharedCheck_305_ = (!lean_is_exclusive(v_m_294_)) as u8;
                if v_isSharedCheck_305_ == 0 {
                    v_unused_306_ = lean_ctor_get(v_m_294_, 0);
                    lean_dec(v_unused_306_);
                    v___x_297_ = v_m_294_;
                    v_isShared_298_ = v_isSharedCheck_305_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_buckets_295_);
                    lean_dec(v_m_294_);
                    v___x_297_ = lean_box(0);
                    v_isShared_298_ = v_isSharedCheck_305_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_299_ = lean_unsigned_to_nat(0);
                if v_isShared_298_ == 0 {
                    lean_ctor_set(v___x_297_, 1, v___x_299_);
                    lean_ctor_set(v___x_297_, 0, v_buckets_295_);
                    v___x_301_ = v___x_297_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_304_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_304_, 0, v_buckets_295_);
                    lean_ctor_set(v_reuseFailAlloc_304_, 1, v___x_299_);
                    v___x_301_ = v_reuseFailAlloc_304_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_302_ = lean_box(0);
                v___x_303_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_303_, 0, v___x_301_);
                lean_ctor_set(v___x_303_, 1, v___x_302_);
                return v___x_303_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_HashMap_iter___boxed(
    mut v_00_u03b1_307_: *mut LeanObject,
    mut v_00_u03b2_308_: *mut LeanObject,
    mut v_inst_309_: *mut LeanObject,
    mut v_inst_310_: *mut LeanObject,
    mut v_m_311_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_312_: *mut LeanObject = core::ptr::null_mut();
    v_res_312_ = l_Std_HashMap_iter(
        v_00_u03b1_307_,
        v_00_u03b2_308_,
        v_inst_309_,
        v_inst_310_,
        v_m_311_,
    );
    lean_dec_ref(v_inst_310_);
    lean_dec_ref(v_inst_309_);
    return v_res_312_;
}
pub unsafe fn l_Std_HashMap_keysIter___redArg(mut v_m_313_: *mut LeanObject) -> *mut LeanObject {
    let mut v_buckets_314_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_316_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_317_: u8 = 0;
    let mut v___x_318_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_320_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_321_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_322_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_323_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_324_: u8 = 0;
    let mut v_unused_325_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_buckets_314_ = lean_ctor_get(v_m_313_, 1);
                v_isSharedCheck_324_ = (!lean_is_exclusive(v_m_313_)) as u8;
                if v_isSharedCheck_324_ == 0 {
                    v_unused_325_ = lean_ctor_get(v_m_313_, 0);
                    lean_dec(v_unused_325_);
                    v___x_316_ = v_m_313_;
                    v_isShared_317_ = v_isSharedCheck_324_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_buckets_314_);
                    lean_dec(v_m_313_);
                    v___x_316_ = lean_box(0);
                    v_isShared_317_ = v_isSharedCheck_324_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_318_ = lean_unsigned_to_nat(0);
                if v_isShared_317_ == 0 {
                    lean_ctor_set(v___x_316_, 1, v___x_318_);
                    lean_ctor_set(v___x_316_, 0, v_buckets_314_);
                    v___x_320_ = v___x_316_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_323_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_323_, 0, v_buckets_314_);
                    lean_ctor_set(v_reuseFailAlloc_323_, 1, v___x_318_);
                    v___x_320_ = v_reuseFailAlloc_323_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_321_ = lean_box(0);
                v___x_322_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_322_, 0, v___x_320_);
                lean_ctor_set(v___x_322_, 1, v___x_321_);
                return v___x_322_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_HashMap_keysIter(
    mut v_00_u03b1_326_: *mut LeanObject,
    mut v_00_u03b2_327_: *mut LeanObject,
    mut v_inst_328_: *mut LeanObject,
    mut v_inst_329_: *mut LeanObject,
    mut v_m_330_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_buckets_331_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_333_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_334_: u8 = 0;
    let mut v___x_335_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_337_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_338_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_339_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_340_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_341_: u8 = 0;
    let mut v_unused_342_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_buckets_331_ = lean_ctor_get(v_m_330_, 1);
                v_isSharedCheck_341_ = (!lean_is_exclusive(v_m_330_)) as u8;
                if v_isSharedCheck_341_ == 0 {
                    v_unused_342_ = lean_ctor_get(v_m_330_, 0);
                    lean_dec(v_unused_342_);
                    v___x_333_ = v_m_330_;
                    v_isShared_334_ = v_isSharedCheck_341_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_buckets_331_);
                    lean_dec(v_m_330_);
                    v___x_333_ = lean_box(0);
                    v_isShared_334_ = v_isSharedCheck_341_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_335_ = lean_unsigned_to_nat(0);
                if v_isShared_334_ == 0 {
                    lean_ctor_set(v___x_333_, 1, v___x_335_);
                    lean_ctor_set(v___x_333_, 0, v_buckets_331_);
                    v___x_337_ = v___x_333_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_340_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_340_, 0, v_buckets_331_);
                    lean_ctor_set(v_reuseFailAlloc_340_, 1, v___x_335_);
                    v___x_337_ = v_reuseFailAlloc_340_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_338_ = lean_box(0);
                v___x_339_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_339_, 0, v___x_337_);
                lean_ctor_set(v___x_339_, 1, v___x_338_);
                return v___x_339_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_HashMap_keysIter___boxed(
    mut v_00_u03b1_343_: *mut LeanObject,
    mut v_00_u03b2_344_: *mut LeanObject,
    mut v_inst_345_: *mut LeanObject,
    mut v_inst_346_: *mut LeanObject,
    mut v_m_347_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_348_: *mut LeanObject = core::ptr::null_mut();
    v_res_348_ = l_Std_HashMap_keysIter(
        v_00_u03b1_343_,
        v_00_u03b2_344_,
        v_inst_345_,
        v_inst_346_,
        v_m_347_,
    );
    lean_dec_ref(v_inst_346_);
    lean_dec_ref(v_inst_345_);
    return v_res_348_;
}
pub unsafe fn l_Std_HashMap_valuesIter___redArg(mut v_m_349_: *mut LeanObject) -> *mut LeanObject {
    let mut v_buckets_350_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_352_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_353_: u8 = 0;
    let mut v___x_354_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_356_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_357_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_358_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_359_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_360_: u8 = 0;
    let mut v_unused_361_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_buckets_350_ = lean_ctor_get(v_m_349_, 1);
                v_isSharedCheck_360_ = (!lean_is_exclusive(v_m_349_)) as u8;
                if v_isSharedCheck_360_ == 0 {
                    v_unused_361_ = lean_ctor_get(v_m_349_, 0);
                    lean_dec(v_unused_361_);
                    v___x_352_ = v_m_349_;
                    v_isShared_353_ = v_isSharedCheck_360_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_buckets_350_);
                    lean_dec(v_m_349_);
                    v___x_352_ = lean_box(0);
                    v_isShared_353_ = v_isSharedCheck_360_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_354_ = lean_unsigned_to_nat(0);
                if v_isShared_353_ == 0 {
                    lean_ctor_set(v___x_352_, 1, v___x_354_);
                    lean_ctor_set(v___x_352_, 0, v_buckets_350_);
                    v___x_356_ = v___x_352_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_359_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_359_, 0, v_buckets_350_);
                    lean_ctor_set(v_reuseFailAlloc_359_, 1, v___x_354_);
                    v___x_356_ = v_reuseFailAlloc_359_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_357_ = lean_box(0);
                v___x_358_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_358_, 0, v___x_356_);
                lean_ctor_set(v___x_358_, 1, v___x_357_);
                return v___x_358_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_HashMap_valuesIter(
    mut v_00_u03b1_362_: *mut LeanObject,
    mut v_00_u03b2_363_: *mut LeanObject,
    mut v_inst_364_: *mut LeanObject,
    mut v_inst_365_: *mut LeanObject,
    mut v_m_366_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_buckets_367_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_369_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_370_: u8 = 0;
    let mut v___x_371_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_373_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_374_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_375_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_376_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_377_: u8 = 0;
    let mut v_unused_378_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_buckets_367_ = lean_ctor_get(v_m_366_, 1);
                v_isSharedCheck_377_ = (!lean_is_exclusive(v_m_366_)) as u8;
                if v_isSharedCheck_377_ == 0 {
                    v_unused_378_ = lean_ctor_get(v_m_366_, 0);
                    lean_dec(v_unused_378_);
                    v___x_369_ = v_m_366_;
                    v_isShared_370_ = v_isSharedCheck_377_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_buckets_367_);
                    lean_dec(v_m_366_);
                    v___x_369_ = lean_box(0);
                    v_isShared_370_ = v_isSharedCheck_377_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_371_ = lean_unsigned_to_nat(0);
                if v_isShared_370_ == 0 {
                    lean_ctor_set(v___x_369_, 1, v___x_371_);
                    lean_ctor_set(v___x_369_, 0, v_buckets_367_);
                    v___x_373_ = v___x_369_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_376_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_376_, 0, v_buckets_367_);
                    lean_ctor_set(v_reuseFailAlloc_376_, 1, v___x_371_);
                    v___x_373_ = v_reuseFailAlloc_376_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_374_ = lean_box(0);
                v___x_375_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_375_, 0, v___x_373_);
                lean_ctor_set(v___x_375_, 1, v___x_374_);
                return v___x_375_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_HashMap_valuesIter___boxed(
    mut v_00_u03b1_379_: *mut LeanObject,
    mut v_00_u03b2_380_: *mut LeanObject,
    mut v_inst_381_: *mut LeanObject,
    mut v_inst_382_: *mut LeanObject,
    mut v_m_383_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_384_: *mut LeanObject = core::ptr::null_mut();
    v_res_384_ = l_Std_HashMap_valuesIter(
        v_00_u03b1_379_,
        v_00_u03b2_380_,
        v_inst_381_,
        v_inst_382_,
        v_m_383_,
    );
    lean_dec_ref(v_inst_382_);
    lean_dec_ref(v_inst_381_);
    return v_res_384_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Std_Data_HashMap_Iterator(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Std_Data_DHashMap_Iterator(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Std_Data_HashMap_Basic(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Std_Data_HashMap_Raw(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Iterators_Combinators_FilterMap(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Std_Data_HashMap_Iterator(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_meta_initialized = true;
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Std_Data_HashMap_Iterator(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Std_Data_DHashMap_Iterator(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Std_Data_HashMap_Basic(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Std_Data_HashMap_Raw(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Data_Iterators_Combinators_FilterMap(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Std_Data_HashMap_Iterator(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Std_Data_HashMap_Iterator(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Std_Data_HashMap_Iterator(builtin);
}
