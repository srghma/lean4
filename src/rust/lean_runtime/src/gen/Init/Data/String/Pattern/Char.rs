// Lean compiler output
// Module: Init.Data.String.Pattern.Char
// Imports: Init.Data.String.Pattern.Pred
use crate::r#gen::Init::Data::String::FindPos::l_String_Slice_posLE;
use crate::r#gen::Init::Data::String::Pattern::Pred::{
    initialize_Init_Data_String_Pattern_Pred, runtime_initialize_Init_Data_String_Pattern_Pred,
};
use crate::lean_imports_rs::Init::Data::String::Basic::{
    lean_string_utf8_get_fast, lean_string_utf8_next_fast,
};
use crate::lean_imports_rs::Init::Prelude::{
    lean_nat_add, lean_nat_dec_eq, lean_nat_sub, lean_uint32_dec_eq,
};
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_alloc_closure, lean_alloc_ctor, lean_box,
    lean_box_uint32, lean_closure_set, lean_ctor_get, lean_ctor_set, lean_dec, lean_dec_ref,
    lean_io_result_is_error, lean_io_result_mk_ok, lean_unbox_uint32, lean_unsigned_to_nat,
};
pub static l_String_Slice_Pattern_Char_instToForwardSearcherCharDefaultForwardSearcherForallBoolBeq___closed__0_value: LeanClosureObject<0> = LeanClosureObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_String_Slice_Pattern_Char_instToForwardSearcherCharDefaultForwardSearcherForallBoolBeq___lam__0___boxed as *const core::ffi::c_void, m_arity: 1, m_num_fixed: 0, m_objs: [] };
static mut l_String_Slice_Pattern_Char_instToForwardSearcherCharDefaultForwardSearcherForallBoolBeq___closed__0: *mut LeanObject = core::ptr::addr_of!(l_String_Slice_Pattern_Char_instToForwardSearcherCharDefaultForwardSearcherForallBoolBeq___closed__0_value) as *mut LeanObject;
pub static l_String_Slice_Pattern_Char_instToBackwardSearcherCharDefaultBackwardSearcherForallBoolBeq___closed__0_value: LeanClosureObject<0> = LeanClosureObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_String_Slice_Pattern_Char_instToBackwardSearcherCharDefaultBackwardSearcherForallBoolBeq___lam__0___boxed as *const core::ffi::c_void, m_arity: 1, m_num_fixed: 0, m_objs: [] };
static mut l_String_Slice_Pattern_Char_instToBackwardSearcherCharDefaultBackwardSearcherForallBoolBeq___closed__0: *mut LeanObject = core::ptr::addr_of!(l_String_Slice_Pattern_Char_instToBackwardSearcherCharDefaultBackwardSearcherForallBoolBeq___closed__0_value) as *mut LeanObject;
pub unsafe fn l_String_Slice_Pattern_Char_instForwardPatternChar___lam__0(
    mut v_c_157_: u32,
    mut v_s_158_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_str_159_: *mut LeanObject = core::ptr::null_mut();
    let mut v_startInclusive_160_: *mut LeanObject = core::ptr::null_mut();
    let mut v_endExclusive_161_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_162_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_163_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_164_: u8 = 0;
    v_str_159_ = lean_ctor_get(v_s_158_, 0);
    v_startInclusive_160_ = lean_ctor_get(v_s_158_, 1);
    v_endExclusive_161_ = lean_ctor_get(v_s_158_, 2);
    v___x_162_ = lean_unsigned_to_nat(0);
    v___x_163_ = lean_nat_sub(v_endExclusive_161_, v_startInclusive_160_);
    v___x_164_ = lean_nat_dec_eq(v___x_162_, v___x_163_);
    lean_dec(v___x_163_);
    if v___x_164_ == 0 {
        let mut v___x_165_: u32 = 0;
        let mut v___x_166_: u8 = 0;
        v___x_165_ = lean_string_utf8_get_fast(v_str_159_, v_startInclusive_160_);
        v___x_166_ = lean_uint32_dec_eq(v___x_165_, v_c_157_);
        if v___x_166_ == 0 {
            let mut v___x_167_: *mut LeanObject = core::ptr::null_mut();
            v___x_167_ = lean_box(0);
            return v___x_167_;
        } else {
            let mut v___x_168_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_169_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_170_: *mut LeanObject = core::ptr::null_mut();
            v___x_168_ = lean_string_utf8_next_fast(v_str_159_, v_startInclusive_160_);
            v___x_169_ = lean_nat_sub(v___x_168_, v_startInclusive_160_);
            v___x_170_ = lean_alloc_ctor(1, 1, (0) as u32);
            lean_ctor_set(v___x_170_, 0, v___x_169_);
            return v___x_170_;
        }
    } else {
        let mut v___x_171_: *mut LeanObject = core::ptr::null_mut();
        v___x_171_ = lean_box(0);
        return v___x_171_;
    }
}
pub unsafe fn l_String_Slice_Pattern_Char_instForwardPatternChar___lam__0___boxed(
    mut v_c_172_: *mut LeanObject,
    mut v_s_173_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_c_boxed_174_: u32 = 0;
    let mut v_res_175_: *mut LeanObject = core::ptr::null_mut();
    v_c_boxed_174_ = lean_unbox_uint32(v_c_172_);
    lean_dec(v_c_172_);
    v_res_175_ =
        l_String_Slice_Pattern_Char_instForwardPatternChar___lam__0(v_c_boxed_174_, v_s_173_);
    lean_dec_ref(v_s_173_);
    return v_res_175_;
}
pub unsafe fn l_String_Slice_Pattern_Char_instForwardPatternChar___lam__1(
    mut v_c_176_: u32,
    mut v_s_177_: *mut LeanObject,
    mut v_h_178_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_str_179_: *mut LeanObject = core::ptr::null_mut();
    let mut v_startInclusive_180_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_181_: u32 = 0;
    let mut v___x_182_: u8 = 0;
    v_str_179_ = lean_ctor_get(v_s_177_, 0);
    v_startInclusive_180_ = lean_ctor_get(v_s_177_, 1);
    v___x_181_ = lean_string_utf8_get_fast(v_str_179_, v_startInclusive_180_);
    v___x_182_ = lean_uint32_dec_eq(v___x_181_, v_c_176_);
    if v___x_182_ == 0 {
        let mut v___x_183_: *mut LeanObject = core::ptr::null_mut();
        v___x_183_ = lean_box(0);
        return v___x_183_;
    } else {
        let mut v___x_184_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_185_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_186_: *mut LeanObject = core::ptr::null_mut();
        v___x_184_ = lean_string_utf8_next_fast(v_str_179_, v_startInclusive_180_);
        v___x_185_ = lean_nat_sub(v___x_184_, v_startInclusive_180_);
        v___x_186_ = lean_alloc_ctor(1, 1, (0) as u32);
        lean_ctor_set(v___x_186_, 0, v___x_185_);
        return v___x_186_;
    }
}
pub unsafe fn l_String_Slice_Pattern_Char_instForwardPatternChar___lam__1___boxed(
    mut v_c_187_: *mut LeanObject,
    mut v_s_188_: *mut LeanObject,
    mut v_h_189_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_c_boxed_190_: u32 = 0;
    let mut v_res_191_: *mut LeanObject = core::ptr::null_mut();
    v_c_boxed_190_ = lean_unbox_uint32(v_c_187_);
    lean_dec(v_c_187_);
    v_res_191_ = l_String_Slice_Pattern_Char_instForwardPatternChar___lam__1(
        v_c_boxed_190_,
        v_s_188_,
        v_h_189_,
    );
    lean_dec_ref(v_s_188_);
    return v_res_191_;
}
pub unsafe fn l_String_Slice_Pattern_Char_instForwardPatternChar___lam__2(
    mut v_c_192_: u32,
    mut v_s_193_: *mut LeanObject,
) -> u8 {
    let mut v_str_194_: *mut LeanObject = core::ptr::null_mut();
    let mut v_startInclusive_195_: *mut LeanObject = core::ptr::null_mut();
    let mut v_endExclusive_196_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_197_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_198_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_199_: u8 = 0;
    v_str_194_ = lean_ctor_get(v_s_193_, 0);
    v_startInclusive_195_ = lean_ctor_get(v_s_193_, 1);
    v_endExclusive_196_ = lean_ctor_get(v_s_193_, 2);
    v___x_197_ = lean_unsigned_to_nat(0);
    v___x_198_ = lean_nat_sub(v_endExclusive_196_, v_startInclusive_195_);
    v___x_199_ = lean_nat_dec_eq(v___x_197_, v___x_198_);
    lean_dec(v___x_198_);
    if v___x_199_ == 0 {
        let mut v___x_200_: u32 = 0;
        let mut v___x_201_: u8 = 0;
        v___x_200_ = lean_string_utf8_get_fast(v_str_194_, v_startInclusive_195_);
        v___x_201_ = lean_uint32_dec_eq(v___x_200_, v_c_192_);
        return v___x_201_;
    } else {
        let mut v___x_202_: u8 = 0;
        v___x_202_ = 0;
        return v___x_202_;
    }
}
pub unsafe fn l_String_Slice_Pattern_Char_instForwardPatternChar___lam__2___boxed(
    mut v_c_203_: *mut LeanObject,
    mut v_s_204_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_c_boxed_205_: u32 = 0;
    let mut v_res_206_: u8 = 0;
    let mut v_r_207_: *mut LeanObject = core::ptr::null_mut();
    v_c_boxed_205_ = lean_unbox_uint32(v_c_203_);
    lean_dec(v_c_203_);
    v_res_206_ =
        l_String_Slice_Pattern_Char_instForwardPatternChar___lam__2(v_c_boxed_205_, v_s_204_);
    lean_dec_ref(v_s_204_);
    v_r_207_ = lean_box((v_res_206_) as usize);
    return v_r_207_;
}
pub unsafe fn l_String_Slice_Pattern_Char_instForwardPatternChar(
    mut v_c_208_: u32,
) -> *mut LeanObject {
    let mut v___x_209_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_210_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_211_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_212_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_213_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_214_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_215_: *mut LeanObject = core::ptr::null_mut();
    v___x_209_ = lean_box_uint32(v_c_208_);
    v___f_210_ = lean_alloc_closure(
        l_String_Slice_Pattern_Char_instForwardPatternChar___lam__0___boxed
            as *mut core::ffi::c_void,
        2,
        1,
    );
    lean_closure_set(v___f_210_, 0, v___x_209_);
    v___x_211_ = lean_box_uint32(v_c_208_);
    v___f_212_ = lean_alloc_closure(
        l_String_Slice_Pattern_Char_instForwardPatternChar___lam__1___boxed
            as *mut core::ffi::c_void,
        3,
        1,
    );
    lean_closure_set(v___f_212_, 0, v___x_211_);
    v___x_213_ = lean_box_uint32(v_c_208_);
    v___f_214_ = lean_alloc_closure(
        l_String_Slice_Pattern_Char_instForwardPatternChar___lam__2___boxed
            as *mut core::ffi::c_void,
        2,
        1,
    );
    lean_closure_set(v___f_214_, 0, v___x_213_);
    v___x_215_ = lean_alloc_ctor(0, 3, (0) as u32);
    lean_ctor_set(v___x_215_, 0, v___f_210_);
    lean_ctor_set(v___x_215_, 1, v___f_212_);
    lean_ctor_set(v___x_215_, 2, v___f_214_);
    return v___x_215_;
}
pub unsafe fn l_String_Slice_Pattern_Char_instForwardPatternChar___boxed(
    mut v_c_216_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_c_boxed_217_: u32 = 0;
    let mut v_res_218_: *mut LeanObject = core::ptr::null_mut();
    v_c_boxed_217_ = lean_unbox_uint32(v_c_216_);
    lean_dec(v_c_216_);
    v_res_218_ = l_String_Slice_Pattern_Char_instForwardPatternChar(v_c_boxed_217_);
    return v_res_218_;
}
pub unsafe fn l_String_Slice_Pattern_Char_instToForwardSearcherCharDefaultForwardSearcherForallBoolBeq___lam__0(
    mut v_s_219_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_220_: *mut LeanObject = core::ptr::null_mut();
    v___x_220_ = lean_unsigned_to_nat(0);
    return v___x_220_;
}
pub unsafe fn l_String_Slice_Pattern_Char_instToForwardSearcherCharDefaultForwardSearcherForallBoolBeq___lam__0___boxed(
    mut v_s_221_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_222_: *mut LeanObject = core::ptr::null_mut();
    v_res_222_ = l_String_Slice_Pattern_Char_instToForwardSearcherCharDefaultForwardSearcherForallBoolBeq___lam__0(v_s_221_);
    lean_dec_ref(v_s_221_);
    return v_res_222_;
}
pub unsafe fn l_String_Slice_Pattern_Char_instToForwardSearcherCharDefaultForwardSearcherForallBoolBeq(
    mut v_c_224_: u32,
) -> *mut LeanObject {
    let mut v___f_225_: *mut LeanObject = core::ptr::null_mut();
    v___f_225_ = l_String_Slice_Pattern_Char_instToForwardSearcherCharDefaultForwardSearcherForallBoolBeq___closed__0;
    return v___f_225_;
}
pub unsafe fn l_String_Slice_Pattern_Char_instToForwardSearcherCharDefaultForwardSearcherForallBoolBeq___boxed(
    mut v_c_226_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_c_boxed_227_: u32 = 0;
    let mut v_res_228_: *mut LeanObject = core::ptr::null_mut();
    v_c_boxed_227_ = lean_unbox_uint32(v_c_226_);
    lean_dec(v_c_226_);
    v_res_228_ =
        l_String_Slice_Pattern_Char_instToForwardSearcherCharDefaultForwardSearcherForallBoolBeq(
            v_c_boxed_227_,
        );
    return v_res_228_;
}
pub unsafe fn l_String_Slice_Pattern_Char_instBackwardPatternChar___lam__0(
    mut v_c_229_: u32,
    mut v_s_230_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_str_231_: *mut LeanObject = core::ptr::null_mut();
    let mut v_startInclusive_232_: *mut LeanObject = core::ptr::null_mut();
    let mut v_endExclusive_233_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_234_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_235_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_236_: u8 = 0;
    v_str_231_ = lean_ctor_get(v_s_230_, 0);
    v_startInclusive_232_ = lean_ctor_get(v_s_230_, 1);
    v_endExclusive_233_ = lean_ctor_get(v_s_230_, 2);
    v___x_234_ = lean_nat_sub(v_endExclusive_233_, v_startInclusive_232_);
    v___x_235_ = lean_unsigned_to_nat(0);
    v___x_236_ = lean_nat_dec_eq(v___x_234_, v___x_235_);
    if v___x_236_ == 0 {
        let mut v___x_237_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_238_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_239_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_240_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_241_: u32 = 0;
        let mut v___x_242_: u8 = 0;
        v___x_237_ = lean_unsigned_to_nat(1);
        v___x_238_ = lean_nat_sub(v___x_234_, v___x_237_);
        lean_dec(v___x_234_);
        v___x_239_ = l_String_Slice_posLE(v_s_230_, v___x_238_);
        v___x_240_ = lean_nat_add(v_startInclusive_232_, v___x_239_);
        v___x_241_ = lean_string_utf8_get_fast(v_str_231_, v___x_240_);
        lean_dec(v___x_240_);
        v___x_242_ = lean_uint32_dec_eq(v___x_241_, v_c_229_);
        if v___x_242_ == 0 {
            let mut v___x_243_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v___x_239_);
            v___x_243_ = lean_box(0);
            return v___x_243_;
        } else {
            let mut v___x_244_: *mut LeanObject = core::ptr::null_mut();
            v___x_244_ = lean_alloc_ctor(1, 1, (0) as u32);
            lean_ctor_set(v___x_244_, 0, v___x_239_);
            return v___x_244_;
        }
    } else {
        let mut v___x_245_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v___x_234_);
        v___x_245_ = lean_box(0);
        return v___x_245_;
    }
}
pub unsafe fn l_String_Slice_Pattern_Char_instBackwardPatternChar___lam__0___boxed(
    mut v_c_246_: *mut LeanObject,
    mut v_s_247_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_c_boxed_248_: u32 = 0;
    let mut v_res_249_: *mut LeanObject = core::ptr::null_mut();
    v_c_boxed_248_ = lean_unbox_uint32(v_c_246_);
    lean_dec(v_c_246_);
    v_res_249_ =
        l_String_Slice_Pattern_Char_instBackwardPatternChar___lam__0(v_c_boxed_248_, v_s_247_);
    lean_dec_ref(v_s_247_);
    return v_res_249_;
}
pub unsafe fn l_String_Slice_Pattern_Char_instBackwardPatternChar___lam__1(
    mut v_c_250_: u32,
    mut v_s_251_: *mut LeanObject,
    mut v_h_252_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_str_253_: *mut LeanObject = core::ptr::null_mut();
    let mut v_startInclusive_254_: *mut LeanObject = core::ptr::null_mut();
    let mut v_endExclusive_255_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_256_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_257_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_258_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_259_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_260_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_261_: u32 = 0;
    let mut v___x_262_: u8 = 0;
    v_str_253_ = lean_ctor_get(v_s_251_, 0);
    v_startInclusive_254_ = lean_ctor_get(v_s_251_, 1);
    v_endExclusive_255_ = lean_ctor_get(v_s_251_, 2);
    v___x_256_ = lean_nat_sub(v_endExclusive_255_, v_startInclusive_254_);
    v___x_257_ = lean_unsigned_to_nat(1);
    v___x_258_ = lean_nat_sub(v___x_256_, v___x_257_);
    lean_dec(v___x_256_);
    v___x_259_ = l_String_Slice_posLE(v_s_251_, v___x_258_);
    v___x_260_ = lean_nat_add(v_startInclusive_254_, v___x_259_);
    v___x_261_ = lean_string_utf8_get_fast(v_str_253_, v___x_260_);
    lean_dec(v___x_260_);
    v___x_262_ = lean_uint32_dec_eq(v___x_261_, v_c_250_);
    if v___x_262_ == 0 {
        let mut v___x_263_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v___x_259_);
        v___x_263_ = lean_box(0);
        return v___x_263_;
    } else {
        let mut v___x_264_: *mut LeanObject = core::ptr::null_mut();
        v___x_264_ = lean_alloc_ctor(1, 1, (0) as u32);
        lean_ctor_set(v___x_264_, 0, v___x_259_);
        return v___x_264_;
    }
}
pub unsafe fn l_String_Slice_Pattern_Char_instBackwardPatternChar___lam__1___boxed(
    mut v_c_265_: *mut LeanObject,
    mut v_s_266_: *mut LeanObject,
    mut v_h_267_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_c_boxed_268_: u32 = 0;
    let mut v_res_269_: *mut LeanObject = core::ptr::null_mut();
    v_c_boxed_268_ = lean_unbox_uint32(v_c_265_);
    lean_dec(v_c_265_);
    v_res_269_ = l_String_Slice_Pattern_Char_instBackwardPatternChar___lam__1(
        v_c_boxed_268_,
        v_s_266_,
        v_h_267_,
    );
    lean_dec_ref(v_s_266_);
    return v_res_269_;
}
pub unsafe fn l_String_Slice_Pattern_Char_instBackwardPatternChar___lam__2(
    mut v_c_270_: u32,
    mut v_s_271_: *mut LeanObject,
) -> u8 {
    let mut v_str_272_: *mut LeanObject = core::ptr::null_mut();
    let mut v_startInclusive_273_: *mut LeanObject = core::ptr::null_mut();
    let mut v_endExclusive_274_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_275_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_276_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_277_: u8 = 0;
    v_str_272_ = lean_ctor_get(v_s_271_, 0);
    v_startInclusive_273_ = lean_ctor_get(v_s_271_, 1);
    v_endExclusive_274_ = lean_ctor_get(v_s_271_, 2);
    v___x_275_ = lean_nat_sub(v_endExclusive_274_, v_startInclusive_273_);
    v___x_276_ = lean_unsigned_to_nat(0);
    v___x_277_ = lean_nat_dec_eq(v___x_275_, v___x_276_);
    if v___x_277_ == 0 {
        let mut v___x_278_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_279_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_280_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_281_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_282_: u32 = 0;
        let mut v___x_283_: u8 = 0;
        v___x_278_ = lean_unsigned_to_nat(1);
        v___x_279_ = lean_nat_sub(v___x_275_, v___x_278_);
        lean_dec(v___x_275_);
        v___x_280_ = l_String_Slice_posLE(v_s_271_, v___x_279_);
        v___x_281_ = lean_nat_add(v_startInclusive_273_, v___x_280_);
        lean_dec(v___x_280_);
        v___x_282_ = lean_string_utf8_get_fast(v_str_272_, v___x_281_);
        lean_dec(v___x_281_);
        v___x_283_ = lean_uint32_dec_eq(v___x_282_, v_c_270_);
        return v___x_283_;
    } else {
        let mut v___x_284_: u8 = 0;
        lean_dec(v___x_275_);
        v___x_284_ = 0;
        return v___x_284_;
    }
}
pub unsafe fn l_String_Slice_Pattern_Char_instBackwardPatternChar___lam__2___boxed(
    mut v_c_285_: *mut LeanObject,
    mut v_s_286_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_c_boxed_287_: u32 = 0;
    let mut v_res_288_: u8 = 0;
    let mut v_r_289_: *mut LeanObject = core::ptr::null_mut();
    v_c_boxed_287_ = lean_unbox_uint32(v_c_285_);
    lean_dec(v_c_285_);
    v_res_288_ =
        l_String_Slice_Pattern_Char_instBackwardPatternChar___lam__2(v_c_boxed_287_, v_s_286_);
    lean_dec_ref(v_s_286_);
    v_r_289_ = lean_box((v_res_288_) as usize);
    return v_r_289_;
}
pub unsafe fn l_String_Slice_Pattern_Char_instBackwardPatternChar(
    mut v_c_290_: u32,
) -> *mut LeanObject {
    let mut v___x_291_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_292_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_293_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_294_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_295_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_296_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_297_: *mut LeanObject = core::ptr::null_mut();
    v___x_291_ = lean_box_uint32(v_c_290_);
    v___f_292_ = lean_alloc_closure(
        l_String_Slice_Pattern_Char_instBackwardPatternChar___lam__0___boxed
            as *mut core::ffi::c_void,
        2,
        1,
    );
    lean_closure_set(v___f_292_, 0, v___x_291_);
    v___x_293_ = lean_box_uint32(v_c_290_);
    v___f_294_ = lean_alloc_closure(
        l_String_Slice_Pattern_Char_instBackwardPatternChar___lam__1___boxed
            as *mut core::ffi::c_void,
        3,
        1,
    );
    lean_closure_set(v___f_294_, 0, v___x_293_);
    v___x_295_ = lean_box_uint32(v_c_290_);
    v___f_296_ = lean_alloc_closure(
        l_String_Slice_Pattern_Char_instBackwardPatternChar___lam__2___boxed
            as *mut core::ffi::c_void,
        2,
        1,
    );
    lean_closure_set(v___f_296_, 0, v___x_295_);
    v___x_297_ = lean_alloc_ctor(0, 3, (0) as u32);
    lean_ctor_set(v___x_297_, 0, v___f_292_);
    lean_ctor_set(v___x_297_, 1, v___f_294_);
    lean_ctor_set(v___x_297_, 2, v___f_296_);
    return v___x_297_;
}
pub unsafe fn l_String_Slice_Pattern_Char_instBackwardPatternChar___boxed(
    mut v_c_298_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_c_boxed_299_: u32 = 0;
    let mut v_res_300_: *mut LeanObject = core::ptr::null_mut();
    v_c_boxed_299_ = lean_unbox_uint32(v_c_298_);
    lean_dec(v_c_298_);
    v_res_300_ = l_String_Slice_Pattern_Char_instBackwardPatternChar(v_c_boxed_299_);
    return v_res_300_;
}
pub unsafe fn l_String_Slice_Pattern_Char_instToBackwardSearcherCharDefaultBackwardSearcherForallBoolBeq___lam__0(
    mut v_s_301_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_startInclusive_302_: *mut LeanObject = core::ptr::null_mut();
    let mut v_endExclusive_303_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_304_: *mut LeanObject = core::ptr::null_mut();
    v_startInclusive_302_ = lean_ctor_get(v_s_301_, 1);
    v_endExclusive_303_ = lean_ctor_get(v_s_301_, 2);
    v___x_304_ = lean_nat_sub(v_endExclusive_303_, v_startInclusive_302_);
    return v___x_304_;
}
pub unsafe fn l_String_Slice_Pattern_Char_instToBackwardSearcherCharDefaultBackwardSearcherForallBoolBeq___lam__0___boxed(
    mut v_s_305_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_306_: *mut LeanObject = core::ptr::null_mut();
    v_res_306_ = l_String_Slice_Pattern_Char_instToBackwardSearcherCharDefaultBackwardSearcherForallBoolBeq___lam__0(v_s_305_);
    lean_dec_ref(v_s_305_);
    return v_res_306_;
}
pub unsafe fn l_String_Slice_Pattern_Char_instToBackwardSearcherCharDefaultBackwardSearcherForallBoolBeq(
    mut v_c_308_: u32,
) -> *mut LeanObject {
    let mut v___f_309_: *mut LeanObject = core::ptr::null_mut();
    v___f_309_ = l_String_Slice_Pattern_Char_instToBackwardSearcherCharDefaultBackwardSearcherForallBoolBeq___closed__0;
    return v___f_309_;
}
pub unsafe fn l_String_Slice_Pattern_Char_instToBackwardSearcherCharDefaultBackwardSearcherForallBoolBeq___boxed(
    mut v_c_310_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_c_boxed_311_: u32 = 0;
    let mut v_res_312_: *mut LeanObject = core::ptr::null_mut();
    v_c_boxed_311_ = lean_unbox_uint32(v_c_310_);
    lean_dec(v_c_310_);
    v_res_312_ =
        l_String_Slice_Pattern_Char_instToBackwardSearcherCharDefaultBackwardSearcherForallBoolBeq(
            v_c_boxed_311_,
        );
    return v_res_312_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Init_Data_String_Pattern_Char(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Init_Data_String_Pattern_Pred(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Init_Data_String_Pattern_Char(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_meta_initialized = true;
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Init_Data_String_Pattern_Char(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Init_Data_String_Pattern_Pred(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_String_Pattern_Char(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Init_Data_String_Pattern_Char(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Init_Data_String_Pattern_Char(builtin);
}
