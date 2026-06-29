// Lean compiler output
// Module: Init.Data.String.Pattern.Char
// Imports: Init.Data.String.Pattern.Pred
use crate::ffi::{
    lean_nat_add, lean_nat_dec_eq, lean_nat_sub, lean_string_utf8_get_fast,
    lean_string_utf8_next_fast, lean_uint32_dec_eq,
};
use crate::r#gen::Init::Data::String::FindPos::l_String_Slice_posLE;
use crate::r#gen::Init::Data::String::Pattern::Pred::{
    initialize_Init_Data_String_Pattern_Pred, runtime_initialize_Init_Data_String_Pattern_Pred,
};
pub static l_String_Slice_Pattern_Char_instToForwardSearcherCharDefaultForwardSearcherForallBoolBeq___closed__0_value: crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_String_Slice_Pattern_Char_instToForwardSearcherCharDefaultForwardSearcherForallBoolBeq___lam__0___boxed as *const core::ffi::c_void, m_arity: 1, m_num_fixed: 0, m_objs: [] };
static mut l_String_Slice_Pattern_Char_instToForwardSearcherCharDefaultForwardSearcherForallBoolBeq___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_String_Slice_Pattern_Char_instToForwardSearcherCharDefaultForwardSearcherForallBoolBeq___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_String_Slice_Pattern_Char_instToBackwardSearcherCharDefaultBackwardSearcherForallBoolBeq___closed__0_value: crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_String_Slice_Pattern_Char_instToBackwardSearcherCharDefaultBackwardSearcherForallBoolBeq___lam__0___boxed as *const core::ffi::c_void, m_arity: 1, m_num_fixed: 0, m_objs: [] };
static mut l_String_Slice_Pattern_Char_instToBackwardSearcherCharDefaultBackwardSearcherForallBoolBeq___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_String_Slice_Pattern_Char_instToBackwardSearcherCharDefaultBackwardSearcherForallBoolBeq___closed__0_value) as *mut crate::leanh::LeanObject;
pub unsafe fn l_String_Slice_Pattern_Char_instForwardPatternChar___lam__0(
    mut v_c_157_: u32,
    mut v_s_158_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_str_159_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_startInclusive_160_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_endExclusive_161_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_162_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_163_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_164_: u8 = 0;
    v_str_159_ = crate::leanh::lean_ctor_get(v_s_158_, 0);
    v_startInclusive_160_ = crate::leanh::lean_ctor_get(v_s_158_, 1);
    v_endExclusive_161_ = crate::leanh::lean_ctor_get(v_s_158_, 2);
    v___x_162_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_163_ = lean_nat_sub(v_endExclusive_161_, v_startInclusive_160_);
    v___x_164_ = lean_nat_dec_eq(v___x_162_, v___x_163_);
    crate::leanh::lean_dec(v___x_163_);
    if v___x_164_ == 0 {
        let mut v___x_165_: u32 = 0;
        let mut v___x_166_: u8 = 0;
        v___x_165_ = lean_string_utf8_get_fast(v_str_159_, v_startInclusive_160_);
        v___x_166_ = lean_uint32_dec_eq(v___x_165_, v_c_157_);
        if v___x_166_ == 0 {
            let mut v___x_167_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_167_ = crate::leanh::lean_box(0);
            return v___x_167_;
        } else {
            let mut v___x_168_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_169_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_170_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_168_ = lean_string_utf8_next_fast(v_str_159_, v_startInclusive_160_);
            v___x_169_ = lean_nat_sub(v___x_168_, v_startInclusive_160_);
            v___x_170_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
            crate::leanh::lean_ctor_set(v___x_170_, 0, v___x_169_);
            return v___x_170_;
        }
    } else {
        let mut v___x_171_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_171_ = crate::leanh::lean_box(0);
        return v___x_171_;
    }
}
pub unsafe fn l_String_Slice_Pattern_Char_instForwardPatternChar___lam__0___boxed(
    mut v_c_172_: *mut crate::leanh::LeanObject,
    mut v_s_173_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_c_boxed_174_: u32 = 0;
    let mut v_res_175_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_c_boxed_174_ = crate::leanh::lean_unbox_uint32(v_c_172_);
    crate::leanh::lean_dec(v_c_172_);
    v_res_175_ =
        l_String_Slice_Pattern_Char_instForwardPatternChar___lam__0(v_c_boxed_174_, v_s_173_);
    crate::leanh::lean_dec_ref(v_s_173_);
    return v_res_175_;
}
pub unsafe fn l_String_Slice_Pattern_Char_instForwardPatternChar___lam__1(
    mut v_c_176_: u32,
    mut v_s_177_: *mut crate::leanh::LeanObject,
    mut v_h_178_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_str_179_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_startInclusive_180_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_181_: u32 = 0;
    let mut v___x_182_: u8 = 0;
    v_str_179_ = crate::leanh::lean_ctor_get(v_s_177_, 0);
    v_startInclusive_180_ = crate::leanh::lean_ctor_get(v_s_177_, 1);
    v___x_181_ = lean_string_utf8_get_fast(v_str_179_, v_startInclusive_180_);
    v___x_182_ = lean_uint32_dec_eq(v___x_181_, v_c_176_);
    if v___x_182_ == 0 {
        let mut v___x_183_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_183_ = crate::leanh::lean_box(0);
        return v___x_183_;
    } else {
        let mut v___x_184_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_185_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_186_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_184_ = lean_string_utf8_next_fast(v_str_179_, v_startInclusive_180_);
        v___x_185_ = lean_nat_sub(v___x_184_, v_startInclusive_180_);
        v___x_186_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_186_, 0, v___x_185_);
        return v___x_186_;
    }
}
pub unsafe fn l_String_Slice_Pattern_Char_instForwardPatternChar___lam__1___boxed(
    mut v_c_187_: *mut crate::leanh::LeanObject,
    mut v_s_188_: *mut crate::leanh::LeanObject,
    mut v_h_189_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_c_boxed_190_: u32 = 0;
    let mut v_res_191_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_c_boxed_190_ = crate::leanh::lean_unbox_uint32(v_c_187_);
    crate::leanh::lean_dec(v_c_187_);
    v_res_191_ = l_String_Slice_Pattern_Char_instForwardPatternChar___lam__1(
        v_c_boxed_190_,
        v_s_188_,
        v_h_189_,
    );
    crate::leanh::lean_dec_ref(v_s_188_);
    return v_res_191_;
}
pub unsafe fn l_String_Slice_Pattern_Char_instForwardPatternChar___lam__2(
    mut v_c_192_: u32,
    mut v_s_193_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v_str_194_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_startInclusive_195_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_endExclusive_196_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_197_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_198_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_199_: u8 = 0;
    v_str_194_ = crate::leanh::lean_ctor_get(v_s_193_, 0);
    v_startInclusive_195_ = crate::leanh::lean_ctor_get(v_s_193_, 1);
    v_endExclusive_196_ = crate::leanh::lean_ctor_get(v_s_193_, 2);
    v___x_197_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_198_ = lean_nat_sub(v_endExclusive_196_, v_startInclusive_195_);
    v___x_199_ = lean_nat_dec_eq(v___x_197_, v___x_198_);
    crate::leanh::lean_dec(v___x_198_);
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
    mut v_c_203_: *mut crate::leanh::LeanObject,
    mut v_s_204_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_c_boxed_205_: u32 = 0;
    let mut v_res_206_: u8 = 0;
    let mut v_r_207_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_c_boxed_205_ = crate::leanh::lean_unbox_uint32(v_c_203_);
    crate::leanh::lean_dec(v_c_203_);
    v_res_206_ =
        l_String_Slice_Pattern_Char_instForwardPatternChar___lam__2(v_c_boxed_205_, v_s_204_);
    crate::leanh::lean_dec_ref(v_s_204_);
    v_r_207_ = crate::leanh::lean_box((v_res_206_) as usize);
    return v_r_207_;
}
pub unsafe fn l_String_Slice_Pattern_Char_instForwardPatternChar(
    mut v_c_208_: u32,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_209_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_210_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_211_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_212_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_213_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_214_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_215_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_209_ = crate::leanh::lean_box_uint32(v_c_208_);
    v___f_210_ = crate::leanh::lean_alloc_closure(
        l_String_Slice_Pattern_Char_instForwardPatternChar___lam__0___boxed
            as *mut core::ffi::c_void,
        2,
        1,
    );
    crate::leanh::lean_closure_set(v___f_210_, 0, v___x_209_);
    v___x_211_ = crate::leanh::lean_box_uint32(v_c_208_);
    v___f_212_ = crate::leanh::lean_alloc_closure(
        l_String_Slice_Pattern_Char_instForwardPatternChar___lam__1___boxed
            as *mut core::ffi::c_void,
        3,
        1,
    );
    crate::leanh::lean_closure_set(v___f_212_, 0, v___x_211_);
    v___x_213_ = crate::leanh::lean_box_uint32(v_c_208_);
    v___f_214_ = crate::leanh::lean_alloc_closure(
        l_String_Slice_Pattern_Char_instForwardPatternChar___lam__2___boxed
            as *mut core::ffi::c_void,
        2,
        1,
    );
    crate::leanh::lean_closure_set(v___f_214_, 0, v___x_213_);
    v___x_215_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_215_, 0, v___f_210_);
    crate::leanh::lean_ctor_set(v___x_215_, 1, v___f_212_);
    crate::leanh::lean_ctor_set(v___x_215_, 2, v___f_214_);
    return v___x_215_;
}
pub unsafe fn l_String_Slice_Pattern_Char_instForwardPatternChar___boxed(
    mut v_c_216_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_c_boxed_217_: u32 = 0;
    let mut v_res_218_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_c_boxed_217_ = crate::leanh::lean_unbox_uint32(v_c_216_);
    crate::leanh::lean_dec(v_c_216_);
    v_res_218_ = l_String_Slice_Pattern_Char_instForwardPatternChar(v_c_boxed_217_);
    return v_res_218_;
}
pub unsafe fn l_String_Slice_Pattern_Char_instToForwardSearcherCharDefaultForwardSearcherForallBoolBeq___lam__0(
    mut v_s_219_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_220_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_220_ = crate::leanh::lean_unsigned_to_nat(0);
    return v___x_220_;
}
pub unsafe fn l_String_Slice_Pattern_Char_instToForwardSearcherCharDefaultForwardSearcherForallBoolBeq___lam__0___boxed(
    mut v_s_221_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_222_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_222_ = l_String_Slice_Pattern_Char_instToForwardSearcherCharDefaultForwardSearcherForallBoolBeq___lam__0(v_s_221_);
    crate::leanh::lean_dec_ref(v_s_221_);
    return v_res_222_;
}
pub unsafe fn l_String_Slice_Pattern_Char_instToForwardSearcherCharDefaultForwardSearcherForallBoolBeq(
    mut v_c_224_: u32,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_225_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_225_ = l_String_Slice_Pattern_Char_instToForwardSearcherCharDefaultForwardSearcherForallBoolBeq___closed__0;
    return v___f_225_;
}
pub unsafe fn l_String_Slice_Pattern_Char_instToForwardSearcherCharDefaultForwardSearcherForallBoolBeq___boxed(
    mut v_c_226_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_c_boxed_227_: u32 = 0;
    let mut v_res_228_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_c_boxed_227_ = crate::leanh::lean_unbox_uint32(v_c_226_);
    crate::leanh::lean_dec(v_c_226_);
    v_res_228_ =
        l_String_Slice_Pattern_Char_instToForwardSearcherCharDefaultForwardSearcherForallBoolBeq(
            v_c_boxed_227_,
        );
    return v_res_228_;
}
pub unsafe fn l_String_Slice_Pattern_Char_instBackwardPatternChar___lam__0(
    mut v_c_229_: u32,
    mut v_s_230_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_str_231_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_startInclusive_232_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_endExclusive_233_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_234_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_235_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_236_: u8 = 0;
    v_str_231_ = crate::leanh::lean_ctor_get(v_s_230_, 0);
    v_startInclusive_232_ = crate::leanh::lean_ctor_get(v_s_230_, 1);
    v_endExclusive_233_ = crate::leanh::lean_ctor_get(v_s_230_, 2);
    v___x_234_ = lean_nat_sub(v_endExclusive_233_, v_startInclusive_232_);
    v___x_235_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_236_ = lean_nat_dec_eq(v___x_234_, v___x_235_);
    if v___x_236_ == 0 {
        let mut v___x_237_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_238_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_239_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_240_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_241_: u32 = 0;
        let mut v___x_242_: u8 = 0;
        v___x_237_ = crate::leanh::lean_unsigned_to_nat(1);
        v___x_238_ = lean_nat_sub(v___x_234_, v___x_237_);
        crate::leanh::lean_dec(v___x_234_);
        v___x_239_ = l_String_Slice_posLE(v_s_230_, v___x_238_);
        v___x_240_ = lean_nat_add(v_startInclusive_232_, v___x_239_);
        v___x_241_ = lean_string_utf8_get_fast(v_str_231_, v___x_240_);
        crate::leanh::lean_dec(v___x_240_);
        v___x_242_ = lean_uint32_dec_eq(v___x_241_, v_c_229_);
        if v___x_242_ == 0 {
            let mut v___x_243_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v___x_239_);
            v___x_243_ = crate::leanh::lean_box(0);
            return v___x_243_;
        } else {
            let mut v___x_244_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_244_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
            crate::leanh::lean_ctor_set(v___x_244_, 0, v___x_239_);
            return v___x_244_;
        }
    } else {
        let mut v___x_245_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v___x_234_);
        v___x_245_ = crate::leanh::lean_box(0);
        return v___x_245_;
    }
}
pub unsafe fn l_String_Slice_Pattern_Char_instBackwardPatternChar___lam__0___boxed(
    mut v_c_246_: *mut crate::leanh::LeanObject,
    mut v_s_247_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_c_boxed_248_: u32 = 0;
    let mut v_res_249_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_c_boxed_248_ = crate::leanh::lean_unbox_uint32(v_c_246_);
    crate::leanh::lean_dec(v_c_246_);
    v_res_249_ =
        l_String_Slice_Pattern_Char_instBackwardPatternChar___lam__0(v_c_boxed_248_, v_s_247_);
    crate::leanh::lean_dec_ref(v_s_247_);
    return v_res_249_;
}
pub unsafe fn l_String_Slice_Pattern_Char_instBackwardPatternChar___lam__1(
    mut v_c_250_: u32,
    mut v_s_251_: *mut crate::leanh::LeanObject,
    mut v_h_252_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_str_253_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_startInclusive_254_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_endExclusive_255_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_256_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_257_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_258_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_259_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_260_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_261_: u32 = 0;
    let mut v___x_262_: u8 = 0;
    v_str_253_ = crate::leanh::lean_ctor_get(v_s_251_, 0);
    v_startInclusive_254_ = crate::leanh::lean_ctor_get(v_s_251_, 1);
    v_endExclusive_255_ = crate::leanh::lean_ctor_get(v_s_251_, 2);
    v___x_256_ = lean_nat_sub(v_endExclusive_255_, v_startInclusive_254_);
    v___x_257_ = crate::leanh::lean_unsigned_to_nat(1);
    v___x_258_ = lean_nat_sub(v___x_256_, v___x_257_);
    crate::leanh::lean_dec(v___x_256_);
    v___x_259_ = l_String_Slice_posLE(v_s_251_, v___x_258_);
    v___x_260_ = lean_nat_add(v_startInclusive_254_, v___x_259_);
    v___x_261_ = lean_string_utf8_get_fast(v_str_253_, v___x_260_);
    crate::leanh::lean_dec(v___x_260_);
    v___x_262_ = lean_uint32_dec_eq(v___x_261_, v_c_250_);
    if v___x_262_ == 0 {
        let mut v___x_263_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v___x_259_);
        v___x_263_ = crate::leanh::lean_box(0);
        return v___x_263_;
    } else {
        let mut v___x_264_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_264_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_264_, 0, v___x_259_);
        return v___x_264_;
    }
}
pub unsafe fn l_String_Slice_Pattern_Char_instBackwardPatternChar___lam__1___boxed(
    mut v_c_265_: *mut crate::leanh::LeanObject,
    mut v_s_266_: *mut crate::leanh::LeanObject,
    mut v_h_267_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_c_boxed_268_: u32 = 0;
    let mut v_res_269_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_c_boxed_268_ = crate::leanh::lean_unbox_uint32(v_c_265_);
    crate::leanh::lean_dec(v_c_265_);
    v_res_269_ = l_String_Slice_Pattern_Char_instBackwardPatternChar___lam__1(
        v_c_boxed_268_,
        v_s_266_,
        v_h_267_,
    );
    crate::leanh::lean_dec_ref(v_s_266_);
    return v_res_269_;
}
pub unsafe fn l_String_Slice_Pattern_Char_instBackwardPatternChar___lam__2(
    mut v_c_270_: u32,
    mut v_s_271_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v_str_272_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_startInclusive_273_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_endExclusive_274_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_275_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_276_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_277_: u8 = 0;
    v_str_272_ = crate::leanh::lean_ctor_get(v_s_271_, 0);
    v_startInclusive_273_ = crate::leanh::lean_ctor_get(v_s_271_, 1);
    v_endExclusive_274_ = crate::leanh::lean_ctor_get(v_s_271_, 2);
    v___x_275_ = lean_nat_sub(v_endExclusive_274_, v_startInclusive_273_);
    v___x_276_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_277_ = lean_nat_dec_eq(v___x_275_, v___x_276_);
    if v___x_277_ == 0 {
        let mut v___x_278_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_279_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_280_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_281_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_282_: u32 = 0;
        let mut v___x_283_: u8 = 0;
        v___x_278_ = crate::leanh::lean_unsigned_to_nat(1);
        v___x_279_ = lean_nat_sub(v___x_275_, v___x_278_);
        crate::leanh::lean_dec(v___x_275_);
        v___x_280_ = l_String_Slice_posLE(v_s_271_, v___x_279_);
        v___x_281_ = lean_nat_add(v_startInclusive_273_, v___x_280_);
        crate::leanh::lean_dec(v___x_280_);
        v___x_282_ = lean_string_utf8_get_fast(v_str_272_, v___x_281_);
        crate::leanh::lean_dec(v___x_281_);
        v___x_283_ = lean_uint32_dec_eq(v___x_282_, v_c_270_);
        return v___x_283_;
    } else {
        let mut v___x_284_: u8 = 0;
        crate::leanh::lean_dec(v___x_275_);
        v___x_284_ = 0;
        return v___x_284_;
    }
}
pub unsafe fn l_String_Slice_Pattern_Char_instBackwardPatternChar___lam__2___boxed(
    mut v_c_285_: *mut crate::leanh::LeanObject,
    mut v_s_286_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_c_boxed_287_: u32 = 0;
    let mut v_res_288_: u8 = 0;
    let mut v_r_289_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_c_boxed_287_ = crate::leanh::lean_unbox_uint32(v_c_285_);
    crate::leanh::lean_dec(v_c_285_);
    v_res_288_ =
        l_String_Slice_Pattern_Char_instBackwardPatternChar___lam__2(v_c_boxed_287_, v_s_286_);
    crate::leanh::lean_dec_ref(v_s_286_);
    v_r_289_ = crate::leanh::lean_box((v_res_288_) as usize);
    return v_r_289_;
}
pub unsafe fn l_String_Slice_Pattern_Char_instBackwardPatternChar(
    mut v_c_290_: u32,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_291_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_292_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_293_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_294_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_295_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_296_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_297_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_291_ = crate::leanh::lean_box_uint32(v_c_290_);
    v___f_292_ = crate::leanh::lean_alloc_closure(
        l_String_Slice_Pattern_Char_instBackwardPatternChar___lam__0___boxed
            as *mut core::ffi::c_void,
        2,
        1,
    );
    crate::leanh::lean_closure_set(v___f_292_, 0, v___x_291_);
    v___x_293_ = crate::leanh::lean_box_uint32(v_c_290_);
    v___f_294_ = crate::leanh::lean_alloc_closure(
        l_String_Slice_Pattern_Char_instBackwardPatternChar___lam__1___boxed
            as *mut core::ffi::c_void,
        3,
        1,
    );
    crate::leanh::lean_closure_set(v___f_294_, 0, v___x_293_);
    v___x_295_ = crate::leanh::lean_box_uint32(v_c_290_);
    v___f_296_ = crate::leanh::lean_alloc_closure(
        l_String_Slice_Pattern_Char_instBackwardPatternChar___lam__2___boxed
            as *mut core::ffi::c_void,
        2,
        1,
    );
    crate::leanh::lean_closure_set(v___f_296_, 0, v___x_295_);
    v___x_297_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_297_, 0, v___f_292_);
    crate::leanh::lean_ctor_set(v___x_297_, 1, v___f_294_);
    crate::leanh::lean_ctor_set(v___x_297_, 2, v___f_296_);
    return v___x_297_;
}
pub unsafe fn l_String_Slice_Pattern_Char_instBackwardPatternChar___boxed(
    mut v_c_298_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_c_boxed_299_: u32 = 0;
    let mut v_res_300_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_c_boxed_299_ = crate::leanh::lean_unbox_uint32(v_c_298_);
    crate::leanh::lean_dec(v_c_298_);
    v_res_300_ = l_String_Slice_Pattern_Char_instBackwardPatternChar(v_c_boxed_299_);
    return v_res_300_;
}
pub unsafe fn l_String_Slice_Pattern_Char_instToBackwardSearcherCharDefaultBackwardSearcherForallBoolBeq___lam__0(
    mut v_s_301_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_startInclusive_302_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_endExclusive_303_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_304_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_startInclusive_302_ = crate::leanh::lean_ctor_get(v_s_301_, 1);
    v_endExclusive_303_ = crate::leanh::lean_ctor_get(v_s_301_, 2);
    v___x_304_ = lean_nat_sub(v_endExclusive_303_, v_startInclusive_302_);
    return v___x_304_;
}
pub unsafe fn l_String_Slice_Pattern_Char_instToBackwardSearcherCharDefaultBackwardSearcherForallBoolBeq___lam__0___boxed(
    mut v_s_305_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_306_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_306_ = l_String_Slice_Pattern_Char_instToBackwardSearcherCharDefaultBackwardSearcherForallBoolBeq___lam__0(v_s_305_);
    crate::leanh::lean_dec_ref(v_s_305_);
    return v_res_306_;
}
pub unsafe fn l_String_Slice_Pattern_Char_instToBackwardSearcherCharDefaultBackwardSearcherForallBoolBeq(
    mut v_c_308_: u32,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_309_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_309_ = l_String_Slice_Pattern_Char_instToBackwardSearcherCharDefaultBackwardSearcherForallBoolBeq___closed__0;
    return v___f_309_;
}
pub unsafe fn l_String_Slice_Pattern_Char_instToBackwardSearcherCharDefaultBackwardSearcherForallBoolBeq___boxed(
    mut v_c_310_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_c_boxed_311_: u32 = 0;
    let mut v_res_312_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_c_boxed_311_ = crate::leanh::lean_unbox_uint32(v_c_310_);
    crate::leanh::lean_dec(v_c_310_);
    v_res_312_ =
        l_String_Slice_Pattern_Char_instToBackwardSearcherCharDefaultBackwardSearcherForallBoolBeq(
            v_c_boxed_311_,
        );
    return v_res_312_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Init_Data_String_Pattern_Char(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Init_Data_String_Pattern_Pred(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Init_Data_String_Pattern_Char(
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
pub unsafe fn initialize_Init_Data_String_Pattern_Char(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Init_Data_String_Pattern_Pred(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_String_Pattern_Char(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Init_Data_String_Pattern_Char(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Init_Data_String_Pattern_Char(builtin);
}
