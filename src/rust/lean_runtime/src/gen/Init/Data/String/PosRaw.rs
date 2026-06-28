// Lean compiler output
// Module: Init.Data.String.PosRaw
// Imports: Init.Data.ByteArray.Basic Init.Data.Nat.Simproc Init.Omega
use crate::r#gen::Init::Data::ByteArray::Basic::{
    initialize_Init_Data_ByteArray_Basic, runtime_initialize_Init_Data_ByteArray_Basic,
};
use crate::r#gen::Init::Data::Nat::Simproc::{
    initialize_Init_Data_Nat_Simproc, runtime_initialize_Init_Data_Nat_Simproc,
};
use crate::r#gen::Init::Omega::{initialize_Init_Omega, runtime_initialize_Init_Omega};
use crate::r#gen::Init::Prelude::l_Char_utf8Size;
use crate::lean_imports_rs::Init::Prelude::{
    lean_nat_add, lean_nat_dec_le, lean_nat_dec_lt, lean_nat_sub, lean_string_utf8_byte_size,
};
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_box, lean_dec, lean_dec_ref, lean_inc,
    lean_io_result_is_error, lean_io_result_mk_ok, lean_mark_persistent, lean_unbox_uint32,
    lean_unsigned_to_nat,
};
pub static l_String_instHSubRaw___closed__0_value: LeanClosureObject<0> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_String_instHSubRaw___lam__0___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_String_instHSubRaw___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_String_instHSubRaw___closed__0_value) as *mut LeanObject;
pub static mut l_String_instHSubRaw: *mut LeanObject =
    core::ptr::addr_of!(l_String_instHSubRaw___closed__0_value) as *mut LeanObject;
pub static l_String_instHSubRawChar___closed__0_value: LeanClosureObject<0> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_String_instHSubRawChar___lam__0___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_String_instHSubRawChar___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_String_instHSubRawChar___closed__0_value) as *mut LeanObject;
pub static mut l_String_instHSubRawChar: *mut LeanObject =
    core::ptr::addr_of!(l_String_instHSubRawChar___closed__0_value) as *mut LeanObject;
pub static l_String_instHAddRawChar___closed__0_value: LeanClosureObject<0> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_String_instHAddRawChar___lam__0___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_String_instHAddRawChar___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_String_instHAddRawChar___closed__0_value) as *mut LeanObject;
pub static mut l_String_instHAddRawChar: *mut LeanObject =
    core::ptr::addr_of!(l_String_instHAddRawChar___closed__0_value) as *mut LeanObject;
pub static l_String_instHAddCharRaw___closed__0_value: LeanClosureObject<0> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_String_instHAddCharRaw___lam__0___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_String_instHAddCharRaw___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_String_instHAddCharRaw___closed__0_value) as *mut LeanObject;
pub static mut l_String_instHAddCharRaw: *mut LeanObject =
    core::ptr::addr_of!(l_String_instHAddCharRaw___closed__0_value) as *mut LeanObject;
pub static l_String_instHAddRaw___closed__0_value: LeanClosureObject<0> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_String_instHAddRaw___lam__0___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_String_instHAddRaw___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_String_instHAddRaw___closed__0_value) as *mut LeanObject;
pub static mut l_String_instHAddRaw: *mut LeanObject =
    core::ptr::addr_of!(l_String_instHAddRaw___closed__0_value) as *mut LeanObject;
pub static l_String_instHAddRaw__1___closed__0_value: LeanClosureObject<0> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_String_instHAddRaw__1___lam__0___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_String_instHAddRaw__1___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_String_instHAddRaw__1___closed__0_value) as *mut LeanObject;
pub static mut l_String_instHAddRaw__1: *mut LeanObject =
    core::ptr::addr_of!(l_String_instHAddRaw__1___closed__0_value) as *mut LeanObject;
pub static mut l_String_instLERaw: *mut LeanObject = core::ptr::null_mut();
pub static mut l_String_instLTRaw: *mut LeanObject = core::ptr::null_mut();
pub unsafe fn l_String_instHSubRaw___lam__0(
    mut v_p_142_: *mut LeanObject,
    mut v_s_143_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_144_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_145_: *mut LeanObject = core::ptr::null_mut();
    v___x_144_ = lean_string_utf8_byte_size(v_s_143_);
    v___x_145_ = lean_nat_sub(v_p_142_, v___x_144_);
    return v___x_145_;
}
pub unsafe fn l_String_instHSubRaw___lam__0___boxed(
    mut v_p_146_: *mut LeanObject,
    mut v_s_147_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_148_: *mut LeanObject = core::ptr::null_mut();
    v_res_148_ = l_String_instHSubRaw___lam__0(v_p_146_, v_s_147_);
    lean_dec_ref(v_s_147_);
    lean_dec(v_p_146_);
    return v_res_148_;
}
pub unsafe fn l_String_instHSubRawChar___lam__0(
    mut v_p_151_: *mut LeanObject,
    mut v_c_152_: u32,
) -> *mut LeanObject {
    let mut v___x_153_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_154_: *mut LeanObject = core::ptr::null_mut();
    v___x_153_ = l_Char_utf8Size(v_c_152_);
    v___x_154_ = lean_nat_sub(v_p_151_, v___x_153_);
    lean_dec(v___x_153_);
    return v___x_154_;
}
pub unsafe fn l_String_instHSubRawChar___lam__0___boxed(
    mut v_p_155_: *mut LeanObject,
    mut v_c_156_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_c_boxed_157_: u32 = 0;
    let mut v_res_158_: *mut LeanObject = core::ptr::null_mut();
    v_c_boxed_157_ = lean_unbox_uint32(v_c_156_);
    lean_dec(v_c_156_);
    v_res_158_ = l_String_instHSubRawChar___lam__0(v_p_155_, v_c_boxed_157_);
    lean_dec(v_p_155_);
    return v_res_158_;
}
pub unsafe fn lean_string_pos_sub(
    mut v_p_u2081_161_: *mut LeanObject,
    mut v_p_u2082_162_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_163_: *mut LeanObject = core::ptr::null_mut();
    v___x_163_ = lean_nat_sub(v_p_u2081_161_, v_p_u2082_162_);
    lean_dec(v_p_u2082_162_);
    lean_dec(v_p_u2081_161_);
    return v___x_163_;
}
pub unsafe fn l_String_instHAddRawChar___lam__0(
    mut v_p_164_: *mut LeanObject,
    mut v_c_165_: u32,
) -> *mut LeanObject {
    let mut v___x_166_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_167_: *mut LeanObject = core::ptr::null_mut();
    v___x_166_ = l_Char_utf8Size(v_c_165_);
    v___x_167_ = lean_nat_add(v_p_164_, v___x_166_);
    lean_dec(v___x_166_);
    return v___x_167_;
}
pub unsafe fn l_String_instHAddRawChar___lam__0___boxed(
    mut v_p_168_: *mut LeanObject,
    mut v_c_169_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_c_boxed_170_: u32 = 0;
    let mut v_res_171_: *mut LeanObject = core::ptr::null_mut();
    v_c_boxed_170_ = lean_unbox_uint32(v_c_169_);
    lean_dec(v_c_169_);
    v_res_171_ = l_String_instHAddRawChar___lam__0(v_p_168_, v_c_boxed_170_);
    lean_dec(v_p_168_);
    return v_res_171_;
}
pub unsafe fn l_String_instHAddCharRaw___lam__0(
    mut v_c_174_: u32,
    mut v_p_175_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_176_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_177_: *mut LeanObject = core::ptr::null_mut();
    v___x_176_ = l_Char_utf8Size(v_c_174_);
    v___x_177_ = lean_nat_add(v___x_176_, v_p_175_);
    lean_dec(v___x_176_);
    return v___x_177_;
}
pub unsafe fn l_String_instHAddCharRaw___lam__0___boxed(
    mut v_c_178_: *mut LeanObject,
    mut v_p_179_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_c_boxed_180_: u32 = 0;
    let mut v_res_181_: *mut LeanObject = core::ptr::null_mut();
    v_c_boxed_180_ = lean_unbox_uint32(v_c_178_);
    lean_dec(v_c_178_);
    v_res_181_ = l_String_instHAddCharRaw___lam__0(v_c_boxed_180_, v_p_179_);
    lean_dec(v_p_179_);
    return v_res_181_;
}
pub unsafe fn l_String_instHAddRaw___lam__0(
    mut v_s_184_: *mut LeanObject,
    mut v_p_185_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_186_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_187_: *mut LeanObject = core::ptr::null_mut();
    v___x_186_ = lean_string_utf8_byte_size(v_s_184_);
    v___x_187_ = lean_nat_add(v___x_186_, v_p_185_);
    return v___x_187_;
}
pub unsafe fn l_String_instHAddRaw___lam__0___boxed(
    mut v_s_188_: *mut LeanObject,
    mut v_p_189_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_190_: *mut LeanObject = core::ptr::null_mut();
    v_res_190_ = l_String_instHAddRaw___lam__0(v_s_188_, v_p_189_);
    lean_dec(v_p_189_);
    lean_dec_ref(v_s_188_);
    return v_res_190_;
}
pub unsafe fn l_String_instHAddRaw__1___lam__0(
    mut v_p_193_: *mut LeanObject,
    mut v_s_194_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_195_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_196_: *mut LeanObject = core::ptr::null_mut();
    v___x_195_ = lean_string_utf8_byte_size(v_s_194_);
    v___x_196_ = lean_nat_add(v_p_193_, v___x_195_);
    return v___x_196_;
}
pub unsafe fn l_String_instHAddRaw__1___lam__0___boxed(
    mut v_p_197_: *mut LeanObject,
    mut v_s_198_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_199_: *mut LeanObject = core::ptr::null_mut();
    v_res_199_ = l_String_instHAddRaw__1___lam__0(v_p_197_, v_s_198_);
    lean_dec_ref(v_s_198_);
    lean_dec(v_p_197_);
    return v_res_199_;
}
pub unsafe fn _init_l_String_instLERaw() -> *mut LeanObject {
    let mut v___x_202_: *mut LeanObject = core::ptr::null_mut();
    v___x_202_ = lean_box(0);
    return v___x_202_;
}
pub unsafe fn _init_l_String_instLTRaw() -> *mut LeanObject {
    let mut v___x_203_: *mut LeanObject = core::ptr::null_mut();
    v___x_203_ = lean_box(0);
    return v___x_203_;
}
pub unsafe fn l_String_instDecidableLeRaw(
    mut v_p_u2081_204_: *mut LeanObject,
    mut v_p_u2082_205_: *mut LeanObject,
) -> u8 {
    let mut v___x_206_: u8 = 0;
    v___x_206_ = lean_nat_dec_le(v_p_u2081_204_, v_p_u2082_205_);
    return v___x_206_;
}
pub unsafe fn l_String_instDecidableLeRaw___boxed(
    mut v_p_u2081_207_: *mut LeanObject,
    mut v_p_u2082_208_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_209_: u8 = 0;
    let mut v_r_210_: *mut LeanObject = core::ptr::null_mut();
    v_res_209_ = l_String_instDecidableLeRaw(v_p_u2081_207_, v_p_u2082_208_);
    lean_dec(v_p_u2082_208_);
    lean_dec(v_p_u2081_207_);
    v_r_210_ = lean_box((v_res_209_) as usize);
    return v_r_210_;
}
pub unsafe fn l_String_instDecidableLtRaw(
    mut v_p_u2081_211_: *mut LeanObject,
    mut v_p_u2082_212_: *mut LeanObject,
) -> u8 {
    let mut v___x_213_: u8 = 0;
    v___x_213_ = lean_nat_dec_lt(v_p_u2081_211_, v_p_u2082_212_);
    return v___x_213_;
}
pub unsafe fn l_String_instDecidableLtRaw___boxed(
    mut v_p_u2081_214_: *mut LeanObject,
    mut v_p_u2082_215_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_216_: u8 = 0;
    let mut v_r_217_: *mut LeanObject = core::ptr::null_mut();
    v_res_216_ = l_String_instDecidableLtRaw(v_p_u2081_214_, v_p_u2082_215_);
    lean_dec(v_p_u2082_215_);
    lean_dec(v_p_u2081_214_);
    v_r_217_ = lean_box((v_res_216_) as usize);
    return v_r_217_;
}
pub unsafe fn l_String_Pos_Raw_byteDistance(
    mut v_lo_218_: *mut LeanObject,
    mut v_hi_219_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_220_: *mut LeanObject = core::ptr::null_mut();
    v___x_220_ = lean_nat_sub(v_hi_219_, v_lo_218_);
    return v___x_220_;
}
pub unsafe fn l_String_Pos_Raw_byteDistance___boxed(
    mut v_lo_221_: *mut LeanObject,
    mut v_hi_222_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_223_: *mut LeanObject = core::ptr::null_mut();
    v_res_223_ = l_String_Pos_Raw_byteDistance(v_lo_221_, v_hi_222_);
    lean_dec(v_hi_222_);
    lean_dec(v_lo_221_);
    return v_res_223_;
}
pub unsafe fn l_String_getUTF8Byte___boxed(
    mut v_s_227_: *mut LeanObject,
    mut v_p_228_: *mut LeanObject,
    mut v_h_229_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_230_: u8 = 0;
    let mut v_r_231_: *mut LeanObject = core::ptr::null_mut();
    v_res_230_ = lean_string_get_byte_fast(v_s_227_, v_p_228_);
    lean_dec_ref(v_s_227_);
    v_r_231_ = lean_box((v_res_230_) as usize);
    return v_r_231_;
}
pub unsafe fn l_String_getUtf8Byte___boxed(
    mut v_s_235_: *mut LeanObject,
    mut v_p_236_: *mut LeanObject,
    mut v_h_237_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_238_: u8 = 0;
    let mut v_r_239_: *mut LeanObject = core::ptr::null_mut();
    v_res_238_ = lean_string_get_byte_fast(v_s_235_, v_p_236_);
    v_r_239_ = lean_box((v_res_238_) as usize);
    return v_r_239_;
}
pub unsafe fn l_String_Pos_Raw_offsetBy(
    mut v_p_240_: *mut LeanObject,
    mut v_offset_241_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_242_: *mut LeanObject = core::ptr::null_mut();
    v___x_242_ = lean_nat_add(v_offset_241_, v_p_240_);
    return v___x_242_;
}
pub unsafe fn l_String_Pos_Raw_offsetBy___boxed(
    mut v_p_243_: *mut LeanObject,
    mut v_offset_244_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_245_: *mut LeanObject = core::ptr::null_mut();
    v_res_245_ = l_String_Pos_Raw_offsetBy(v_p_243_, v_offset_244_);
    lean_dec(v_offset_244_);
    lean_dec(v_p_243_);
    return v_res_245_;
}
pub unsafe fn l_String_Pos_Raw_unoffsetBy(
    mut v_p_246_: *mut LeanObject,
    mut v_offset_247_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_248_: *mut LeanObject = core::ptr::null_mut();
    v___x_248_ = lean_nat_sub(v_p_246_, v_offset_247_);
    return v___x_248_;
}
pub unsafe fn l_String_Pos_Raw_unoffsetBy___boxed(
    mut v_p_249_: *mut LeanObject,
    mut v_offset_250_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_251_: *mut LeanObject = core::ptr::null_mut();
    v_res_251_ = l_String_Pos_Raw_unoffsetBy(v_p_249_, v_offset_250_);
    lean_dec(v_offset_250_);
    lean_dec(v_p_249_);
    return v_res_251_;
}
pub unsafe fn l_String_Pos_Raw_increaseBy(
    mut v_p_252_: *mut LeanObject,
    mut v_n_253_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_254_: *mut LeanObject = core::ptr::null_mut();
    v___x_254_ = lean_nat_add(v_p_252_, v_n_253_);
    return v___x_254_;
}
pub unsafe fn l_String_Pos_Raw_increaseBy___boxed(
    mut v_p_255_: *mut LeanObject,
    mut v_n_256_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_257_: *mut LeanObject = core::ptr::null_mut();
    v_res_257_ = l_String_Pos_Raw_increaseBy(v_p_255_, v_n_256_);
    lean_dec(v_n_256_);
    lean_dec(v_p_255_);
    return v_res_257_;
}
pub unsafe fn l_String_Pos_Raw_decreaseBy(
    mut v_p_258_: *mut LeanObject,
    mut v_n_259_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_260_: *mut LeanObject = core::ptr::null_mut();
    v___x_260_ = lean_nat_sub(v_p_258_, v_n_259_);
    return v___x_260_;
}
pub unsafe fn l_String_Pos_Raw_decreaseBy___boxed(
    mut v_p_261_: *mut LeanObject,
    mut v_n_262_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_263_: *mut LeanObject = core::ptr::null_mut();
    v_res_263_ = l_String_Pos_Raw_decreaseBy(v_p_261_, v_n_262_);
    lean_dec(v_n_262_);
    lean_dec(v_p_261_);
    return v_res_263_;
}
pub unsafe fn l_String_Pos_Raw_inc(mut v_p_264_: *mut LeanObject) -> *mut LeanObject {
    let mut v___x_265_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_266_: *mut LeanObject = core::ptr::null_mut();
    v___x_265_ = lean_unsigned_to_nat(1);
    v___x_266_ = lean_nat_add(v_p_264_, v___x_265_);
    return v___x_266_;
}
pub unsafe fn l_String_Pos_Raw_inc___boxed(mut v_p_267_: *mut LeanObject) -> *mut LeanObject {
    let mut v_res_268_: *mut LeanObject = core::ptr::null_mut();
    v_res_268_ = l_String_Pos_Raw_inc(v_p_267_);
    lean_dec(v_p_267_);
    return v_res_268_;
}
pub unsafe fn l_String_Pos_Raw_dec(mut v_p_269_: *mut LeanObject) -> *mut LeanObject {
    let mut v___x_270_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_271_: *mut LeanObject = core::ptr::null_mut();
    v___x_270_ = lean_unsigned_to_nat(1);
    v___x_271_ = lean_nat_sub(v_p_269_, v___x_270_);
    return v___x_271_;
}
pub unsafe fn l_String_Pos_Raw_dec___boxed(mut v_p_272_: *mut LeanObject) -> *mut LeanObject {
    let mut v_res_273_: *mut LeanObject = core::ptr::null_mut();
    v_res_273_ = l_String_Pos_Raw_dec(v_p_272_);
    lean_dec(v_p_272_);
    return v_res_273_;
}
pub unsafe fn l_String_Pos_Raw_min(
    mut v_p_u2081_274_: *mut LeanObject,
    mut v_p_u2082_275_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_276_: u8 = 0;
    v___x_276_ = lean_nat_dec_le(v_p_u2081_274_, v_p_u2082_275_);
    if v___x_276_ == 0 {
        lean_inc(v_p_u2082_275_);
        return v_p_u2082_275_;
    } else {
        lean_inc(v_p_u2081_274_);
        return v_p_u2081_274_;
    }
}
pub unsafe fn l_String_Pos_Raw_min___boxed(
    mut v_p_u2081_277_: *mut LeanObject,
    mut v_p_u2082_278_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_279_: *mut LeanObject = core::ptr::null_mut();
    v_res_279_ = l_String_Pos_Raw_min(v_p_u2081_277_, v_p_u2082_278_);
    lean_dec(v_p_u2082_278_);
    lean_dec(v_p_u2081_277_);
    return v_res_279_;
}
pub unsafe fn lean_string_pos_min(
    mut v_p_u2081_280_: *mut LeanObject,
    mut v_p_u2082_281_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_282_: u8 = 0;
    v___x_282_ = lean_nat_dec_le(v_p_u2081_280_, v_p_u2082_281_);
    if v___x_282_ == 0 {
        lean_dec(v_p_u2081_280_);
        return v_p_u2082_281_;
    } else {
        lean_dec(v_p_u2082_281_);
        return v_p_u2081_280_;
    }
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Init_Data_String_PosRaw(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Init_Data_ByteArray_Basic(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Nat_Simproc(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Omega(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    l_String_instLERaw = _init_l_String_instLERaw();
    lean_mark_persistent(l_String_instLERaw);
    l_String_instLTRaw = _init_l_String_instLTRaw();
    lean_mark_persistent(l_String_instLTRaw);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Init_Data_String_PosRaw(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_meta_initialized = true;
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Init_Data_String_PosRaw(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Init_Data_ByteArray_Basic(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Data_Nat_Simproc(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Omega(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_String_PosRaw(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Init_Data_String_PosRaw(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Init_Data_String_PosRaw(builtin);
}
