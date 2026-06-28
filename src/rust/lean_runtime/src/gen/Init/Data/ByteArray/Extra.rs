// Lean compiler output
// Module: Init.Data.ByteArray.Extra
// Imports: Init.Data.ByteArray.Basic Init.Data.String.Defs Init.Data.UInt.Basic
use crate::r#gen::Init::Data::ByteArray::Basic::{
    initialize_Init_Data_ByteArray_Basic, runtime_initialize_Init_Data_ByteArray_Basic,
};
use crate::r#gen::Init::Data::String::Defs::{
    initialize_Init_Data_String_Defs, runtime_initialize_Init_Data_String_Defs,
};
use crate::r#gen::Init::Data::UInt::Basic::{
    initialize_Init_Data_UInt_Basic, runtime_initialize_Init_Data_UInt_Basic,
};
use crate::r#gen::Init::Prelude::l_instInhabitedUInt64;
use crate::r#gen::Init::Util::l_mkPanicMessageWithDecl;
use crate::lean_imports_rs::Init::Data::ByteArray::Basic::lean_byte_array_get;
use crate::lean_imports_rs::Init::Data::UInt::Basic::{lean_uint64_lor, lean_uint64_shift_left};
use crate::lean_imports_rs::Init::Data::UInt::BasicAux::lean_uint8_to_uint64;
use crate::lean_imports_rs::Init::Prelude::{
    lean_byte_array_size, lean_nat_dec_eq, lean_panic_fn_borrowed,
};
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_box, lean_box_uint64, lean_dec, lean_dec_ref,
    lean_io_result_is_error, lean_io_result_mk_ok, lean_mark_persistent, lean_obj_once,
    lean_unbox_uint64, lean_unsigned_to_nat,
};
pub static mut l_panic___at___00ByteArray_toUInt64LE_x21_spec__0___boxed__const__1:
    *mut LeanObject = core::ptr::null_mut();
pub static l_ByteArray_toUInt64LE_x21___closed__0_value: LeanStringObject<26> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 26,
    m_capacity: 26,
    m_length: 25,
    m_data: [
        73, 110, 105, 116, 46, 68, 97, 116, 97, 46, 66, 121, 116, 101, 65, 114, 114, 97, 121, 46,
        69, 120, 116, 114, 97, 0,
    ],
};
static mut l_ByteArray_toUInt64LE_x21___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_ByteArray_toUInt64LE_x21___closed__0_value) as *mut LeanObject;
pub static l_ByteArray_toUInt64LE_x21___closed__1_value: LeanStringObject<22> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 22,
    m_capacity: 22,
    m_length: 21,
    m_data: [
        66, 121, 116, 101, 65, 114, 114, 97, 121, 46, 116, 111, 85, 73, 110, 116, 54, 52, 76, 69,
        33, 0,
    ],
};
static mut l_ByteArray_toUInt64LE_x21___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_ByteArray_toUInt64LE_x21___closed__1_value) as *mut LeanObject;
pub static l_ByteArray_toUInt64LE_x21___closed__2_value: LeanStringObject<37> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 37,
    m_capacity: 37,
    m_length: 36,
    m_data: [
        97, 115, 115, 101, 114, 116, 105, 111, 110, 32, 118, 105, 111, 108, 97, 116, 105, 111, 110,
        58, 32, 98, 115, 46, 115, 105, 122, 101, 32, 61, 61, 32, 56, 10, 32, 32, 0,
    ],
};
static mut l_ByteArray_toUInt64LE_x21___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_ByteArray_toUInt64LE_x21___closed__2_value) as *mut LeanObject;
static mut l_ByteArray_toUInt64LE_x21___closed__3_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_ByteArray_toUInt64LE_x21___closed__3: *mut LeanObject = core::ptr::null_mut();
pub static l_ByteArray_toUInt64BE_x21___closed__0_value: LeanStringObject<22> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 22,
    m_capacity: 22,
    m_length: 21,
    m_data: [
        66, 121, 116, 101, 65, 114, 114, 97, 121, 46, 116, 111, 85, 73, 110, 116, 54, 52, 66, 69,
        33, 0,
    ],
};
static mut l_ByteArray_toUInt64BE_x21___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_ByteArray_toUInt64BE_x21___closed__0_value) as *mut LeanObject;
static mut l_ByteArray_toUInt64BE_x21___closed__1_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_ByteArray_toUInt64BE_x21___closed__1: *mut LeanObject = core::ptr::null_mut();
pub unsafe fn _init_l_panic___at___00ByteArray_toUInt64LE_x21_spec__0___boxed__const__1()
-> *mut LeanObject {
    let mut v___x_134_: u64 = 0;
    let mut v___x_135_: *mut LeanObject = core::ptr::null_mut();
    v___x_134_ = l_instInhabitedUInt64;
    v___x_135_ = lean_box_uint64(v___x_134_);
    return v___x_135_;
}
pub unsafe fn l_panic___at___00ByteArray_toUInt64LE_x21_spec__0(
    mut v_msg_136_: *mut LeanObject,
) -> u64 {
    let mut v___x_137_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_138_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_139_: u64 = 0;
    v___x_137_ = l_panic___at___00ByteArray_toUInt64LE_x21_spec__0___boxed__const__1;
    v___x_138_ = lean_panic_fn_borrowed(v___x_137_, v_msg_136_);
    v___x_139_ = lean_unbox_uint64(v___x_138_);
    lean_dec(v___x_138_);
    return v___x_139_;
}
pub unsafe fn l_panic___at___00ByteArray_toUInt64LE_x21_spec__0___boxed(
    mut v_msg_140_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_141_: u64 = 0;
    let mut v_r_142_: *mut LeanObject = core::ptr::null_mut();
    v_res_141_ = l_panic___at___00ByteArray_toUInt64LE_x21_spec__0(v_msg_140_);
    v_r_142_ = lean_box_uint64(v_res_141_);
    return v_r_142_;
}
pub unsafe fn _init_l_ByteArray_toUInt64LE_x21___closed__3() -> *mut LeanObject {
    let mut v___x_146_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_147_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_148_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_149_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_150_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_151_: *mut LeanObject = core::ptr::null_mut();
    v___x_146_ = l_ByteArray_toUInt64LE_x21___closed__2;
    v___x_147_ = lean_unsigned_to_nat(2);
    v___x_148_ = lean_unsigned_to_nat(21);
    v___x_149_ = l_ByteArray_toUInt64LE_x21___closed__1;
    v___x_150_ = l_ByteArray_toUInt64LE_x21___closed__0;
    v___x_151_ =
        l_mkPanicMessageWithDecl(v___x_150_, v___x_149_, v___x_148_, v___x_147_, v___x_146_);
    return v___x_151_;
}
pub unsafe fn l_ByteArray_toUInt64LE_x21(mut v_bs_152_: *mut LeanObject) -> u64 {
    let mut v___x_153_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_154_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_155_: u8 = 0;
    v___x_153_ = lean_byte_array_size(v_bs_152_);
    v___x_154_ = lean_unsigned_to_nat(8);
    v___x_155_ = lean_nat_dec_eq(v___x_153_, v___x_154_);
    if v___x_155_ == 0 {
        let mut v___x_156_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_157_: u64 = 0;
        v___x_156_ = lean_obj_once(
            core::ptr::addr_of_mut!(l_ByteArray_toUInt64LE_x21___closed__3),
            core::ptr::addr_of_mut!(l_ByteArray_toUInt64LE_x21___closed__3_once),
            _init_l_ByteArray_toUInt64LE_x21___closed__3,
        );
        v___x_157_ = l_panic___at___00ByteArray_toUInt64LE_x21_spec__0(v___x_156_);
        return v___x_157_;
    } else {
        let mut v___x_158_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_159_: u8 = 0;
        let mut v___x_160_: u64 = 0;
        let mut v___x_161_: u64 = 0;
        let mut v___x_162_: u64 = 0;
        let mut v___x_163_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_164_: u8 = 0;
        let mut v___x_165_: u64 = 0;
        let mut v___x_166_: u64 = 0;
        let mut v___x_167_: u64 = 0;
        let mut v___x_168_: u64 = 0;
        let mut v___x_169_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_170_: u8 = 0;
        let mut v___x_171_: u64 = 0;
        let mut v___x_172_: u64 = 0;
        let mut v___x_173_: u64 = 0;
        let mut v___x_174_: u64 = 0;
        let mut v___x_175_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_176_: u8 = 0;
        let mut v___x_177_: u64 = 0;
        let mut v___x_178_: u64 = 0;
        let mut v___x_179_: u64 = 0;
        let mut v___x_180_: u64 = 0;
        let mut v___x_181_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_182_: u8 = 0;
        let mut v___x_183_: u64 = 0;
        let mut v___x_184_: u64 = 0;
        let mut v___x_185_: u64 = 0;
        let mut v___x_186_: u64 = 0;
        let mut v___x_187_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_188_: u8 = 0;
        let mut v___x_189_: u64 = 0;
        let mut v___x_190_: u64 = 0;
        let mut v___x_191_: u64 = 0;
        let mut v___x_192_: u64 = 0;
        let mut v___x_193_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_194_: u8 = 0;
        let mut v___x_195_: u64 = 0;
        let mut v___x_196_: u64 = 0;
        let mut v___x_197_: u64 = 0;
        let mut v___x_198_: u64 = 0;
        let mut v___x_199_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_200_: u8 = 0;
        let mut v___x_201_: u64 = 0;
        let mut v___x_202_: u64 = 0;
        v___x_158_ = lean_unsigned_to_nat(7);
        v___x_159_ = lean_byte_array_get(v_bs_152_, v___x_158_);
        v___x_160_ = lean_uint8_to_uint64(v___x_159_);
        v___x_161_ = 56u64;
        v___x_162_ = lean_uint64_shift_left(v___x_160_, v___x_161_);
        v___x_163_ = lean_unsigned_to_nat(6);
        v___x_164_ = lean_byte_array_get(v_bs_152_, v___x_163_);
        v___x_165_ = lean_uint8_to_uint64(v___x_164_);
        v___x_166_ = 48u64;
        v___x_167_ = lean_uint64_shift_left(v___x_165_, v___x_166_);
        v___x_168_ = lean_uint64_lor(v___x_162_, v___x_167_);
        v___x_169_ = lean_unsigned_to_nat(5);
        v___x_170_ = lean_byte_array_get(v_bs_152_, v___x_169_);
        v___x_171_ = lean_uint8_to_uint64(v___x_170_);
        v___x_172_ = 40u64;
        v___x_173_ = lean_uint64_shift_left(v___x_171_, v___x_172_);
        v___x_174_ = lean_uint64_lor(v___x_168_, v___x_173_);
        v___x_175_ = lean_unsigned_to_nat(4);
        v___x_176_ = lean_byte_array_get(v_bs_152_, v___x_175_);
        v___x_177_ = lean_uint8_to_uint64(v___x_176_);
        v___x_178_ = 32u64;
        v___x_179_ = lean_uint64_shift_left(v___x_177_, v___x_178_);
        v___x_180_ = lean_uint64_lor(v___x_174_, v___x_179_);
        v___x_181_ = lean_unsigned_to_nat(3);
        v___x_182_ = lean_byte_array_get(v_bs_152_, v___x_181_);
        v___x_183_ = lean_uint8_to_uint64(v___x_182_);
        v___x_184_ = 24u64;
        v___x_185_ = lean_uint64_shift_left(v___x_183_, v___x_184_);
        v___x_186_ = lean_uint64_lor(v___x_180_, v___x_185_);
        v___x_187_ = lean_unsigned_to_nat(2);
        v___x_188_ = lean_byte_array_get(v_bs_152_, v___x_187_);
        v___x_189_ = lean_uint8_to_uint64(v___x_188_);
        v___x_190_ = 16u64;
        v___x_191_ = lean_uint64_shift_left(v___x_189_, v___x_190_);
        v___x_192_ = lean_uint64_lor(v___x_186_, v___x_191_);
        v___x_193_ = lean_unsigned_to_nat(1);
        v___x_194_ = lean_byte_array_get(v_bs_152_, v___x_193_);
        v___x_195_ = lean_uint8_to_uint64(v___x_194_);
        v___x_196_ = 8u64;
        v___x_197_ = lean_uint64_shift_left(v___x_195_, v___x_196_);
        v___x_198_ = lean_uint64_lor(v___x_192_, v___x_197_);
        v___x_199_ = lean_unsigned_to_nat(0);
        v___x_200_ = lean_byte_array_get(v_bs_152_, v___x_199_);
        v___x_201_ = lean_uint8_to_uint64(v___x_200_);
        v___x_202_ = lean_uint64_lor(v___x_198_, v___x_201_);
        return v___x_202_;
    }
}
pub unsafe fn l_ByteArray_toUInt64LE_x21___boxed(
    mut v_bs_203_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_204_: u64 = 0;
    let mut v_r_205_: *mut LeanObject = core::ptr::null_mut();
    v_res_204_ = l_ByteArray_toUInt64LE_x21(v_bs_203_);
    lean_dec_ref(v_bs_203_);
    v_r_205_ = lean_box_uint64(v_res_204_);
    return v_r_205_;
}
pub unsafe fn _init_l_ByteArray_toUInt64BE_x21___closed__1() -> *mut LeanObject {
    let mut v___x_207_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_208_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_209_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_210_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_211_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_212_: *mut LeanObject = core::ptr::null_mut();
    v___x_207_ = l_ByteArray_toUInt64LE_x21___closed__2;
    v___x_208_ = lean_unsigned_to_nat(2);
    v___x_209_ = lean_unsigned_to_nat(37);
    v___x_210_ = l_ByteArray_toUInt64BE_x21___closed__0;
    v___x_211_ = l_ByteArray_toUInt64LE_x21___closed__0;
    v___x_212_ =
        l_mkPanicMessageWithDecl(v___x_211_, v___x_210_, v___x_209_, v___x_208_, v___x_207_);
    return v___x_212_;
}
pub unsafe fn l_ByteArray_toUInt64BE_x21(mut v_bs_213_: *mut LeanObject) -> u64 {
    let mut v___x_214_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_215_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_216_: u8 = 0;
    v___x_214_ = lean_byte_array_size(v_bs_213_);
    v___x_215_ = lean_unsigned_to_nat(8);
    v___x_216_ = lean_nat_dec_eq(v___x_214_, v___x_215_);
    if v___x_216_ == 0 {
        let mut v___x_217_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_218_: u64 = 0;
        v___x_217_ = lean_obj_once(
            core::ptr::addr_of_mut!(l_ByteArray_toUInt64BE_x21___closed__1),
            core::ptr::addr_of_mut!(l_ByteArray_toUInt64BE_x21___closed__1_once),
            _init_l_ByteArray_toUInt64BE_x21___closed__1,
        );
        v___x_218_ = l_panic___at___00ByteArray_toUInt64LE_x21_spec__0(v___x_217_);
        return v___x_218_;
    } else {
        let mut v___x_219_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_220_: u8 = 0;
        let mut v___x_221_: u64 = 0;
        let mut v___x_222_: u64 = 0;
        let mut v___x_223_: u64 = 0;
        let mut v___x_224_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_225_: u8 = 0;
        let mut v___x_226_: u64 = 0;
        let mut v___x_227_: u64 = 0;
        let mut v___x_228_: u64 = 0;
        let mut v___x_229_: u64 = 0;
        let mut v___x_230_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_231_: u8 = 0;
        let mut v___x_232_: u64 = 0;
        let mut v___x_233_: u64 = 0;
        let mut v___x_234_: u64 = 0;
        let mut v___x_235_: u64 = 0;
        let mut v___x_236_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_237_: u8 = 0;
        let mut v___x_238_: u64 = 0;
        let mut v___x_239_: u64 = 0;
        let mut v___x_240_: u64 = 0;
        let mut v___x_241_: u64 = 0;
        let mut v___x_242_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_243_: u8 = 0;
        let mut v___x_244_: u64 = 0;
        let mut v___x_245_: u64 = 0;
        let mut v___x_246_: u64 = 0;
        let mut v___x_247_: u64 = 0;
        let mut v___x_248_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_249_: u8 = 0;
        let mut v___x_250_: u64 = 0;
        let mut v___x_251_: u64 = 0;
        let mut v___x_252_: u64 = 0;
        let mut v___x_253_: u64 = 0;
        let mut v___x_254_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_255_: u8 = 0;
        let mut v___x_256_: u64 = 0;
        let mut v___x_257_: u64 = 0;
        let mut v___x_258_: u64 = 0;
        let mut v___x_259_: u64 = 0;
        let mut v___x_260_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_261_: u8 = 0;
        let mut v___x_262_: u64 = 0;
        let mut v___x_263_: u64 = 0;
        v___x_219_ = lean_unsigned_to_nat(0);
        v___x_220_ = lean_byte_array_get(v_bs_213_, v___x_219_);
        v___x_221_ = lean_uint8_to_uint64(v___x_220_);
        v___x_222_ = 56u64;
        v___x_223_ = lean_uint64_shift_left(v___x_221_, v___x_222_);
        v___x_224_ = lean_unsigned_to_nat(1);
        v___x_225_ = lean_byte_array_get(v_bs_213_, v___x_224_);
        v___x_226_ = lean_uint8_to_uint64(v___x_225_);
        v___x_227_ = 48u64;
        v___x_228_ = lean_uint64_shift_left(v___x_226_, v___x_227_);
        v___x_229_ = lean_uint64_lor(v___x_223_, v___x_228_);
        v___x_230_ = lean_unsigned_to_nat(2);
        v___x_231_ = lean_byte_array_get(v_bs_213_, v___x_230_);
        v___x_232_ = lean_uint8_to_uint64(v___x_231_);
        v___x_233_ = 40u64;
        v___x_234_ = lean_uint64_shift_left(v___x_232_, v___x_233_);
        v___x_235_ = lean_uint64_lor(v___x_229_, v___x_234_);
        v___x_236_ = lean_unsigned_to_nat(3);
        v___x_237_ = lean_byte_array_get(v_bs_213_, v___x_236_);
        v___x_238_ = lean_uint8_to_uint64(v___x_237_);
        v___x_239_ = 32u64;
        v___x_240_ = lean_uint64_shift_left(v___x_238_, v___x_239_);
        v___x_241_ = lean_uint64_lor(v___x_235_, v___x_240_);
        v___x_242_ = lean_unsigned_to_nat(4);
        v___x_243_ = lean_byte_array_get(v_bs_213_, v___x_242_);
        v___x_244_ = lean_uint8_to_uint64(v___x_243_);
        v___x_245_ = 24u64;
        v___x_246_ = lean_uint64_shift_left(v___x_244_, v___x_245_);
        v___x_247_ = lean_uint64_lor(v___x_241_, v___x_246_);
        v___x_248_ = lean_unsigned_to_nat(5);
        v___x_249_ = lean_byte_array_get(v_bs_213_, v___x_248_);
        v___x_250_ = lean_uint8_to_uint64(v___x_249_);
        v___x_251_ = 16u64;
        v___x_252_ = lean_uint64_shift_left(v___x_250_, v___x_251_);
        v___x_253_ = lean_uint64_lor(v___x_247_, v___x_252_);
        v___x_254_ = lean_unsigned_to_nat(6);
        v___x_255_ = lean_byte_array_get(v_bs_213_, v___x_254_);
        v___x_256_ = lean_uint8_to_uint64(v___x_255_);
        v___x_257_ = 8u64;
        v___x_258_ = lean_uint64_shift_left(v___x_256_, v___x_257_);
        v___x_259_ = lean_uint64_lor(v___x_253_, v___x_258_);
        v___x_260_ = lean_unsigned_to_nat(7);
        v___x_261_ = lean_byte_array_get(v_bs_213_, v___x_260_);
        v___x_262_ = lean_uint8_to_uint64(v___x_261_);
        v___x_263_ = lean_uint64_lor(v___x_259_, v___x_262_);
        return v___x_263_;
    }
}
pub unsafe fn l_ByteArray_toUInt64BE_x21___boxed(
    mut v_bs_264_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_265_: u64 = 0;
    let mut v_r_266_: *mut LeanObject = core::ptr::null_mut();
    v_res_265_ = l_ByteArray_toUInt64BE_x21(v_bs_264_);
    lean_dec_ref(v_bs_264_);
    v_r_266_ = lean_box_uint64(v_res_265_);
    return v_r_266_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Init_Data_ByteArray_Extra(builtin: u8) -> *mut LeanObject {
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
    res = runtime_initialize_Init_Data_String_Defs(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_UInt_Basic(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    l_panic___at___00ByteArray_toUInt64LE_x21_spec__0___boxed__const__1 =
        _init_l_panic___at___00ByteArray_toUInt64LE_x21_spec__0___boxed__const__1();
    lean_mark_persistent(l_panic___at___00ByteArray_toUInt64LE_x21_spec__0___boxed__const__1);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Init_Data_ByteArray_Extra(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_meta_initialized = true;
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Init_Data_ByteArray_Extra(builtin: u8) -> *mut LeanObject {
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
    res = initialize_Init_Data_String_Defs(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Data_UInt_Basic(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_ByteArray_Extra(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Init_Data_ByteArray_Extra(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Init_Data_ByteArray_Extra(builtin);
}
