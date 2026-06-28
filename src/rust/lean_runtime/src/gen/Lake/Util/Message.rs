// Lean compiler output
// Module: Lake.Util.Message
// Imports: Lean.Parser.Basic
use crate::r#gen::Init::Data::String::Basic::l_String_Slice_Pos_get_x3f;
use crate::r#gen::Init::Data::String::FindPos::l_String_Slice_Pos_prev_x3f;
use crate::r#gen::Init::Prelude::{l_Lean_Syntax_getPos_x3f, l_Lean_Syntax_getTailPos_x3f};
use crate::r#gen::Lean::Data::Position::l_Lean_FileMap_toPosition;
use crate::r#gen::Lean::Exception::{l_Lean_Exception_getRef, l_Lean_Exception_toMessageData};
use crate::r#gen::Lean::Message::{
    l_Lean_MessageData_ofFormat, l_Lean_MessageData_toString, l_Lean_MessageLog_toList,
    l_Lean_mkErrorStringWithPos,
};
use crate::r#gen::Lean::Parser::Basic::{
    initialize_Lean_Parser_Basic, runtime_initialize_Lean_Parser_Basic,
};
use crate::r#gen::Lean::Parser::Types::l_Lean_Parser_Error_toString;
use crate::lean_imports_rs::Init::Data::String::Defs::lean_string_append;
use crate::lean_imports_rs::Init::Prelude::{
    lean_nat_dec_eq, lean_string_dec_eq, lean_string_utf8_byte_size, lean_uint32_dec_eq,
};
pub static l_Lake_mkParserErrorMessage___closed__0_value: crate::leanh::LeanStringObject<1> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 1,
        m_capacity: 1,
        m_length: 0,
        m_data: [0],
    };
static mut l_Lake_mkParserErrorMessage___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_mkParserErrorMessage___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_mkMessageStringCore___closed__0_value: crate::leanh::LeanStringObject<2> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 2,
        m_capacity: 2,
        m_length: 1,
        m_data: [10, 0],
    };
static mut l_Lake_mkMessageStringCore___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_mkMessageStringCore___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_mkMessageStringCore___closed__1_value: crate::leanh::LeanStringObject<7> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 7,
        m_capacity: 7,
        m_length: 6,
        m_data: [105, 110, 102, 111, 58, 32, 0],
    };
static mut l_Lake_mkMessageStringCore___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_mkMessageStringCore___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_mkMessageStringCore___closed__2_value: crate::leanh::LeanStringObject<10> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 10,
        m_capacity: 10,
        m_length: 9,
        m_data: [119, 97, 114, 110, 105, 110, 103, 58, 32, 0],
    };
static mut l_Lake_mkMessageStringCore___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_mkMessageStringCore___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_mkMessageStringCore___closed__3_value: crate::leanh::LeanStringObject<8> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 8,
        m_capacity: 8,
        m_length: 7,
        m_data: [101, 114, 114, 111, 114, 58, 32, 0],
    };
static mut l_Lake_mkMessageStringCore___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_mkMessageStringCore___closed__3_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_mkMessageStringCore___closed__4_value: crate::leanh::LeanStringObject<3> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 3,
        m_capacity: 3,
        m_length: 2,
        m_data: [58, 10, 0],
    };
static mut l_Lake_mkMessageStringCore___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_mkMessageStringCore___closed__4_value)
        as *mut crate::leanh::LeanObject;
pub unsafe fn l_Lake_mkParserErrorMessage(
    mut v_ictx_180_: *mut crate::leanh::LeanObject,
    mut v_s_181_: *mut crate::leanh::LeanObject,
    mut v_e_182_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_fileName_183_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fileMap_184_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_pos_185_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_186_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_187_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_188_: u8 = 0;
    let mut v___x_189_: u8 = 0;
    let mut v___x_190_: u8 = 0;
    let mut v___x_191_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_192_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_193_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_194_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_195_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_fileName_183_ = crate::leanh::lean_ctor_get(v_ictx_180_, 1);
    crate::leanh::lean_inc_ref(v_fileName_183_);
    v_fileMap_184_ = crate::leanh::lean_ctor_get(v_ictx_180_, 2);
    crate::leanh::lean_inc_ref(v_fileMap_184_);
    crate::leanh::lean_dec_ref(v_ictx_180_);
    v_pos_185_ = crate::leanh::lean_ctor_get(v_s_181_, 2);
    v___x_186_ = l_Lean_FileMap_toPosition(v_fileMap_184_, v_pos_185_);
    v___x_187_ = crate::leanh::lean_box(0);
    v___x_188_ = 1;
    v___x_189_ = 2;
    v___x_190_ = 0;
    v___x_191_ = l_Lake_mkParserErrorMessage___closed__0;
    v___x_192_ = l_Lean_Parser_Error_toString(v_e_182_);
    v___x_193_ = crate::leanh::lean_alloc_ctor(3, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_193_, 0, v___x_192_);
    v___x_194_ = l_Lean_MessageData_ofFormat(v___x_193_);
    v___x_195_ = crate::leanh::lean_alloc_ctor(0, 5, (3) as u32);
    crate::leanh::lean_ctor_set(v___x_195_, 0, v_fileName_183_);
    crate::leanh::lean_ctor_set(v___x_195_, 1, v___x_186_);
    crate::leanh::lean_ctor_set(v___x_195_, 2, v___x_187_);
    crate::leanh::lean_ctor_set(v___x_195_, 3, v___x_191_);
    crate::leanh::lean_ctor_set(v___x_195_, 4, v___x_194_);
    crate::leanh::lean_ctor_set_uint8(
        v___x_195_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 5) as u32,
        v___x_188_,
    );
    crate::leanh::lean_ctor_set_uint8(
        v___x_195_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 5 + 1) as u32,
        v___x_189_,
    );
    crate::leanh::lean_ctor_set_uint8(
        v___x_195_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 5 + 2) as u32,
        v___x_190_,
    );
    return v___x_195_;
}
pub unsafe fn l_Lake_mkParserErrorMessage___boxed(
    mut v_ictx_196_: *mut crate::leanh::LeanObject,
    mut v_s_197_: *mut crate::leanh::LeanObject,
    mut v_e_198_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_199_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_199_ = l_Lake_mkParserErrorMessage(v_ictx_196_, v_s_197_, v_e_198_);
    crate::leanh::lean_dec_ref(v_s_197_);
    return v_res_199_;
}
pub unsafe fn l_Lake_mkExceptionMessage(
    mut v_ictx_200_: *mut crate::leanh::LeanObject,
    mut v_e_201_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_fileName_202_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fileMap_203_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_204_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_205_: u8 = 0;
    let mut v___y_207_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_208_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_209_: u8 = 0;
    let mut v___x_210_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_211_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_212_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_214_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_215_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_216_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_217_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_218_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_220_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_221_: u8 = 0;
    let mut v___x_222_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_224_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_225_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_226_: u8 = 0;
    let mut v___x_227_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_228_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_229_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_fileName_202_ = crate::leanh::lean_ctor_get(v_ictx_200_, 1);
                crate::leanh::lean_inc_ref(v_fileName_202_);
                v_fileMap_203_ = crate::leanh::lean_ctor_get(v_ictx_200_, 2);
                crate::leanh::lean_inc_ref(v_fileMap_203_);
                crate::leanh::lean_dec_ref(v_ictx_200_);
                v___x_204_ = l_Lean_Exception_getRef(v_e_201_);
                v___x_205_ = 0;
                v___x_227_ = l_Lean_Syntax_getPos_x3f(v___x_204_, v___x_205_);
                if crate::leanh::lean_obj_tag(v___x_227_) == 0 {
                    v___x_228_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___y_214_ = v___x_228_;
                    state = 2;
                    continue;
                } else {
                    v_val_229_ = crate::leanh::lean_ctor_get(v___x_227_, 0);
                    crate::leanh::lean_inc(v_val_229_);
                    crate::leanh::lean_dec_ref_known(v___x_227_, 1);
                    v___y_214_ = v_val_229_;
                    state = 2;
                    continue;
                }
            }
            1 => {
                v___x_209_ = 2;
                v___x_210_ = l_Lake_mkParserErrorMessage___closed__0;
                v___x_211_ = l_Lean_Exception_toMessageData(v_e_201_);
                v___x_212_ = crate::leanh::lean_alloc_ctor(0, 5, (3) as u32);
                crate::leanh::lean_ctor_set(v___x_212_, 0, v_fileName_202_);
                crate::leanh::lean_ctor_set(v___x_212_, 1, v___y_207_);
                crate::leanh::lean_ctor_set(v___x_212_, 2, v___y_208_);
                crate::leanh::lean_ctor_set(v___x_212_, 3, v___x_210_);
                crate::leanh::lean_ctor_set(v___x_212_, 4, v___x_211_);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_212_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 5) as u32,
                    v___x_205_,
                );
                crate::leanh::lean_ctor_set_uint8(
                    v___x_212_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 5 + 1) as u32,
                    v___x_209_,
                );
                crate::leanh::lean_ctor_set_uint8(
                    v___x_212_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 5 + 2) as u32,
                    v___x_205_,
                );
                return v___x_212_;
            }
            2 => {
                crate::leanh::lean_inc_ref(v_fileMap_203_);
                v___x_215_ = l_Lean_FileMap_toPosition(v_fileMap_203_, v___y_214_);
                crate::leanh::lean_dec(v___y_214_);
                v___x_216_ = l_Lean_Syntax_getTailPos_x3f(v___x_204_, v___x_205_);
                crate::leanh::lean_dec(v___x_204_);
                if crate::leanh::lean_obj_tag(v___x_216_) == 0 {
                    crate::leanh::lean_dec_ref(v_fileMap_203_);
                    v___x_217_ = crate::leanh::lean_box(0);
                    v___y_207_ = v___x_215_;
                    v___y_208_ = v___x_217_;
                    state = 1;
                    continue;
                } else {
                    v_val_218_ = crate::leanh::lean_ctor_get(v___x_216_, 0);
                    v_isSharedCheck_226_ = (!crate::leanh::lean_is_exclusive(v___x_216_)) as u8;
                    if v_isSharedCheck_226_ == 0 {
                        v___x_220_ = v___x_216_;
                        v_isShared_221_ = v_isSharedCheck_226_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_val_218_);
                        crate::leanh::lean_dec(v___x_216_);
                        v___x_220_ = crate::leanh::lean_box(0);
                        v_isShared_221_ = v_isSharedCheck_226_;
                        state = 3;
                        continue;
                    }
                }
            }
            3 => {
                v___x_222_ = l_Lean_FileMap_toPosition(v_fileMap_203_, v_val_218_);
                crate::leanh::lean_dec(v_val_218_);
                if v_isShared_221_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_220_, 0, v___x_222_);
                    v___x_224_ = v___x_220_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_225_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_225_, 0, v___x_222_);
                    v___x_224_ = v_reuseFailAlloc_225_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___y_207_ = v___x_215_;
                v___y_208_ = v___x_224_;
                state = 1;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lake_mkMessageNoPos(
    mut v_ictx_230_: *mut crate::leanh::LeanObject,
    mut v_data_231_: *mut crate::leanh::LeanObject,
    mut v_severity_232_: u8,
) -> *mut crate::leanh::LeanObject {
    let mut v_fileName_233_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fileMap_234_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_235_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_236_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_237_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_238_: u8 = 0;
    let mut v___x_239_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_240_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_fileName_233_ = crate::leanh::lean_ctor_get(v_ictx_230_, 1);
    crate::leanh::lean_inc_ref(v_fileName_233_);
    v_fileMap_234_ = crate::leanh::lean_ctor_get(v_ictx_230_, 2);
    crate::leanh::lean_inc_ref(v_fileMap_234_);
    crate::leanh::lean_dec_ref(v_ictx_230_);
    v___x_235_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_236_ = l_Lean_FileMap_toPosition(v_fileMap_234_, v___x_235_);
    v___x_237_ = crate::leanh::lean_box(0);
    v___x_238_ = 0;
    v___x_239_ = l_Lake_mkParserErrorMessage___closed__0;
    v___x_240_ = crate::leanh::lean_alloc_ctor(0, 5, (3) as u32);
    crate::leanh::lean_ctor_set(v___x_240_, 0, v_fileName_233_);
    crate::leanh::lean_ctor_set(v___x_240_, 1, v___x_236_);
    crate::leanh::lean_ctor_set(v___x_240_, 2, v___x_237_);
    crate::leanh::lean_ctor_set(v___x_240_, 3, v___x_239_);
    crate::leanh::lean_ctor_set(v___x_240_, 4, v_data_231_);
    crate::leanh::lean_ctor_set_uint8(
        v___x_240_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 5) as u32,
        v___x_238_,
    );
    crate::leanh::lean_ctor_set_uint8(
        v___x_240_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 5 + 1) as u32,
        v_severity_232_,
    );
    crate::leanh::lean_ctor_set_uint8(
        v___x_240_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 5 + 2) as u32,
        v___x_238_,
    );
    return v___x_240_;
}
pub unsafe fn l_Lake_mkMessageNoPos___boxed(
    mut v_ictx_241_: *mut crate::leanh::LeanObject,
    mut v_data_242_: *mut crate::leanh::LeanObject,
    mut v_severity_243_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_severity_boxed_244_: u8 = 0;
    let mut v_res_245_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_severity_boxed_244_ = (crate::leanh::lean_unbox(v_severity_243_) as u8);
    v_res_245_ = l_Lake_mkMessageNoPos(v_ictx_241_, v_data_242_, v_severity_boxed_244_);
    return v_res_245_;
}
pub unsafe fn l_Lake_mkMessageStringCore(
    mut v_severity_251_: u8,
    mut v_fileName_252_: *mut crate::leanh::LeanObject,
    mut v_caption_253_: *mut crate::leanh::LeanObject,
    mut v_body_254_: *mut crate::leanh::LeanObject,
    mut v_pos_255_: *mut crate::leanh::LeanObject,
    mut v_endPos_x3f_256_: *mut crate::leanh::LeanObject,
    mut v_infoWithPos_257_: u8,
) -> *mut crate::leanh::LeanObject {
    let mut v___y_259_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_260_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_str_261_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_263_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_264_: u8 = 0;
    let mut v___y_266_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_267_: u8 = 0;
    let mut v___y_268_: u32 = 0;
    let mut v___x_269_: u32 = 0;
    let mut v___x_270_: u8 = 0;
    let mut v_str_272_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_273_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_274_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_275_: u8 = 0;
    let mut v___x_276_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_277_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_278_: u32 = 0;
    let mut v_val_279_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_280_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_281_: u32 = 0;
    let mut v_val_282_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_283_: u32 = 0;
    let mut v_str_285_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_286_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_287_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_288_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_str_289_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_290_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_291_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_292_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_str_293_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_294_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_295_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_296_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_str_297_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_298_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_299_: u8 = 0;
    let mut v___x_300_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_301_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_str_302_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_298_ = l_Lake_mkParserErrorMessage___closed__0;
                v___x_299_ = lean_string_dec_eq(v_caption_253_, v___x_298_);
                if v___x_299_ == 0 {
                    v___x_300_ = l_Lake_mkMessageStringCore___closed__4;
                    v___x_301_ = lean_string_append(v_caption_253_, v___x_300_);
                    v_str_302_ = lean_string_append(v___x_301_, v_body_254_);
                    crate::leanh::lean_dec_ref(v_body_254_);
                    v_str_285_ = v_str_302_;
                    state = 5;
                    continue;
                } else {
                    crate::leanh::lean_dec_ref(v_caption_253_);
                    v_str_285_ = v_body_254_;
                    state = 5;
                    continue;
                }
            }
            1 => {
                v___x_260_ = l_Lake_mkMessageStringCore___closed__0;
                v_str_261_ = lean_string_append(v___y_259_, v___x_260_);
                return v_str_261_;
            }
            2 => {
                if v___y_264_ == 0 {
                    return v___y_263_;
                } else {
                    v___y_259_ = v___y_263_;
                    state = 1;
                    continue;
                }
            }
            3 => {
                v___x_269_ = 10;
                v___x_270_ = lean_uint32_dec_eq(v___y_268_, v___x_269_);
                if v___x_270_ == 0 {
                    v___y_259_ = v___y_266_;
                    state = 1;
                    continue;
                } else {
                    v___y_263_ = v___y_266_;
                    v___y_264_ = v___y_267_;
                    state = 2;
                    continue;
                }
            }
            4 => {
                v___x_273_ = lean_string_utf8_byte_size(v_str_272_);
                v___x_274_ = crate::leanh::lean_unsigned_to_nat(0);
                v___x_275_ = lean_nat_dec_eq(v___x_273_, v___x_274_);
                if v___x_275_ == 0 {
                    crate::leanh::lean_inc_ref(v_str_272_);
                    v___x_276_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_276_, 0, v_str_272_);
                    crate::leanh::lean_ctor_set(v___x_276_, 1, v___x_274_);
                    crate::leanh::lean_ctor_set(v___x_276_, 2, v___x_273_);
                    v___x_277_ = l_String_Slice_Pos_prev_x3f(v___x_276_, v___x_273_);
                    if crate::leanh::lean_obj_tag(v___x_277_) == 0 {
                        crate::leanh::lean_dec_ref_known(v___x_276_, 3);
                        v___x_278_ = 65;
                        v___y_266_ = v_str_272_;
                        v___y_267_ = v___x_275_;
                        v___y_268_ = v___x_278_;
                        state = 3;
                        continue;
                    } else {
                        v_val_279_ = crate::leanh::lean_ctor_get(v___x_277_, 0);
                        crate::leanh::lean_inc(v_val_279_);
                        crate::leanh::lean_dec_ref_known(v___x_277_, 1);
                        v___x_280_ = l_String_Slice_Pos_get_x3f(v___x_276_, v_val_279_);
                        crate::leanh::lean_dec(v_val_279_);
                        crate::leanh::lean_dec_ref_known(v___x_276_, 3);
                        if crate::leanh::lean_obj_tag(v___x_280_) == 0 {
                            v___x_281_ = 65;
                            v___y_266_ = v_str_272_;
                            v___y_267_ = v___x_275_;
                            v___y_268_ = v___x_281_;
                            state = 3;
                            continue;
                        } else {
                            v_val_282_ = crate::leanh::lean_ctor_get(v___x_280_, 0);
                            crate::leanh::lean_inc(v_val_282_);
                            crate::leanh::lean_dec_ref_known(v___x_280_, 1);
                            v___x_283_ = crate::leanh::lean_unbox_uint32(v_val_282_);
                            crate::leanh::lean_dec(v_val_282_);
                            v___y_266_ = v_str_272_;
                            v___y_267_ = v___x_275_;
                            v___y_268_ = v___x_283_;
                            state = 3;
                            continue;
                        }
                    }
                } else {
                    v___y_263_ = v_str_272_;
                    v___y_264_ = v___x_275_;
                    state = 2;
                    continue;
                }
            }
            5 => match v_severity_251_ {
                0 => {
                    if v_infoWithPos_257_ == 0 {
                        crate::leanh::lean_dec(v_endPos_x3f_256_);
                        crate::leanh::lean_dec_ref(v_pos_255_);
                        crate::leanh::lean_dec_ref(v_fileName_252_);
                        v_str_272_ = v_str_285_;
                        state = 4;
                        continue;
                    } else {
                        v___x_286_ = l_Lake_mkMessageStringCore___closed__1;
                        v___x_287_ = crate::leanh::lean_box(0);
                        v___x_288_ = l_Lean_mkErrorStringWithPos(
                            v_fileName_252_,
                            v_pos_255_,
                            v___x_286_,
                            v_endPos_x3f_256_,
                            v___x_287_,
                            v___x_287_,
                        );
                        v_str_289_ = lean_string_append(v___x_288_, v_str_285_);
                        crate::leanh::lean_dec_ref(v_str_285_);
                        v_str_272_ = v_str_289_;
                        state = 4;
                        continue;
                    }
                }
                1 => {
                    v___x_290_ = l_Lake_mkMessageStringCore___closed__2;
                    v___x_291_ = crate::leanh::lean_box(0);
                    v___x_292_ = l_Lean_mkErrorStringWithPos(
                        v_fileName_252_,
                        v_pos_255_,
                        v___x_290_,
                        v_endPos_x3f_256_,
                        v___x_291_,
                        v___x_291_,
                    );
                    v_str_293_ = lean_string_append(v___x_292_, v_str_285_);
                    crate::leanh::lean_dec_ref(v_str_285_);
                    v_str_272_ = v_str_293_;
                    state = 4;
                    continue;
                }
                _ => {
                    v___x_294_ = l_Lake_mkMessageStringCore___closed__3;
                    v___x_295_ = crate::leanh::lean_box(0);
                    v___x_296_ = l_Lean_mkErrorStringWithPos(
                        v_fileName_252_,
                        v_pos_255_,
                        v___x_294_,
                        v_endPos_x3f_256_,
                        v___x_295_,
                        v___x_295_,
                    );
                    v_str_297_ = lean_string_append(v___x_296_, v_str_285_);
                    crate::leanh::lean_dec_ref(v_str_285_);
                    v_str_272_ = v_str_297_;
                    state = 4;
                    continue;
                }
            },
            _ => {}
        }
    }
}
pub unsafe fn l_Lake_mkMessageStringCore___boxed(
    mut v_severity_303_: *mut crate::leanh::LeanObject,
    mut v_fileName_304_: *mut crate::leanh::LeanObject,
    mut v_caption_305_: *mut crate::leanh::LeanObject,
    mut v_body_306_: *mut crate::leanh::LeanObject,
    mut v_pos_307_: *mut crate::leanh::LeanObject,
    mut v_endPos_x3f_308_: *mut crate::leanh::LeanObject,
    mut v_infoWithPos_309_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_severity_boxed_310_: u8 = 0;
    let mut v_infoWithPos_boxed_311_: u8 = 0;
    let mut v_res_312_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_severity_boxed_310_ = (crate::leanh::lean_unbox(v_severity_303_) as u8);
    v_infoWithPos_boxed_311_ = (crate::leanh::lean_unbox(v_infoWithPos_309_) as u8);
    v_res_312_ = l_Lake_mkMessageStringCore(
        v_severity_boxed_310_,
        v_fileName_304_,
        v_caption_305_,
        v_body_306_,
        v_pos_307_,
        v_endPos_x3f_308_,
        v_infoWithPos_boxed_311_,
    );
    return v_res_312_;
}
pub unsafe fn l_Lake_mkMessageString(
    mut v_msg_313_: *mut crate::leanh::LeanObject,
    mut v_includeEndPos_314_: u8,
    mut v_infoWithPos_315_: u8,
) -> *mut crate::leanh::LeanObject {
    let mut v___y_318_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fileName_319_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_pos_320_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_severity_321_: u8 = 0;
    let mut v_caption_322_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_data_323_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_324_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_325_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_326_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_endPos_327_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if v_includeEndPos_314_ == 0 {
                    v___x_326_ = crate::leanh::lean_box(0);
                    v___y_318_ = v___x_326_;
                    state = 1;
                    continue;
                } else {
                    v_endPos_327_ = crate::leanh::lean_ctor_get(v_msg_313_, 2);
                    crate::leanh::lean_inc(v_endPos_327_);
                    v___y_318_ = v_endPos_327_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_fileName_319_ = crate::leanh::lean_ctor_get(v_msg_313_, 0);
                crate::leanh::lean_inc_ref(v_fileName_319_);
                v_pos_320_ = crate::leanh::lean_ctor_get(v_msg_313_, 1);
                crate::leanh::lean_inc_ref(v_pos_320_);
                v_severity_321_ = crate::leanh::lean_ctor_get_uint8(
                    v_msg_313_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 5 + 1) as u32,
                );
                v_caption_322_ = crate::leanh::lean_ctor_get(v_msg_313_, 3);
                crate::leanh::lean_inc_ref(v_caption_322_);
                v_data_323_ = crate::leanh::lean_ctor_get(v_msg_313_, 4);
                crate::leanh::lean_inc(v_data_323_);
                crate::leanh::lean_dec_ref(v_msg_313_);
                v___x_324_ = l_Lean_MessageData_toString(v_data_323_);
                v___x_325_ = l_Lake_mkMessageStringCore(
                    v_severity_321_,
                    v_fileName_319_,
                    v_caption_322_,
                    v___x_324_,
                    v_pos_320_,
                    v___y_318_,
                    v_infoWithPos_315_,
                );
                return v___x_325_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lake_mkMessageString___boxed(
    mut v_msg_328_: *mut crate::leanh::LeanObject,
    mut v_includeEndPos_329_: *mut crate::leanh::LeanObject,
    mut v_infoWithPos_330_: *mut crate::leanh::LeanObject,
    mut v_a_331_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_includeEndPos_boxed_332_: u8 = 0;
    let mut v_infoWithPos_boxed_333_: u8 = 0;
    let mut v_res_334_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_includeEndPos_boxed_332_ = (crate::leanh::lean_unbox(v_includeEndPos_329_) as u8);
    v_infoWithPos_boxed_333_ = (crate::leanh::lean_unbox(v_infoWithPos_330_) as u8);
    v_res_334_ = l_Lake_mkMessageString(
        v_msg_328_,
        v_includeEndPos_boxed_332_,
        v_infoWithPos_boxed_333_,
    );
    return v_res_334_;
}
pub unsafe fn l_List_foldlM___at___00Lake_mkMessageLogString_spec__0(
    mut v_x_335_: *mut crate::leanh::LeanObject,
    mut v_x_336_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_head_338_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_339_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_340_: u8 = 0;
    let mut v___x_341_: u8 = 0;
    let mut v___x_342_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_343_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_336_) == 0 {
                    return v_x_335_;
                } else {
                    v_head_338_ = crate::leanh::lean_ctor_get(v_x_336_, 0);
                    crate::leanh::lean_inc(v_head_338_);
                    v_tail_339_ = crate::leanh::lean_ctor_get(v_x_336_, 1);
                    crate::leanh::lean_inc(v_tail_339_);
                    crate::leanh::lean_dec_ref_known(v_x_336_, 2);
                    v___x_340_ = 0;
                    v___x_341_ = 1;
                    v___x_342_ = l_Lake_mkMessageString(v_head_338_, v___x_340_, v___x_341_);
                    v___x_343_ = lean_string_append(v_x_335_, v___x_342_);
                    crate::leanh::lean_dec_ref(v___x_342_);
                    v_x_335_ = v___x_343_;
                    v_x_336_ = v_tail_339_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_foldlM___at___00Lake_mkMessageLogString_spec__0___boxed(
    mut v_x_345_: *mut crate::leanh::LeanObject,
    mut v_x_346_: *mut crate::leanh::LeanObject,
    mut v___y_347_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_348_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_348_ = l_List_foldlM___at___00Lake_mkMessageLogString_spec__0(v_x_345_, v_x_346_);
    return v_res_348_;
}
pub unsafe fn l_Lake_mkMessageLogString(
    mut v_log_349_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_351_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_352_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_353_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_351_ = l_Lake_mkParserErrorMessage___closed__0;
    v___x_352_ = l_Lean_MessageLog_toList(v_log_349_);
    v___x_353_ = l_List_foldlM___at___00Lake_mkMessageLogString_spec__0(v___x_351_, v___x_352_);
    return v___x_353_;
}
pub unsafe fn l_Lake_mkMessageLogString___boxed(
    mut v_log_354_: *mut crate::leanh::LeanObject,
    mut v_a_355_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_356_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_356_ = l_Lake_mkMessageLogString(v_log_354_);
    crate::leanh::lean_dec_ref(v_log_354_);
    return v_res_356_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lake_Util_Message(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Parser_Basic(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lake_Util_Message(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_meta_initialized = true;
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lake_Util_Message(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Parser_Basic(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lake_Util_Message(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Lake_Util_Message(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Lake_Util_Message(builtin);
}
