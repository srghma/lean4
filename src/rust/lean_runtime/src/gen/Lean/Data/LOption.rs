// Lean compiler output
// Module: Lean.Data.LOption
// Imports: Init.Data.String.Basic
use crate::r#gen::Init::Data::String::Basic::{
    initialize_Init_Data_String_Basic, runtime_initialize_Init_Data_String_Basic,
};
use crate::lean_imports_rs::Init::Data::String::Defs::lean_string_append;
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_alloc_closure, lean_alloc_ctor, lean_apply_1,
    lean_apply_2, lean_apply_4, lean_box, lean_closure_set, lean_ctor_get, lean_ctor_set, lean_dec,
    lean_dec_ref, lean_dec_ref_known, lean_inc, lean_inc_ref, lean_io_result_is_error,
    lean_io_result_mk_ok, lean_is_exclusive, lean_obj_tag, lean_unbox, lean_unsigned_to_nat,
};
pub static l_Lean_instToStringLOption___redArg___lam__0___closed__0_value: LeanStringObject<5> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 5,
        m_capacity: 5,
        m_length: 4,
        m_data: [110, 111, 110, 101, 0],
    };
static mut l_Lean_instToStringLOption___redArg___lam__0___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_instToStringLOption___redArg___lam__0___closed__0_value)
        as *mut LeanObject;
pub static l_Lean_instToStringLOption___redArg___lam__0___closed__1_value: LeanStringObject<7> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 7,
        m_capacity: 7,
        m_length: 6,
        m_data: [40, 115, 111, 109, 101, 32, 0],
    };
static mut l_Lean_instToStringLOption___redArg___lam__0___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_instToStringLOption___redArg___lam__0___closed__1_value)
        as *mut LeanObject;
pub static l_Lean_instToStringLOption___redArg___lam__0___closed__2_value: LeanStringObject<2> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 2,
        m_capacity: 2,
        m_length: 1,
        m_data: [41, 0],
    };
static mut l_Lean_instToStringLOption___redArg___lam__0___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_instToStringLOption___redArg___lam__0___closed__2_value)
        as *mut LeanObject;
pub static l_Lean_instToStringLOption___redArg___lam__0___closed__3_value: LeanStringObject<6> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 6,
        m_capacity: 6,
        m_length: 5,
        m_data: [117, 110, 100, 101, 102, 0],
    };
static mut l_Lean_instToStringLOption___redArg___lam__0___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_instToStringLOption___redArg___lam__0___closed__3_value)
        as *mut LeanObject;
pub unsafe fn l_Lean_LOption_ctorIdx___redArg(mut v_x_160_: *mut LeanObject) -> *mut LeanObject {
    match lean_obj_tag(v_x_160_) {
        0 => {
            let mut v___x_161_: *mut LeanObject = core::ptr::null_mut();
            v___x_161_ = lean_unsigned_to_nat(0);
            return v___x_161_;
        }
        1 => {
            let mut v___x_162_: *mut LeanObject = core::ptr::null_mut();
            v___x_162_ = lean_unsigned_to_nat(1);
            return v___x_162_;
        }
        _ => {
            let mut v___x_163_: *mut LeanObject = core::ptr::null_mut();
            v___x_163_ = lean_unsigned_to_nat(2);
            return v___x_163_;
        }
    }
}
pub unsafe fn l_Lean_LOption_ctorIdx___redArg___boxed(
    mut v_x_164_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_165_: *mut LeanObject = core::ptr::null_mut();
    v_res_165_ = l_Lean_LOption_ctorIdx___redArg(v_x_164_);
    lean_dec(v_x_164_);
    return v_res_165_;
}
pub unsafe fn l_Lean_LOption_ctorIdx(
    mut v_00_u03b1_166_: *mut LeanObject,
    mut v_x_167_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_168_: *mut LeanObject = core::ptr::null_mut();
    v___x_168_ = l_Lean_LOption_ctorIdx___redArg(v_x_167_);
    return v___x_168_;
}
pub unsafe fn l_Lean_LOption_ctorIdx___boxed(
    mut v_00_u03b1_169_: *mut LeanObject,
    mut v_x_170_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_171_: *mut LeanObject = core::ptr::null_mut();
    v_res_171_ = l_Lean_LOption_ctorIdx(v_00_u03b1_169_, v_x_170_);
    lean_dec(v_x_170_);
    return v_res_171_;
}
pub unsafe fn l_Lean_LOption_ctorElim___redArg(
    mut v_t_172_: *mut LeanObject,
    mut v_k_173_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_t_172_) == 1 {
        let mut v_a_174_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_175_: *mut LeanObject = core::ptr::null_mut();
        v_a_174_ = lean_ctor_get(v_t_172_, 0);
        lean_inc(v_a_174_);
        lean_dec_ref_known(v_t_172_, 1);
        v___x_175_ = lean_apply_1(v_k_173_, v_a_174_);
        return v___x_175_;
    } else {
        lean_dec(v_t_172_);
        return v_k_173_;
    }
}
pub unsafe fn l_Lean_LOption_ctorElim(
    mut v_00_u03b1_176_: *mut LeanObject,
    mut v_motive_177_: *mut LeanObject,
    mut v_ctorIdx_178_: *mut LeanObject,
    mut v_t_179_: *mut LeanObject,
    mut v_h_180_: *mut LeanObject,
    mut v_k_181_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_182_: *mut LeanObject = core::ptr::null_mut();
    v___x_182_ = l_Lean_LOption_ctorElim___redArg(v_t_179_, v_k_181_);
    return v___x_182_;
}
pub unsafe fn l_Lean_LOption_ctorElim___boxed(
    mut v_00_u03b1_183_: *mut LeanObject,
    mut v_motive_184_: *mut LeanObject,
    mut v_ctorIdx_185_: *mut LeanObject,
    mut v_t_186_: *mut LeanObject,
    mut v_h_187_: *mut LeanObject,
    mut v_k_188_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_189_: *mut LeanObject = core::ptr::null_mut();
    v_res_189_ = l_Lean_LOption_ctorElim(
        v_00_u03b1_183_,
        v_motive_184_,
        v_ctorIdx_185_,
        v_t_186_,
        v_h_187_,
        v_k_188_,
    );
    lean_dec(v_ctorIdx_185_);
    return v_res_189_;
}
pub unsafe fn l_Lean_LOption_none_elim___redArg(
    mut v_t_190_: *mut LeanObject,
    mut v_none_191_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_192_: *mut LeanObject = core::ptr::null_mut();
    v___x_192_ = l_Lean_LOption_ctorElim___redArg(v_t_190_, v_none_191_);
    return v___x_192_;
}
pub unsafe fn l_Lean_LOption_none_elim(
    mut v_00_u03b1_193_: *mut LeanObject,
    mut v_motive_194_: *mut LeanObject,
    mut v_t_195_: *mut LeanObject,
    mut v_h_196_: *mut LeanObject,
    mut v_none_197_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_198_: *mut LeanObject = core::ptr::null_mut();
    v___x_198_ = l_Lean_LOption_ctorElim___redArg(v_t_195_, v_none_197_);
    return v___x_198_;
}
pub unsafe fn l_Lean_LOption_some_elim___redArg(
    mut v_t_199_: *mut LeanObject,
    mut v_some_200_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_201_: *mut LeanObject = core::ptr::null_mut();
    v___x_201_ = l_Lean_LOption_ctorElim___redArg(v_t_199_, v_some_200_);
    return v___x_201_;
}
pub unsafe fn l_Lean_LOption_some_elim(
    mut v_00_u03b1_202_: *mut LeanObject,
    mut v_motive_203_: *mut LeanObject,
    mut v_t_204_: *mut LeanObject,
    mut v_h_205_: *mut LeanObject,
    mut v_some_206_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_207_: *mut LeanObject = core::ptr::null_mut();
    v___x_207_ = l_Lean_LOption_ctorElim___redArg(v_t_204_, v_some_206_);
    return v___x_207_;
}
pub unsafe fn l_Lean_LOption_undef_elim___redArg(
    mut v_t_208_: *mut LeanObject,
    mut v_undef_209_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_210_: *mut LeanObject = core::ptr::null_mut();
    v___x_210_ = l_Lean_LOption_ctorElim___redArg(v_t_208_, v_undef_209_);
    return v___x_210_;
}
pub unsafe fn l_Lean_LOption_undef_elim(
    mut v_00_u03b1_211_: *mut LeanObject,
    mut v_motive_212_: *mut LeanObject,
    mut v_t_213_: *mut LeanObject,
    mut v_h_214_: *mut LeanObject,
    mut v_undef_215_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_216_: *mut LeanObject = core::ptr::null_mut();
    v___x_216_ = l_Lean_LOption_ctorElim___redArg(v_t_213_, v_undef_215_);
    return v___x_216_;
}
pub unsafe fn l_Lean_instInhabitedLOption_default(
    mut v_00_u03b1_217_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_218_: *mut LeanObject = core::ptr::null_mut();
    v___x_218_ = lean_box(0);
    return v___x_218_;
}
pub unsafe fn l_Lean_instInhabitedLOption(mut v_a_219_: *mut LeanObject) -> *mut LeanObject {
    let mut v___x_220_: *mut LeanObject = core::ptr::null_mut();
    v___x_220_ = lean_box(0);
    return v___x_220_;
}
pub unsafe fn l_Lean_instBEqLOption_beq___redArg(
    mut v_inst_221_: *mut LeanObject,
    mut v_x_222_: *mut LeanObject,
    mut v_x_223_: *mut LeanObject,
) -> u8 {
    match lean_obj_tag(v_x_222_) {
        0 => {
            lean_dec_ref(v_inst_221_);
            if lean_obj_tag(v_x_223_) == 0 {
                let mut v___x_224_: u8 = 0;
                v___x_224_ = 1;
                return v___x_224_;
            } else {
                let mut v___x_225_: u8 = 0;
                lean_dec(v_x_223_);
                v___x_225_ = 0;
                return v___x_225_;
            }
        }
        1 => {
            if lean_obj_tag(v_x_223_) == 1 {
                let mut v_a_226_: *mut LeanObject = core::ptr::null_mut();
                let mut v_a_227_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_228_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_229_: u8 = 0;
                v_a_226_ = lean_ctor_get(v_x_222_, 0);
                lean_inc(v_a_226_);
                lean_dec_ref_known(v_x_222_, 1);
                v_a_227_ = lean_ctor_get(v_x_223_, 0);
                lean_inc(v_a_227_);
                lean_dec_ref_known(v_x_223_, 1);
                v___x_228_ = lean_apply_2(v_inst_221_, v_a_226_, v_a_227_);
                v___x_229_ = (lean_unbox(v___x_228_) as u8);
                return v___x_229_;
            } else {
                let mut v___x_230_: u8 = 0;
                lean_dec_ref_known(v_x_222_, 1);
                lean_dec(v_x_223_);
                lean_dec_ref(v_inst_221_);
                v___x_230_ = 0;
                return v___x_230_;
            }
        }
        _ => {
            lean_dec_ref(v_inst_221_);
            if lean_obj_tag(v_x_223_) == 2 {
                let mut v___x_231_: u8 = 0;
                v___x_231_ = 1;
                return v___x_231_;
            } else {
                let mut v___x_232_: u8 = 0;
                lean_dec(v_x_223_);
                v___x_232_ = 0;
                return v___x_232_;
            }
        }
    }
}
pub unsafe fn l_Lean_instBEqLOption_beq___redArg___boxed(
    mut v_inst_233_: *mut LeanObject,
    mut v_x_234_: *mut LeanObject,
    mut v_x_235_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_236_: u8 = 0;
    let mut v_r_237_: *mut LeanObject = core::ptr::null_mut();
    v_res_236_ = l_Lean_instBEqLOption_beq___redArg(v_inst_233_, v_x_234_, v_x_235_);
    v_r_237_ = lean_box((v_res_236_) as usize);
    return v_r_237_;
}
pub unsafe fn l_Lean_instBEqLOption_beq(
    mut v_00_u03b1_238_: *mut LeanObject,
    mut v_inst_239_: *mut LeanObject,
    mut v_x_240_: *mut LeanObject,
    mut v_x_241_: *mut LeanObject,
) -> u8 {
    let mut v___x_242_: u8 = 0;
    v___x_242_ = l_Lean_instBEqLOption_beq___redArg(v_inst_239_, v_x_240_, v_x_241_);
    return v___x_242_;
}
pub unsafe fn l_Lean_instBEqLOption_beq___boxed(
    mut v_00_u03b1_243_: *mut LeanObject,
    mut v_inst_244_: *mut LeanObject,
    mut v_x_245_: *mut LeanObject,
    mut v_x_246_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_247_: u8 = 0;
    let mut v_r_248_: *mut LeanObject = core::ptr::null_mut();
    v_res_247_ = l_Lean_instBEqLOption_beq(v_00_u03b1_243_, v_inst_244_, v_x_245_, v_x_246_);
    v_r_248_ = lean_box((v_res_247_) as usize);
    return v_r_248_;
}
pub unsafe fn l_Lean_instBEqLOption___redArg(mut v_inst_249_: *mut LeanObject) -> *mut LeanObject {
    let mut v___x_250_: *mut LeanObject = core::ptr::null_mut();
    v___x_250_ = lean_alloc_closure(
        l_Lean_instBEqLOption_beq___boxed as *mut core::ffi::c_void,
        4,
        2,
    );
    lean_closure_set(v___x_250_, 0, lean_box(0));
    lean_closure_set(v___x_250_, 1, v_inst_249_);
    return v___x_250_;
}
pub unsafe fn l_Lean_instBEqLOption(
    mut v_00_u03b1_251_: *mut LeanObject,
    mut v_inst_252_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_253_: *mut LeanObject = core::ptr::null_mut();
    v___x_253_ = lean_alloc_closure(
        l_Lean_instBEqLOption_beq___boxed as *mut core::ffi::c_void,
        4,
        2,
    );
    lean_closure_set(v___x_253_, 0, lean_box(0));
    lean_closure_set(v___x_253_, 1, v_inst_252_);
    return v___x_253_;
}
pub unsafe fn l_Lean_instToStringLOption___redArg___lam__0(
    mut v_inst_258_: *mut LeanObject,
    mut v_x_259_: *mut LeanObject,
) -> *mut LeanObject {
    match lean_obj_tag(v_x_259_) {
        0 => {
            let mut v___x_260_: *mut LeanObject = core::ptr::null_mut();
            lean_dec_ref(v_inst_258_);
            v___x_260_ = l_Lean_instToStringLOption___redArg___lam__0___closed__0;
            return v___x_260_;
        }
        1 => {
            let mut v_a_261_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_262_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_263_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_264_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_265_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_266_: *mut LeanObject = core::ptr::null_mut();
            v_a_261_ = lean_ctor_get(v_x_259_, 0);
            lean_inc(v_a_261_);
            lean_dec_ref_known(v_x_259_, 1);
            v___x_262_ = l_Lean_instToStringLOption___redArg___lam__0___closed__1;
            v___x_263_ = lean_apply_1(v_inst_258_, v_a_261_);
            v___x_264_ = lean_string_append(v___x_262_, v___x_263_);
            lean_dec_ref(v___x_263_);
            v___x_265_ = l_Lean_instToStringLOption___redArg___lam__0___closed__2;
            v___x_266_ = lean_string_append(v___x_264_, v___x_265_);
            return v___x_266_;
        }
        _ => {
            let mut v___x_267_: *mut LeanObject = core::ptr::null_mut();
            lean_dec_ref(v_inst_258_);
            v___x_267_ = l_Lean_instToStringLOption___redArg___lam__0___closed__3;
            return v___x_267_;
        }
    }
}
pub unsafe fn l_Lean_instToStringLOption___redArg(
    mut v_inst_268_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_269_: *mut LeanObject = core::ptr::null_mut();
    v___f_269_ = lean_alloc_closure(
        l_Lean_instToStringLOption___redArg___lam__0 as *mut core::ffi::c_void,
        2,
        1,
    );
    lean_closure_set(v___f_269_, 0, v_inst_268_);
    return v___f_269_;
}
pub unsafe fn l_Lean_instToStringLOption(
    mut v_00_u03b1_270_: *mut LeanObject,
    mut v_inst_271_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_272_: *mut LeanObject = core::ptr::null_mut();
    v___f_272_ = lean_alloc_closure(
        l_Lean_instToStringLOption___redArg___lam__0 as *mut core::ffi::c_void,
        2,
        1,
    );
    lean_closure_set(v___f_272_, 0, v_inst_271_);
    return v___f_272_;
}
pub unsafe fn l_Lean_LOption_toOption___redArg(mut v_x_273_: *mut LeanObject) -> *mut LeanObject {
    let mut v_a_274_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_276_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_277_: u8 = 0;
    let mut v___x_279_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_280_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_281_: u8 = 0;
    let mut v___x_282_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_273_) == 1 {
                    v_a_274_ = lean_ctor_get(v_x_273_, 0);
                    v_isSharedCheck_281_ = (!lean_is_exclusive(v_x_273_)) as u8;
                    if v_isSharedCheck_281_ == 0 {
                        v___x_276_ = v_x_273_;
                        v_isShared_277_ = v_isSharedCheck_281_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_274_);
                        lean_dec(v_x_273_);
                        v___x_276_ = lean_box(0);
                        v_isShared_277_ = v_isSharedCheck_281_;
                        state = 1;
                        continue;
                    }
                } else {
                    lean_dec(v_x_273_);
                    v___x_282_ = lean_box(0);
                    return v___x_282_;
                }
            }
            1 => {
                if v_isShared_277_ == 0 {
                    v___x_279_ = v___x_276_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_280_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_280_, 0, v_a_274_);
                    v___x_279_ = v_reuseFailAlloc_280_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_279_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_LOption_toOption(
    mut v_00_u03b1_283_: *mut LeanObject,
    mut v_x_284_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_285_: *mut LeanObject = core::ptr::null_mut();
    v___x_285_ = l_Lean_LOption_toOption___redArg(v_x_284_);
    return v___x_285_;
}
pub unsafe fn l_Option_toLOption___redArg(mut v_x_286_: *mut LeanObject) -> *mut LeanObject {
    let mut v___x_287_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_288_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_290_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_291_: u8 = 0;
    let mut v___x_293_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_294_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_295_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_286_) == 0 {
                    v___x_287_ = lean_box(0);
                    return v___x_287_;
                } else {
                    v_val_288_ = lean_ctor_get(v_x_286_, 0);
                    v_isSharedCheck_295_ = (!lean_is_exclusive(v_x_286_)) as u8;
                    if v_isSharedCheck_295_ == 0 {
                        v___x_290_ = v_x_286_;
                        v_isShared_291_ = v_isSharedCheck_295_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_val_288_);
                        lean_dec(v_x_286_);
                        v___x_290_ = lean_box(0);
                        v_isShared_291_ = v_isSharedCheck_295_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_291_ == 0 {
                    v___x_293_ = v___x_290_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_294_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_294_, 0, v_val_288_);
                    v___x_293_ = v_reuseFailAlloc_294_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_293_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Option_toLOption(
    mut v_00_u03b1_296_: *mut LeanObject,
    mut v_x_297_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_298_: *mut LeanObject = core::ptr::null_mut();
    v___x_298_ = l_Option_toLOption___redArg(v_x_297_);
    return v___x_298_;
}
pub unsafe fn l_toLOptionM___redArg___lam__0(
    mut v_toPure_299_: *mut LeanObject,
    mut v_b_300_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_301_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_302_: *mut LeanObject = core::ptr::null_mut();
    v___x_301_ = l_Option_toLOption___redArg(v_b_300_);
    v___x_302_ = lean_apply_2(v_toPure_299_, lean_box(0), v___x_301_);
    return v___x_302_;
}
pub unsafe fn l_toLOptionM___redArg(
    mut v_inst_303_: *mut LeanObject,
    mut v_x_304_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toApplicative_305_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toBind_306_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toPure_307_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_308_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_309_: *mut LeanObject = core::ptr::null_mut();
    v_toApplicative_305_ = lean_ctor_get(v_inst_303_, 0);
    lean_inc_ref(v_toApplicative_305_);
    v_toBind_306_ = lean_ctor_get(v_inst_303_, 1);
    lean_inc(v_toBind_306_);
    lean_dec_ref(v_inst_303_);
    v_toPure_307_ = lean_ctor_get(v_toApplicative_305_, 1);
    lean_inc(v_toPure_307_);
    lean_dec_ref(v_toApplicative_305_);
    v___f_308_ = lean_alloc_closure(
        l_toLOptionM___redArg___lam__0 as *mut core::ffi::c_void,
        2,
        1,
    );
    lean_closure_set(v___f_308_, 0, v_toPure_307_);
    v___x_309_ = lean_apply_4(
        v_toBind_306_,
        lean_box(0),
        lean_box(0),
        v_x_304_,
        v___f_308_,
    );
    return v___x_309_;
}
pub unsafe fn l_toLOptionM(
    mut v_00_u03b1_310_: *mut LeanObject,
    mut v_m_311_: *mut LeanObject,
    mut v_inst_312_: *mut LeanObject,
    mut v_x_313_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toApplicative_314_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toBind_315_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toPure_316_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_317_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_318_: *mut LeanObject = core::ptr::null_mut();
    v_toApplicative_314_ = lean_ctor_get(v_inst_312_, 0);
    lean_inc_ref(v_toApplicative_314_);
    v_toBind_315_ = lean_ctor_get(v_inst_312_, 1);
    lean_inc(v_toBind_315_);
    lean_dec_ref(v_inst_312_);
    v_toPure_316_ = lean_ctor_get(v_toApplicative_314_, 1);
    lean_inc(v_toPure_316_);
    lean_dec_ref(v_toApplicative_314_);
    v___f_317_ = lean_alloc_closure(
        l_toLOptionM___redArg___lam__0 as *mut core::ffi::c_void,
        2,
        1,
    );
    lean_closure_set(v___f_317_, 0, v_toPure_316_);
    v___x_318_ = lean_apply_4(
        v_toBind_315_,
        lean_box(0),
        lean_box(0),
        v_x_313_,
        v___f_317_,
    );
    return v___x_318_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Data_LOption(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Init_Data_String_Basic(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Data_LOption(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_meta_initialized = true;
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lean_Data_LOption(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Init_Data_String_Basic(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Data_LOption(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Lean_Data_LOption(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Lean_Data_LOption(builtin);
}
