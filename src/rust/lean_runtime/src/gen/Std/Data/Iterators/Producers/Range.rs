// Lean compiler output
// Module: Std.Data.Iterators.Producers.Range
// Imports: Init.Data.Range.Polymorphic.Iterators
use crate::r#gen::Init::Data::Range::Polymorphic::Iterators::{
    initialize_Init_Data_Range_Polymorphic_Iterators,
    runtime_initialize_Init_Data_Range_Polymorphic_Iterators,
};
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_alloc_ctor, lean_apply_1, lean_box, lean_ctor_get,
    lean_ctor_set, lean_dec, lean_dec_ref, lean_inc, lean_inc_ref, lean_io_result_is_error,
    lean_io_result_mk_ok, lean_is_exclusive,
};
pub unsafe fn l_Std_Rcc_iter___redArg(mut v_r_139_: *mut LeanObject) -> *mut LeanObject {
    let mut v_lower_140_: *mut LeanObject = core::ptr::null_mut();
    let mut v_upper_141_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_143_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_144_: u8 = 0;
    let mut v___x_145_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_147_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_148_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_149_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_lower_140_ = lean_ctor_get(v_r_139_, 0);
                v_upper_141_ = lean_ctor_get(v_r_139_, 1);
                v_isSharedCheck_149_ = (!lean_is_exclusive(v_r_139_)) as u8;
                if v_isSharedCheck_149_ == 0 {
                    v___x_143_ = v_r_139_;
                    v_isShared_144_ = v_isSharedCheck_149_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_upper_141_);
                    lean_inc(v_lower_140_);
                    lean_dec(v_r_139_);
                    v___x_143_ = lean_box(0);
                    v_isShared_144_ = v_isSharedCheck_149_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_145_ = lean_alloc_ctor(1, 1, (0) as u32);
                lean_ctor_set(v___x_145_, 0, v_lower_140_);
                if v_isShared_144_ == 0 {
                    lean_ctor_set(v___x_143_, 0, v___x_145_);
                    v___x_147_ = v___x_143_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_148_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_148_, 0, v___x_145_);
                    lean_ctor_set(v_reuseFailAlloc_148_, 1, v_upper_141_);
                    v___x_147_ = v_reuseFailAlloc_148_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_147_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Rcc_iter(
    mut v_00_u03b1_150_: *mut LeanObject,
    mut v_r_151_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_lower_152_: *mut LeanObject = core::ptr::null_mut();
    let mut v_upper_153_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_155_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_156_: u8 = 0;
    let mut v___x_157_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_159_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_160_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_161_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_lower_152_ = lean_ctor_get(v_r_151_, 0);
                v_upper_153_ = lean_ctor_get(v_r_151_, 1);
                v_isSharedCheck_161_ = (!lean_is_exclusive(v_r_151_)) as u8;
                if v_isSharedCheck_161_ == 0 {
                    v___x_155_ = v_r_151_;
                    v_isShared_156_ = v_isSharedCheck_161_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_upper_153_);
                    lean_inc(v_lower_152_);
                    lean_dec(v_r_151_);
                    v___x_155_ = lean_box(0);
                    v_isShared_156_ = v_isSharedCheck_161_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_157_ = lean_alloc_ctor(1, 1, (0) as u32);
                lean_ctor_set(v___x_157_, 0, v_lower_152_);
                if v_isShared_156_ == 0 {
                    lean_ctor_set(v___x_155_, 0, v___x_157_);
                    v___x_159_ = v___x_155_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_160_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_160_, 0, v___x_157_);
                    lean_ctor_set(v_reuseFailAlloc_160_, 1, v_upper_153_);
                    v___x_159_ = v_reuseFailAlloc_160_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_159_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Rco_iter___redArg(mut v_r_162_: *mut LeanObject) -> *mut LeanObject {
    let mut v_lower_163_: *mut LeanObject = core::ptr::null_mut();
    let mut v_upper_164_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_166_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_167_: u8 = 0;
    let mut v___x_168_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_170_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_171_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_172_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_lower_163_ = lean_ctor_get(v_r_162_, 0);
                v_upper_164_ = lean_ctor_get(v_r_162_, 1);
                v_isSharedCheck_172_ = (!lean_is_exclusive(v_r_162_)) as u8;
                if v_isSharedCheck_172_ == 0 {
                    v___x_166_ = v_r_162_;
                    v_isShared_167_ = v_isSharedCheck_172_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_upper_164_);
                    lean_inc(v_lower_163_);
                    lean_dec(v_r_162_);
                    v___x_166_ = lean_box(0);
                    v_isShared_167_ = v_isSharedCheck_172_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_168_ = lean_alloc_ctor(1, 1, (0) as u32);
                lean_ctor_set(v___x_168_, 0, v_lower_163_);
                if v_isShared_167_ == 0 {
                    lean_ctor_set(v___x_166_, 0, v___x_168_);
                    v___x_170_ = v___x_166_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_171_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_171_, 0, v___x_168_);
                    lean_ctor_set(v_reuseFailAlloc_171_, 1, v_upper_164_);
                    v___x_170_ = v_reuseFailAlloc_171_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_170_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Rco_iter(
    mut v_00_u03b1_173_: *mut LeanObject,
    mut v_r_174_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_lower_175_: *mut LeanObject = core::ptr::null_mut();
    let mut v_upper_176_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_178_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_179_: u8 = 0;
    let mut v___x_180_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_182_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_183_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_184_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_lower_175_ = lean_ctor_get(v_r_174_, 0);
                v_upper_176_ = lean_ctor_get(v_r_174_, 1);
                v_isSharedCheck_184_ = (!lean_is_exclusive(v_r_174_)) as u8;
                if v_isSharedCheck_184_ == 0 {
                    v___x_178_ = v_r_174_;
                    v_isShared_179_ = v_isSharedCheck_184_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_upper_176_);
                    lean_inc(v_lower_175_);
                    lean_dec(v_r_174_);
                    v___x_178_ = lean_box(0);
                    v_isShared_179_ = v_isSharedCheck_184_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_180_ = lean_alloc_ctor(1, 1, (0) as u32);
                lean_ctor_set(v___x_180_, 0, v_lower_175_);
                if v_isShared_179_ == 0 {
                    lean_ctor_set(v___x_178_, 0, v___x_180_);
                    v___x_182_ = v___x_178_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_183_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_183_, 0, v___x_180_);
                    lean_ctor_set(v_reuseFailAlloc_183_, 1, v_upper_176_);
                    v___x_182_ = v_reuseFailAlloc_183_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_182_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Rci_iter___redArg(mut v_r_185_: *mut LeanObject) -> *mut LeanObject {
    let mut v___x_186_: *mut LeanObject = core::ptr::null_mut();
    v___x_186_ = lean_alloc_ctor(1, 1, (0) as u32);
    lean_ctor_set(v___x_186_, 0, v_r_185_);
    return v___x_186_;
}
pub unsafe fn l_Std_Rci_iter(
    mut v_00_u03b1_187_: *mut LeanObject,
    mut v_r_188_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_189_: *mut LeanObject = core::ptr::null_mut();
    v___x_189_ = lean_alloc_ctor(1, 1, (0) as u32);
    lean_ctor_set(v___x_189_, 0, v_r_188_);
    return v___x_189_;
}
pub unsafe fn l_Std_Roc_iter___redArg(
    mut v_inst_190_: *mut LeanObject,
    mut v_r_191_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_succ_x3f_192_: *mut LeanObject = core::ptr::null_mut();
    let mut v_lower_193_: *mut LeanObject = core::ptr::null_mut();
    let mut v_upper_194_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_196_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_197_: u8 = 0;
    let mut v___x_198_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_200_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_201_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_202_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_succ_x3f_192_ = lean_ctor_get(v_inst_190_, 0);
                lean_inc_ref(v_succ_x3f_192_);
                lean_dec_ref(v_inst_190_);
                v_lower_193_ = lean_ctor_get(v_r_191_, 0);
                v_upper_194_ = lean_ctor_get(v_r_191_, 1);
                v_isSharedCheck_202_ = (!lean_is_exclusive(v_r_191_)) as u8;
                if v_isSharedCheck_202_ == 0 {
                    v___x_196_ = v_r_191_;
                    v_isShared_197_ = v_isSharedCheck_202_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_upper_194_);
                    lean_inc(v_lower_193_);
                    lean_dec(v_r_191_);
                    v___x_196_ = lean_box(0);
                    v_isShared_197_ = v_isSharedCheck_202_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_198_ = lean_apply_1(v_succ_x3f_192_, v_lower_193_);
                if v_isShared_197_ == 0 {
                    lean_ctor_set(v___x_196_, 0, v___x_198_);
                    v___x_200_ = v___x_196_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_201_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_201_, 0, v___x_198_);
                    lean_ctor_set(v_reuseFailAlloc_201_, 1, v_upper_194_);
                    v___x_200_ = v_reuseFailAlloc_201_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_200_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Roc_iter(
    mut v_00_u03b1_203_: *mut LeanObject,
    mut v_inst_204_: *mut LeanObject,
    mut v_r_205_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_succ_x3f_206_: *mut LeanObject = core::ptr::null_mut();
    let mut v_lower_207_: *mut LeanObject = core::ptr::null_mut();
    let mut v_upper_208_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_210_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_211_: u8 = 0;
    let mut v___x_212_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_214_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_215_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_216_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_succ_x3f_206_ = lean_ctor_get(v_inst_204_, 0);
                lean_inc_ref(v_succ_x3f_206_);
                lean_dec_ref(v_inst_204_);
                v_lower_207_ = lean_ctor_get(v_r_205_, 0);
                v_upper_208_ = lean_ctor_get(v_r_205_, 1);
                v_isSharedCheck_216_ = (!lean_is_exclusive(v_r_205_)) as u8;
                if v_isSharedCheck_216_ == 0 {
                    v___x_210_ = v_r_205_;
                    v_isShared_211_ = v_isSharedCheck_216_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_upper_208_);
                    lean_inc(v_lower_207_);
                    lean_dec(v_r_205_);
                    v___x_210_ = lean_box(0);
                    v_isShared_211_ = v_isSharedCheck_216_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_212_ = lean_apply_1(v_succ_x3f_206_, v_lower_207_);
                if v_isShared_211_ == 0 {
                    lean_ctor_set(v___x_210_, 0, v___x_212_);
                    v___x_214_ = v___x_210_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_215_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_215_, 0, v___x_212_);
                    lean_ctor_set(v_reuseFailAlloc_215_, 1, v_upper_208_);
                    v___x_214_ = v_reuseFailAlloc_215_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_214_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Roo_iter___redArg(
    mut v_inst_217_: *mut LeanObject,
    mut v_r_218_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_succ_x3f_219_: *mut LeanObject = core::ptr::null_mut();
    let mut v_lower_220_: *mut LeanObject = core::ptr::null_mut();
    let mut v_upper_221_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_223_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_224_: u8 = 0;
    let mut v___x_225_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_227_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_228_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_229_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_succ_x3f_219_ = lean_ctor_get(v_inst_217_, 0);
                lean_inc_ref(v_succ_x3f_219_);
                lean_dec_ref(v_inst_217_);
                v_lower_220_ = lean_ctor_get(v_r_218_, 0);
                v_upper_221_ = lean_ctor_get(v_r_218_, 1);
                v_isSharedCheck_229_ = (!lean_is_exclusive(v_r_218_)) as u8;
                if v_isSharedCheck_229_ == 0 {
                    v___x_223_ = v_r_218_;
                    v_isShared_224_ = v_isSharedCheck_229_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_upper_221_);
                    lean_inc(v_lower_220_);
                    lean_dec(v_r_218_);
                    v___x_223_ = lean_box(0);
                    v_isShared_224_ = v_isSharedCheck_229_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_225_ = lean_apply_1(v_succ_x3f_219_, v_lower_220_);
                if v_isShared_224_ == 0 {
                    lean_ctor_set(v___x_223_, 0, v___x_225_);
                    v___x_227_ = v___x_223_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_228_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_228_, 0, v___x_225_);
                    lean_ctor_set(v_reuseFailAlloc_228_, 1, v_upper_221_);
                    v___x_227_ = v_reuseFailAlloc_228_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_227_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Roo_iter(
    mut v_00_u03b1_230_: *mut LeanObject,
    mut v_inst_231_: *mut LeanObject,
    mut v_r_232_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_succ_x3f_233_: *mut LeanObject = core::ptr::null_mut();
    let mut v_lower_234_: *mut LeanObject = core::ptr::null_mut();
    let mut v_upper_235_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_237_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_238_: u8 = 0;
    let mut v___x_239_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_241_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_242_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_243_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_succ_x3f_233_ = lean_ctor_get(v_inst_231_, 0);
                lean_inc_ref(v_succ_x3f_233_);
                lean_dec_ref(v_inst_231_);
                v_lower_234_ = lean_ctor_get(v_r_232_, 0);
                v_upper_235_ = lean_ctor_get(v_r_232_, 1);
                v_isSharedCheck_243_ = (!lean_is_exclusive(v_r_232_)) as u8;
                if v_isSharedCheck_243_ == 0 {
                    v___x_237_ = v_r_232_;
                    v_isShared_238_ = v_isSharedCheck_243_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_upper_235_);
                    lean_inc(v_lower_234_);
                    lean_dec(v_r_232_);
                    v___x_237_ = lean_box(0);
                    v_isShared_238_ = v_isSharedCheck_243_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_239_ = lean_apply_1(v_succ_x3f_233_, v_lower_234_);
                if v_isShared_238_ == 0 {
                    lean_ctor_set(v___x_237_, 0, v___x_239_);
                    v___x_241_ = v___x_237_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_242_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_242_, 0, v___x_239_);
                    lean_ctor_set(v_reuseFailAlloc_242_, 1, v_upper_235_);
                    v___x_241_ = v_reuseFailAlloc_242_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_241_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Roi_iter___redArg(
    mut v_inst_244_: *mut LeanObject,
    mut v_r_245_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_succ_x3f_246_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_247_: *mut LeanObject = core::ptr::null_mut();
    v_succ_x3f_246_ = lean_ctor_get(v_inst_244_, 0);
    lean_inc_ref(v_succ_x3f_246_);
    lean_dec_ref(v_inst_244_);
    v___x_247_ = lean_apply_1(v_succ_x3f_246_, v_r_245_);
    return v___x_247_;
}
pub unsafe fn l_Std_Roi_iter(
    mut v_00_u03b1_248_: *mut LeanObject,
    mut v_inst_249_: *mut LeanObject,
    mut v_r_250_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_succ_x3f_251_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_252_: *mut LeanObject = core::ptr::null_mut();
    v_succ_x3f_251_ = lean_ctor_get(v_inst_249_, 0);
    lean_inc_ref(v_succ_x3f_251_);
    lean_dec_ref(v_inst_249_);
    v___x_252_ = lean_apply_1(v_succ_x3f_251_, v_r_250_);
    return v___x_252_;
}
pub unsafe fn l_Std_Ric_iter___redArg(
    mut v_inst_253_: *mut LeanObject,
    mut v_r_254_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_255_: *mut LeanObject = core::ptr::null_mut();
    v___x_255_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_255_, 0, v_inst_253_);
    lean_ctor_set(v___x_255_, 1, v_r_254_);
    return v___x_255_;
}
pub unsafe fn l_Std_Ric_iter(
    mut v_00_u03b1_256_: *mut LeanObject,
    mut v_inst_257_: *mut LeanObject,
    mut v_r_258_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_259_: *mut LeanObject = core::ptr::null_mut();
    v___x_259_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_259_, 0, v_inst_257_);
    lean_ctor_set(v___x_259_, 1, v_r_258_);
    return v___x_259_;
}
pub unsafe fn l_Std_Rio_iter___redArg(
    mut v_inst_260_: *mut LeanObject,
    mut v_r_261_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_262_: *mut LeanObject = core::ptr::null_mut();
    v___x_262_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_262_, 0, v_inst_260_);
    lean_ctor_set(v___x_262_, 1, v_r_261_);
    return v___x_262_;
}
pub unsafe fn l_Std_Rio_iter(
    mut v_00_u03b1_263_: *mut LeanObject,
    mut v_inst_264_: *mut LeanObject,
    mut v_r_265_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_266_: *mut LeanObject = core::ptr::null_mut();
    v___x_266_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_266_, 0, v_inst_264_);
    lean_ctor_set(v___x_266_, 1, v_r_265_);
    return v___x_266_;
}
pub unsafe fn l_Std_Rii_iter___redArg(mut v_inst_267_: *mut LeanObject) -> *mut LeanObject {
    lean_inc(v_inst_267_);
    return v_inst_267_;
}
pub unsafe fn l_Std_Rii_iter___redArg___boxed(mut v_inst_268_: *mut LeanObject) -> *mut LeanObject {
    let mut v_res_269_: *mut LeanObject = core::ptr::null_mut();
    v_res_269_ = l_Std_Rii_iter___redArg(v_inst_268_);
    lean_dec(v_inst_268_);
    return v_res_269_;
}
pub unsafe fn l_Std_Rii_iter(
    mut v_00_u03b1_270_: *mut LeanObject,
    mut v_inst_271_: *mut LeanObject,
    mut v_x_272_: *mut LeanObject,
) -> *mut LeanObject {
    lean_inc(v_inst_271_);
    return v_inst_271_;
}
pub unsafe fn l_Std_Rii_iter___boxed(
    mut v_00_u03b1_273_: *mut LeanObject,
    mut v_inst_274_: *mut LeanObject,
    mut v_x_275_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_276_: *mut LeanObject = core::ptr::null_mut();
    v_res_276_ = l_Std_Rii_iter(v_00_u03b1_273_, v_inst_274_, v_x_275_);
    lean_dec(v_inst_274_);
    return v_res_276_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Std_Data_Iterators_Producers_Range(
    builtin: u8,
) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Init_Data_Range_Polymorphic_Iterators(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Std_Data_Iterators_Producers_Range(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_meta_initialized = true;
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Std_Data_Iterators_Producers_Range(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Init_Data_Range_Polymorphic_Iterators(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Std_Data_Iterators_Producers_Range(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Std_Data_Iterators_Producers_Range(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Std_Data_Iterators_Producers_Range(builtin);
}
