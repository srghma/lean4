// Lean compiler output
// Module: Std.Data.Iterators.Producers.Range
// Imports: Init.Data.Range.Polymorphic.Iterators
use crate::r#gen::Init::Data::Range::Polymorphic::Iterators::{
    initialize_Init_Data_Range_Polymorphic_Iterators,
    runtime_initialize_Init_Data_Range_Polymorphic_Iterators,
};
pub unsafe fn l_Std_Rcc_iter___redArg(
    mut v_r_139_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_lower_140_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_upper_141_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_143_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_144_: u8 = 0;
    let mut v___x_145_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_147_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_148_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_149_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_lower_140_ = crate::leanh::lean_ctor_get(v_r_139_, 0);
                v_upper_141_ = crate::leanh::lean_ctor_get(v_r_139_, 1);
                v_isSharedCheck_149_ = (!crate::leanh::lean_is_exclusive(v_r_139_)) as u8;
                if v_isSharedCheck_149_ == 0 {
                    v___x_143_ = v_r_139_;
                    v_isShared_144_ = v_isSharedCheck_149_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_upper_141_);
                    crate::leanh::lean_inc(v_lower_140_);
                    crate::leanh::lean_dec(v_r_139_);
                    v___x_143_ = crate::leanh::lean_box(0);
                    v_isShared_144_ = v_isSharedCheck_149_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_145_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_145_, 0, v_lower_140_);
                if v_isShared_144_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_143_, 0, v___x_145_);
                    v___x_147_ = v___x_143_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_148_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_148_, 0, v___x_145_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_148_, 1, v_upper_141_);
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
    mut v_00_u03b1_150_: *mut crate::leanh::LeanObject,
    mut v_r_151_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_lower_152_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_upper_153_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_155_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_156_: u8 = 0;
    let mut v___x_157_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_159_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_160_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_161_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_lower_152_ = crate::leanh::lean_ctor_get(v_r_151_, 0);
                v_upper_153_ = crate::leanh::lean_ctor_get(v_r_151_, 1);
                v_isSharedCheck_161_ = (!crate::leanh::lean_is_exclusive(v_r_151_)) as u8;
                if v_isSharedCheck_161_ == 0 {
                    v___x_155_ = v_r_151_;
                    v_isShared_156_ = v_isSharedCheck_161_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_upper_153_);
                    crate::leanh::lean_inc(v_lower_152_);
                    crate::leanh::lean_dec(v_r_151_);
                    v___x_155_ = crate::leanh::lean_box(0);
                    v_isShared_156_ = v_isSharedCheck_161_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_157_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_157_, 0, v_lower_152_);
                if v_isShared_156_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_155_, 0, v___x_157_);
                    v___x_159_ = v___x_155_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_160_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_160_, 0, v___x_157_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_160_, 1, v_upper_153_);
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
pub unsafe fn l_Std_Rco_iter___redArg(
    mut v_r_162_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_lower_163_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_upper_164_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_166_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_167_: u8 = 0;
    let mut v___x_168_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_170_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_171_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_172_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_lower_163_ = crate::leanh::lean_ctor_get(v_r_162_, 0);
                v_upper_164_ = crate::leanh::lean_ctor_get(v_r_162_, 1);
                v_isSharedCheck_172_ = (!crate::leanh::lean_is_exclusive(v_r_162_)) as u8;
                if v_isSharedCheck_172_ == 0 {
                    v___x_166_ = v_r_162_;
                    v_isShared_167_ = v_isSharedCheck_172_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_upper_164_);
                    crate::leanh::lean_inc(v_lower_163_);
                    crate::leanh::lean_dec(v_r_162_);
                    v___x_166_ = crate::leanh::lean_box(0);
                    v_isShared_167_ = v_isSharedCheck_172_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_168_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_168_, 0, v_lower_163_);
                if v_isShared_167_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_166_, 0, v___x_168_);
                    v___x_170_ = v___x_166_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_171_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_171_, 0, v___x_168_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_171_, 1, v_upper_164_);
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
    mut v_00_u03b1_173_: *mut crate::leanh::LeanObject,
    mut v_r_174_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_lower_175_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_upper_176_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_178_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_179_: u8 = 0;
    let mut v___x_180_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_182_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_183_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_184_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_lower_175_ = crate::leanh::lean_ctor_get(v_r_174_, 0);
                v_upper_176_ = crate::leanh::lean_ctor_get(v_r_174_, 1);
                v_isSharedCheck_184_ = (!crate::leanh::lean_is_exclusive(v_r_174_)) as u8;
                if v_isSharedCheck_184_ == 0 {
                    v___x_178_ = v_r_174_;
                    v_isShared_179_ = v_isSharedCheck_184_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_upper_176_);
                    crate::leanh::lean_inc(v_lower_175_);
                    crate::leanh::lean_dec(v_r_174_);
                    v___x_178_ = crate::leanh::lean_box(0);
                    v_isShared_179_ = v_isSharedCheck_184_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_180_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_180_, 0, v_lower_175_);
                if v_isShared_179_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_178_, 0, v___x_180_);
                    v___x_182_ = v___x_178_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_183_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_183_, 0, v___x_180_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_183_, 1, v_upper_176_);
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
pub unsafe fn l_Std_Rci_iter___redArg(
    mut v_r_185_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_186_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_186_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_186_, 0, v_r_185_);
    return v___x_186_;
}
pub unsafe fn l_Std_Rci_iter(
    mut v_00_u03b1_187_: *mut crate::leanh::LeanObject,
    mut v_r_188_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_189_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_189_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_189_, 0, v_r_188_);
    return v___x_189_;
}
pub unsafe fn l_Std_Roc_iter___redArg(
    mut v_inst_190_: *mut crate::leanh::LeanObject,
    mut v_r_191_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_succ_x3f_192_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_lower_193_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_upper_194_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_196_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_197_: u8 = 0;
    let mut v___x_198_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_200_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_201_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_202_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_succ_x3f_192_ = crate::leanh::lean_ctor_get(v_inst_190_, 0);
                crate::leanh::lean_inc_ref(v_succ_x3f_192_);
                crate::leanh::lean_dec_ref(v_inst_190_);
                v_lower_193_ = crate::leanh::lean_ctor_get(v_r_191_, 0);
                v_upper_194_ = crate::leanh::lean_ctor_get(v_r_191_, 1);
                v_isSharedCheck_202_ = (!crate::leanh::lean_is_exclusive(v_r_191_)) as u8;
                if v_isSharedCheck_202_ == 0 {
                    v___x_196_ = v_r_191_;
                    v_isShared_197_ = v_isSharedCheck_202_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_upper_194_);
                    crate::leanh::lean_inc(v_lower_193_);
                    crate::leanh::lean_dec(v_r_191_);
                    v___x_196_ = crate::leanh::lean_box(0);
                    v_isShared_197_ = v_isSharedCheck_202_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_198_ = crate::leanh::lean_apply_1(v_succ_x3f_192_, v_lower_193_);
                if v_isShared_197_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_196_, 0, v___x_198_);
                    v___x_200_ = v___x_196_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_201_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_201_, 0, v___x_198_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_201_, 1, v_upper_194_);
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
    mut v_00_u03b1_203_: *mut crate::leanh::LeanObject,
    mut v_inst_204_: *mut crate::leanh::LeanObject,
    mut v_r_205_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_succ_x3f_206_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_lower_207_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_upper_208_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_210_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_211_: u8 = 0;
    let mut v___x_212_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_214_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_215_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_216_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_succ_x3f_206_ = crate::leanh::lean_ctor_get(v_inst_204_, 0);
                crate::leanh::lean_inc_ref(v_succ_x3f_206_);
                crate::leanh::lean_dec_ref(v_inst_204_);
                v_lower_207_ = crate::leanh::lean_ctor_get(v_r_205_, 0);
                v_upper_208_ = crate::leanh::lean_ctor_get(v_r_205_, 1);
                v_isSharedCheck_216_ = (!crate::leanh::lean_is_exclusive(v_r_205_)) as u8;
                if v_isSharedCheck_216_ == 0 {
                    v___x_210_ = v_r_205_;
                    v_isShared_211_ = v_isSharedCheck_216_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_upper_208_);
                    crate::leanh::lean_inc(v_lower_207_);
                    crate::leanh::lean_dec(v_r_205_);
                    v___x_210_ = crate::leanh::lean_box(0);
                    v_isShared_211_ = v_isSharedCheck_216_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_212_ = crate::leanh::lean_apply_1(v_succ_x3f_206_, v_lower_207_);
                if v_isShared_211_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_210_, 0, v___x_212_);
                    v___x_214_ = v___x_210_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_215_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_215_, 0, v___x_212_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_215_, 1, v_upper_208_);
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
    mut v_inst_217_: *mut crate::leanh::LeanObject,
    mut v_r_218_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_succ_x3f_219_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_lower_220_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_upper_221_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_223_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_224_: u8 = 0;
    let mut v___x_225_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_227_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_228_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_229_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_succ_x3f_219_ = crate::leanh::lean_ctor_get(v_inst_217_, 0);
                crate::leanh::lean_inc_ref(v_succ_x3f_219_);
                crate::leanh::lean_dec_ref(v_inst_217_);
                v_lower_220_ = crate::leanh::lean_ctor_get(v_r_218_, 0);
                v_upper_221_ = crate::leanh::lean_ctor_get(v_r_218_, 1);
                v_isSharedCheck_229_ = (!crate::leanh::lean_is_exclusive(v_r_218_)) as u8;
                if v_isSharedCheck_229_ == 0 {
                    v___x_223_ = v_r_218_;
                    v_isShared_224_ = v_isSharedCheck_229_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_upper_221_);
                    crate::leanh::lean_inc(v_lower_220_);
                    crate::leanh::lean_dec(v_r_218_);
                    v___x_223_ = crate::leanh::lean_box(0);
                    v_isShared_224_ = v_isSharedCheck_229_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_225_ = crate::leanh::lean_apply_1(v_succ_x3f_219_, v_lower_220_);
                if v_isShared_224_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_223_, 0, v___x_225_);
                    v___x_227_ = v___x_223_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_228_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_228_, 0, v___x_225_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_228_, 1, v_upper_221_);
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
    mut v_00_u03b1_230_: *mut crate::leanh::LeanObject,
    mut v_inst_231_: *mut crate::leanh::LeanObject,
    mut v_r_232_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_succ_x3f_233_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_lower_234_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_upper_235_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_237_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_238_: u8 = 0;
    let mut v___x_239_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_241_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_242_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_243_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_succ_x3f_233_ = crate::leanh::lean_ctor_get(v_inst_231_, 0);
                crate::leanh::lean_inc_ref(v_succ_x3f_233_);
                crate::leanh::lean_dec_ref(v_inst_231_);
                v_lower_234_ = crate::leanh::lean_ctor_get(v_r_232_, 0);
                v_upper_235_ = crate::leanh::lean_ctor_get(v_r_232_, 1);
                v_isSharedCheck_243_ = (!crate::leanh::lean_is_exclusive(v_r_232_)) as u8;
                if v_isSharedCheck_243_ == 0 {
                    v___x_237_ = v_r_232_;
                    v_isShared_238_ = v_isSharedCheck_243_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_upper_235_);
                    crate::leanh::lean_inc(v_lower_234_);
                    crate::leanh::lean_dec(v_r_232_);
                    v___x_237_ = crate::leanh::lean_box(0);
                    v_isShared_238_ = v_isSharedCheck_243_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_239_ = crate::leanh::lean_apply_1(v_succ_x3f_233_, v_lower_234_);
                if v_isShared_238_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_237_, 0, v___x_239_);
                    v___x_241_ = v___x_237_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_242_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_242_, 0, v___x_239_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_242_, 1, v_upper_235_);
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
    mut v_inst_244_: *mut crate::leanh::LeanObject,
    mut v_r_245_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_succ_x3f_246_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_247_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_succ_x3f_246_ = crate::leanh::lean_ctor_get(v_inst_244_, 0);
    crate::leanh::lean_inc_ref(v_succ_x3f_246_);
    crate::leanh::lean_dec_ref(v_inst_244_);
    v___x_247_ = crate::leanh::lean_apply_1(v_succ_x3f_246_, v_r_245_);
    return v___x_247_;
}
pub unsafe fn l_Std_Roi_iter(
    mut v_00_u03b1_248_: *mut crate::leanh::LeanObject,
    mut v_inst_249_: *mut crate::leanh::LeanObject,
    mut v_r_250_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_succ_x3f_251_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_252_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_succ_x3f_251_ = crate::leanh::lean_ctor_get(v_inst_249_, 0);
    crate::leanh::lean_inc_ref(v_succ_x3f_251_);
    crate::leanh::lean_dec_ref(v_inst_249_);
    v___x_252_ = crate::leanh::lean_apply_1(v_succ_x3f_251_, v_r_250_);
    return v___x_252_;
}
pub unsafe fn l_Std_Ric_iter___redArg(
    mut v_inst_253_: *mut crate::leanh::LeanObject,
    mut v_r_254_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_255_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_255_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_255_, 0, v_inst_253_);
    crate::leanh::lean_ctor_set(v___x_255_, 1, v_r_254_);
    return v___x_255_;
}
pub unsafe fn l_Std_Ric_iter(
    mut v_00_u03b1_256_: *mut crate::leanh::LeanObject,
    mut v_inst_257_: *mut crate::leanh::LeanObject,
    mut v_r_258_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_259_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_259_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_259_, 0, v_inst_257_);
    crate::leanh::lean_ctor_set(v___x_259_, 1, v_r_258_);
    return v___x_259_;
}
pub unsafe fn l_Std_Rio_iter___redArg(
    mut v_inst_260_: *mut crate::leanh::LeanObject,
    mut v_r_261_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_262_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_262_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_262_, 0, v_inst_260_);
    crate::leanh::lean_ctor_set(v___x_262_, 1, v_r_261_);
    return v___x_262_;
}
pub unsafe fn l_Std_Rio_iter(
    mut v_00_u03b1_263_: *mut crate::leanh::LeanObject,
    mut v_inst_264_: *mut crate::leanh::LeanObject,
    mut v_r_265_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_266_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_266_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_266_, 0, v_inst_264_);
    crate::leanh::lean_ctor_set(v___x_266_, 1, v_r_265_);
    return v___x_266_;
}
pub unsafe fn l_Std_Rii_iter___redArg(
    mut v_inst_267_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_inst_267_);
    return v_inst_267_;
}
pub unsafe fn l_Std_Rii_iter___redArg___boxed(
    mut v_inst_268_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_269_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_269_ = l_Std_Rii_iter___redArg(v_inst_268_);
    crate::leanh::lean_dec(v_inst_268_);
    return v_res_269_;
}
pub unsafe fn l_Std_Rii_iter(
    mut v_00_u03b1_270_: *mut crate::leanh::LeanObject,
    mut v_inst_271_: *mut crate::leanh::LeanObject,
    mut v_x_272_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_inst_271_);
    return v_inst_271_;
}
pub unsafe fn l_Std_Rii_iter___boxed(
    mut v_00_u03b1_273_: *mut crate::leanh::LeanObject,
    mut v_inst_274_: *mut crate::leanh::LeanObject,
    mut v_x_275_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_276_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_276_ = l_Std_Rii_iter(v_00_u03b1_273_, v_inst_274_, v_x_275_);
    crate::leanh::lean_dec(v_inst_274_);
    return v_res_276_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Std_Data_Iterators_Producers_Range(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Init_Data_Range_Polymorphic_Iterators(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Std_Data_Iterators_Producers_Range(
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
pub unsafe fn initialize_Std_Data_Iterators_Producers_Range(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Init_Data_Range_Polymorphic_Iterators(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Std_Data_Iterators_Producers_Range(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Std_Data_Iterators_Producers_Range(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Std_Data_Iterators_Producers_Range(builtin);
}
