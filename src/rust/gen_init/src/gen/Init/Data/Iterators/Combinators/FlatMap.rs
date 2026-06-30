// Lean compiler output
// Module: Init.Data.Iterators.Combinators.FlatMap
// Imports: Init.Data.Iterators.Combinators.Monadic.FlatMap Init.Data.Iterators.Combinators.FilterMap
use crate::r#gen::Init::Data::Iterators::Combinators::FilterMap::{
    initialize_Init_Data_Iterators_Combinators_FilterMap,
    runtime_initialize_Init_Data_Iterators_Combinators_FilterMap,
};
use crate::r#gen::Init::Data::Iterators::Combinators::Monadic::FlatMap::{
    initialize_Init_Data_Iterators_Combinators_Monadic_FlatMap,
    runtime_initialize_Init_Data_Iterators_Combinators_Monadic_FlatMap,
};
pub unsafe fn l_Std_Iter_flatMapAfterM___redArg(
    mut v_it_u2081_123_: *mut leanh::LeanObject,
    mut v_it_u2082_124_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_125_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_125_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_125_, 0, v_it_u2081_123_);
    leanh::lean_ctor_set(v___x_125_, 1, v_it_u2082_124_);
    return v___x_125_;
}
pub unsafe fn l_Std_Iter_flatMapAfterM(
    mut v_00_u03b1_126_: *mut leanh::LeanObject,
    mut v_00_u03b2_127_: *mut leanh::LeanObject,
    mut v_00_u03b1_u2082_128_: *mut leanh::LeanObject,
    mut v_00_u03b3_129_: *mut leanh::LeanObject,
    mut v_m_130_: *mut leanh::LeanObject,
    mut v_inst_131_: *mut leanh::LeanObject,
    mut v_inst_132_: *mut leanh::LeanObject,
    mut v_inst_133_: *mut leanh::LeanObject,
    mut v_inst_134_: *mut leanh::LeanObject,
    mut v_f_135_: *mut leanh::LeanObject,
    mut v_it_u2081_136_: *mut leanh::LeanObject,
    mut v_it_u2082_137_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_138_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_138_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_138_, 0, v_it_u2081_136_);
    leanh::lean_ctor_set(v___x_138_, 1, v_it_u2082_137_);
    return v___x_138_;
}
pub unsafe fn l_Std_Iter_flatMapAfterM___boxed(
    mut v_00_u03b1_139_: *mut leanh::LeanObject,
    mut v_00_u03b2_140_: *mut leanh::LeanObject,
    mut v_00_u03b1_u2082_141_: *mut leanh::LeanObject,
    mut v_00_u03b3_142_: *mut leanh::LeanObject,
    mut v_m_143_: *mut leanh::LeanObject,
    mut v_inst_144_: *mut leanh::LeanObject,
    mut v_inst_145_: *mut leanh::LeanObject,
    mut v_inst_146_: *mut leanh::LeanObject,
    mut v_inst_147_: *mut leanh::LeanObject,
    mut v_f_148_: *mut leanh::LeanObject,
    mut v_it_u2081_149_: *mut leanh::LeanObject,
    mut v_it_u2082_150_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_151_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_151_ = l_Std_Iter_flatMapAfterM(
        v_00_u03b1_139_,
        v_00_u03b2_140_,
        v_00_u03b1_u2082_141_,
        v_00_u03b3_142_,
        v_m_143_,
        v_inst_144_,
        v_inst_145_,
        v_inst_146_,
        v_inst_147_,
        v_f_148_,
        v_it_u2081_149_,
        v_it_u2082_150_,
    );
    leanh::lean_dec(v_f_148_);
    leanh::lean_dec(v_inst_147_);
    leanh::lean_dec(v_inst_146_);
    leanh::lean_dec(v_inst_145_);
    leanh::lean_dec_ref(v_inst_144_);
    return v_res_151_;
}
pub unsafe fn l_Std_Iter_flatMapM___redArg(
    mut v_it_152_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_153_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_154_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_153_ = leanh::lean_box(0);
    v___x_154_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_154_, 0, v_it_152_);
    leanh::lean_ctor_set(v___x_154_, 1, v___x_153_);
    return v___x_154_;
}
pub unsafe fn l_Std_Iter_flatMapM(
    mut v_00_u03b1_155_: *mut leanh::LeanObject,
    mut v_00_u03b2_156_: *mut leanh::LeanObject,
    mut v_00_u03b1_u2082_157_: *mut leanh::LeanObject,
    mut v_00_u03b3_158_: *mut leanh::LeanObject,
    mut v_m_159_: *mut leanh::LeanObject,
    mut v_inst_160_: *mut leanh::LeanObject,
    mut v_inst_161_: *mut leanh::LeanObject,
    mut v_inst_162_: *mut leanh::LeanObject,
    mut v_inst_163_: *mut leanh::LeanObject,
    mut v_f_164_: *mut leanh::LeanObject,
    mut v_it_165_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_166_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_167_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_166_ = leanh::lean_box(0);
    v___x_167_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_167_, 0, v_it_165_);
    leanh::lean_ctor_set(v___x_167_, 1, v___x_166_);
    return v___x_167_;
}
pub unsafe fn l_Std_Iter_flatMapM___boxed(
    mut v_00_u03b1_168_: *mut leanh::LeanObject,
    mut v_00_u03b2_169_: *mut leanh::LeanObject,
    mut v_00_u03b1_u2082_170_: *mut leanh::LeanObject,
    mut v_00_u03b3_171_: *mut leanh::LeanObject,
    mut v_m_172_: *mut leanh::LeanObject,
    mut v_inst_173_: *mut leanh::LeanObject,
    mut v_inst_174_: *mut leanh::LeanObject,
    mut v_inst_175_: *mut leanh::LeanObject,
    mut v_inst_176_: *mut leanh::LeanObject,
    mut v_f_177_: *mut leanh::LeanObject,
    mut v_it_178_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_179_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_179_ = l_Std_Iter_flatMapM(
        v_00_u03b1_168_,
        v_00_u03b2_169_,
        v_00_u03b1_u2082_170_,
        v_00_u03b3_171_,
        v_m_172_,
        v_inst_173_,
        v_inst_174_,
        v_inst_175_,
        v_inst_176_,
        v_f_177_,
        v_it_178_,
    );
    leanh::lean_dec(v_f_177_);
    leanh::lean_dec(v_inst_176_);
    leanh::lean_dec(v_inst_175_);
    leanh::lean_dec(v_inst_174_);
    leanh::lean_dec_ref(v_inst_173_);
    return v_res_179_;
}
pub unsafe fn l_Std_Iter_flatMapAfter___redArg(
    mut v_it_u2081_180_: *mut leanh::LeanObject,
    mut v_it_u2082_181_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_182_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_183_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_184_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_186_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_187_: u8 = 0;
    let mut v___x_189_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_190_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_191_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_192_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_it_u2082_181_) == 0 {
                    v___x_182_ = leanh::lean_box(0);
                    v___x_183_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_183_, 0, v_it_u2081_180_);
                    leanh::lean_ctor_set(v___x_183_, 1, v___x_182_);
                    return v___x_183_;
                } else {
                    v_val_184_ = leanh::lean_ctor_get(v_it_u2082_181_, 0);
                    v_isSharedCheck_192_ =
                        (!leanh::lean_is_exclusive(v_it_u2082_181_)) as u8;
                    if v_isSharedCheck_192_ == 0 {
                        v___x_186_ = v_it_u2082_181_;
                        v_isShared_187_ = v_isSharedCheck_192_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_val_184_);
                        leanh::lean_dec(v_it_u2082_181_);
                        v___x_186_ = leanh::lean_box(0);
                        v_isShared_187_ = v_isSharedCheck_192_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_187_ == 0 {
                    v___x_189_ = v___x_186_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_191_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_191_, 0, v_val_184_);
                    v___x_189_ = v_reuseFailAlloc_191_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_190_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_190_, 0, v_it_u2081_180_);
                leanh::lean_ctor_set(v___x_190_, 1, v___x_189_);
                return v___x_190_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Iter_flatMapAfter(
    mut v_00_u03b1_193_: *mut leanh::LeanObject,
    mut v_00_u03b2_194_: *mut leanh::LeanObject,
    mut v_00_u03b1_u2082_195_: *mut leanh::LeanObject,
    mut v_00_u03b3_196_: *mut leanh::LeanObject,
    mut v_inst_197_: *mut leanh::LeanObject,
    mut v_inst_198_: *mut leanh::LeanObject,
    mut v_f_199_: *mut leanh::LeanObject,
    mut v_it_u2081_200_: *mut leanh::LeanObject,
    mut v_it_u2082_201_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_202_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_203_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_204_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_206_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_207_: u8 = 0;
    let mut v___x_209_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_210_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_211_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_212_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_it_u2082_201_) == 0 {
                    v___x_202_ = leanh::lean_box(0);
                    v___x_203_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_203_, 0, v_it_u2081_200_);
                    leanh::lean_ctor_set(v___x_203_, 1, v___x_202_);
                    return v___x_203_;
                } else {
                    v_val_204_ = leanh::lean_ctor_get(v_it_u2082_201_, 0);
                    v_isSharedCheck_212_ =
                        (!leanh::lean_is_exclusive(v_it_u2082_201_)) as u8;
                    if v_isSharedCheck_212_ == 0 {
                        v___x_206_ = v_it_u2082_201_;
                        v_isShared_207_ = v_isSharedCheck_212_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_val_204_);
                        leanh::lean_dec(v_it_u2082_201_);
                        v___x_206_ = leanh::lean_box(0);
                        v_isShared_207_ = v_isSharedCheck_212_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_207_ == 0 {
                    v___x_209_ = v___x_206_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_211_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_211_, 0, v_val_204_);
                    v___x_209_ = v_reuseFailAlloc_211_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_210_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_210_, 0, v_it_u2081_200_);
                leanh::lean_ctor_set(v___x_210_, 1, v___x_209_);
                return v___x_210_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Iter_flatMapAfter___boxed(
    mut v_00_u03b1_213_: *mut leanh::LeanObject,
    mut v_00_u03b2_214_: *mut leanh::LeanObject,
    mut v_00_u03b1_u2082_215_: *mut leanh::LeanObject,
    mut v_00_u03b3_216_: *mut leanh::LeanObject,
    mut v_inst_217_: *mut leanh::LeanObject,
    mut v_inst_218_: *mut leanh::LeanObject,
    mut v_f_219_: *mut leanh::LeanObject,
    mut v_it_u2081_220_: *mut leanh::LeanObject,
    mut v_it_u2082_221_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_222_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_222_ = l_Std_Iter_flatMapAfter(
        v_00_u03b1_213_,
        v_00_u03b2_214_,
        v_00_u03b1_u2082_215_,
        v_00_u03b3_216_,
        v_inst_217_,
        v_inst_218_,
        v_f_219_,
        v_it_u2081_220_,
        v_it_u2082_221_,
    );
    leanh::lean_dec(v_f_219_);
    leanh::lean_dec(v_inst_218_);
    leanh::lean_dec(v_inst_217_);
    return v_res_222_;
}
pub unsafe fn l_Std_Iter_flatMap___redArg(
    mut v_it_223_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_224_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_225_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_224_ = leanh::lean_box(0);
    v___x_225_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_225_, 0, v_it_223_);
    leanh::lean_ctor_set(v___x_225_, 1, v___x_224_);
    return v___x_225_;
}
pub unsafe fn l_Std_Iter_flatMap(
    mut v_00_u03b1_226_: *mut leanh::LeanObject,
    mut v_00_u03b2_227_: *mut leanh::LeanObject,
    mut v_00_u03b1_u2082_228_: *mut leanh::LeanObject,
    mut v_00_u03b3_229_: *mut leanh::LeanObject,
    mut v_inst_230_: *mut leanh::LeanObject,
    mut v_inst_231_: *mut leanh::LeanObject,
    mut v_f_232_: *mut leanh::LeanObject,
    mut v_it_233_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_234_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_235_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_234_ = leanh::lean_box(0);
    v___x_235_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_235_, 0, v_it_233_);
    leanh::lean_ctor_set(v___x_235_, 1, v___x_234_);
    return v___x_235_;
}
pub unsafe fn l_Std_Iter_flatMap___boxed(
    mut v_00_u03b1_236_: *mut leanh::LeanObject,
    mut v_00_u03b2_237_: *mut leanh::LeanObject,
    mut v_00_u03b1_u2082_238_: *mut leanh::LeanObject,
    mut v_00_u03b3_239_: *mut leanh::LeanObject,
    mut v_inst_240_: *mut leanh::LeanObject,
    mut v_inst_241_: *mut leanh::LeanObject,
    mut v_f_242_: *mut leanh::LeanObject,
    mut v_it_243_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_244_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_244_ = l_Std_Iter_flatMap(
        v_00_u03b1_236_,
        v_00_u03b2_237_,
        v_00_u03b1_u2082_238_,
        v_00_u03b3_239_,
        v_inst_240_,
        v_inst_241_,
        v_f_242_,
        v_it_243_,
    );
    leanh::lean_dec(v_f_242_);
    leanh::lean_dec(v_inst_241_);
    leanh::lean_dec(v_inst_240_);
    return v_res_244_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Init_Data_Iterators_Combinators_FlatMap(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Init_Data_Iterators_Combinators_Monadic_FlatMap(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Iterators_Combinators_FilterMap(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Init_Data_Iterators_Combinators_FlatMap(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_meta_initialized = true;
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Init_Data_Iterators_Combinators_FlatMap(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Init_Data_Iterators_Combinators_Monadic_FlatMap(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Iterators_Combinators_FilterMap(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Iterators_Combinators_FlatMap(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = meta_initialize_Init_Data_Iterators_Combinators_FlatMap(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return initialize_Init_Data_Iterators_Combinators_FlatMap(builtin);
}