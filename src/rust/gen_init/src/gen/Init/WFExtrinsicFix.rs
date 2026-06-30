// Lean compiler output
// Module: Init.WFExtrinsicFix
// Imports: Init.WF Init.Classical Init.Ext Init.NotationExtra
use crate::r#gen::Init::Classical::{initialize_Init_Classical, runtime_initialize_Init_Classical};
use crate::r#gen::Init::Ext::{initialize_Init_Ext, runtime_initialize_Init_Ext};
use crate::r#gen::Init::NotationExtra::{
    initialize_Init_NotationExtra, runtime_initialize_Init_NotationExtra,
};
use crate::r#gen::Init::WF::{initialize_Init_WF, runtime_initialize_Init_WF};
pub unsafe fn l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix___redArg(
    mut v_F_136_: *mut leanh::LeanObject,
    mut v_a_137_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_138_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_139_: *mut leanh::LeanObject = core::ptr::null_mut();
    leanh::lean_inc(v_F_136_);
    v___f_138_ = leanh::lean_alloc_closure(
        l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix___redArg___lam__0
            as *mut core::ffi::c_void,
        3,
        1,
    );
    leanh::lean_closure_set(v___f_138_, 0, v_F_136_);
    v___x_139_ = leanh::lean_apply_2(v_F_136_, v_a_137_, v___f_138_);
    return v___x_139_;
}
pub unsafe fn l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix___redArg___lam__0(
    mut v_F_140_: *mut leanh::LeanObject,
    mut v_a_141_: *mut leanh::LeanObject,
    mut v_x_142_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_143_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_143_ =
        l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix___redArg(v_F_140_, v_a_141_);
    return v___x_143_;
}
pub unsafe fn l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix(
    mut v_00_u03b1_144_: *mut leanh::LeanObject,
    mut v_C_145_: *mut leanh::LeanObject,
    mut v_inst_146_: *mut leanh::LeanObject,
    mut v_R_147_: *mut leanh::LeanObject,
    mut v_F_148_: *mut leanh::LeanObject,
    mut v_a_149_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_150_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_150_ =
        l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix___redArg(v_F_148_, v_a_149_);
    return v___x_150_;
}
pub unsafe fn l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___redArg(
    mut v_F_151_: *mut leanh::LeanObject,
    mut v_a_152_: *mut leanh::LeanObject,
    mut v_b_153_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_154_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_155_: *mut leanh::LeanObject = core::ptr::null_mut();
    leanh::lean_inc(v_F_151_);
    v___f_154_ = leanh::lean_alloc_closure(
        l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___redArg___lam__0
            as *mut core::ffi::c_void,
        4,
        1,
    );
    leanh::lean_closure_set(v___f_154_, 0, v_F_151_);
    v___x_155_ = leanh::lean_apply_3(v_F_151_, v_a_152_, v_b_153_, v___f_154_);
    return v___x_155_;
}
pub unsafe fn l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___redArg___lam__0(
    mut v_F_156_: *mut leanh::LeanObject,
    mut v_a_x27_157_: *mut leanh::LeanObject,
    mut v_b_x27_158_: *mut leanh::LeanObject,
    mut v_x_159_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_160_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_160_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___redArg(
        v_F_156_,
        v_a_x27_157_,
        v_b_x27_158_,
    );
    return v___x_160_;
}
pub unsafe fn l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082(
    mut v_00_u03b1_161_: *mut leanh::LeanObject,
    mut v_00_u03b2_162_: *mut leanh::LeanObject,
    mut v_C_u2082_163_: *mut leanh::LeanObject,
    mut v_inst_164_: *mut leanh::LeanObject,
    mut v_R_165_: *mut leanh::LeanObject,
    mut v_F_166_: *mut leanh::LeanObject,
    mut v_a_167_: *mut leanh::LeanObject,
    mut v_b_168_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_169_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_169_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___redArg(
        v_F_166_, v_a_167_, v_b_168_,
    );
    return v___x_169_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___redArg(
    mut v_F_170_: *mut leanh::LeanObject,
    mut v_a_171_: *mut leanh::LeanObject,
    mut v_b_172_: *mut leanh::LeanObject,
    mut v_c_173_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_174_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_175_: *mut leanh::LeanObject = core::ptr::null_mut();
    leanh::lean_inc(v_F_170_);
    v___f_174_ = leanh::lean_alloc_closure(
        l_WellFounded_opaqueFix_u2083___redArg___lam__0 as *mut core::ffi::c_void,
        5,
        1,
    );
    leanh::lean_closure_set(v___f_174_, 0, v_F_170_);
    v___x_175_ = leanh::lean_apply_4(v_F_170_, v_a_171_, v_b_172_, v_c_173_, v___f_174_);
    return v___x_175_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___redArg___lam__0(
    mut v_F_176_: *mut leanh::LeanObject,
    mut v_a_177_: *mut leanh::LeanObject,
    mut v_b_178_: *mut leanh::LeanObject,
    mut v_c_179_: *mut leanh::LeanObject,
    mut v_x_180_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_181_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_181_ = l_WellFounded_opaqueFix_u2083___redArg(v_F_176_, v_a_177_, v_b_178_, v_c_179_);
    return v___x_181_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083(
    mut v_00_u03b1_182_: *mut leanh::LeanObject,
    mut v_00_u03b2_183_: *mut leanh::LeanObject,
    mut v_00_u03b3_184_: *mut leanh::LeanObject,
    mut v_C_u2083_185_: *mut leanh::LeanObject,
    mut v_inst_186_: *mut leanh::LeanObject,
    mut v_R_187_: *mut leanh::LeanObject,
    mut v_F_188_: *mut leanh::LeanObject,
    mut v_a_189_: *mut leanh::LeanObject,
    mut v_b_190_: *mut leanh::LeanObject,
    mut v_c_191_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_192_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_192_ = l_WellFounded_opaqueFix_u2083___redArg(v_F_188_, v_a_189_, v_b_190_, v_c_191_);
    return v___x_192_;
}
pub unsafe fn l_WellFounded_partialExtrinsicFix___redArg___lam__0(
    mut v_recur_193_: *mut leanh::LeanObject,
    mut v_a_x27_194_: *mut leanh::LeanObject,
    mut v_hR_195_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_196_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_196_ = leanh::lean_apply_2(v_recur_193_, v_a_x27_194_, leanh::lean_box(0));
    return v___x_196_;
}
pub unsafe fn l_WellFounded_partialExtrinsicFix___redArg___lam__1(
    mut v_F_197_: *mut leanh::LeanObject,
    mut v_a_198_: *mut leanh::LeanObject,
    mut v_recur_199_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_200_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_201_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_200_ = leanh::lean_alloc_closure(
        l_WellFounded_partialExtrinsicFix___redArg___lam__0 as *mut core::ffi::c_void,
        3,
        1,
    );
    leanh::lean_closure_set(v___f_200_, 0, v_recur_199_);
    v___x_201_ = leanh::lean_apply_2(v_F_197_, v_a_198_, v___f_200_);
    return v___x_201_;
}
pub unsafe fn l_WellFounded_partialExtrinsicFix___redArg(
    mut v_F_202_: *mut leanh::LeanObject,
    mut v_a_203_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_204_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_205_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_204_ = leanh::lean_alloc_closure(
        l_WellFounded_partialExtrinsicFix___redArg___lam__1 as *mut core::ffi::c_void,
        3,
        1,
    );
    leanh::lean_closure_set(v___f_204_, 0, v_F_202_);
    v___x_205_ =
        l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix___redArg(v___f_204_, v_a_203_);
    return v___x_205_;
}
pub unsafe fn l_WellFounded_partialExtrinsicFix(
    mut v_00_u03b1_206_: *mut leanh::LeanObject,
    mut v_C_207_: *mut leanh::LeanObject,
    mut v_inst_208_: *mut leanh::LeanObject,
    mut v_R_209_: *mut leanh::LeanObject,
    mut v_F_210_: *mut leanh::LeanObject,
    mut v_a_211_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_212_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_213_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_212_ = leanh::lean_alloc_closure(
        l_WellFounded_partialExtrinsicFix___redArg___lam__1 as *mut core::ffi::c_void,
        3,
        1,
    );
    leanh::lean_closure_set(v___f_212_, 0, v_F_210_);
    v___x_213_ =
        l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix___redArg(v___f_212_, v_a_211_);
    return v___x_213_;
}
pub unsafe fn l_WellFounded_partialExtrinsicFix_u2082___redArg___lam__0(
    mut v_recur_214_: *mut leanh::LeanObject,
    mut v_a_x27_215_: *mut leanh::LeanObject,
    mut v_b_x27_216_: *mut leanh::LeanObject,
    mut v_hR_217_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_218_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_218_ = leanh::lean_apply_3(
        v_recur_214_,
        v_a_x27_215_,
        v_b_x27_216_,
        leanh::lean_box(0),
    );
    return v___x_218_;
}
pub unsafe fn l_WellFounded_partialExtrinsicFix_u2082___redArg___lam__1(
    mut v_F_219_: *mut leanh::LeanObject,
    mut v_a_220_: *mut leanh::LeanObject,
    mut v_b_221_: *mut leanh::LeanObject,
    mut v_recur_222_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_223_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_224_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_223_ = leanh::lean_alloc_closure(
        l_WellFounded_partialExtrinsicFix_u2082___redArg___lam__0 as *mut core::ffi::c_void,
        4,
        1,
    );
    leanh::lean_closure_set(v___f_223_, 0, v_recur_222_);
    v___x_224_ = leanh::lean_apply_3(v_F_219_, v_a_220_, v_b_221_, v___f_223_);
    return v___x_224_;
}
pub unsafe fn l_WellFounded_partialExtrinsicFix_u2082___redArg(
    mut v_F_225_: *mut leanh::LeanObject,
    mut v_a_226_: *mut leanh::LeanObject,
    mut v_b_227_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_228_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_229_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_228_ = leanh::lean_alloc_closure(
        l_WellFounded_partialExtrinsicFix_u2082___redArg___lam__1 as *mut core::ffi::c_void,
        4,
        1,
    );
    leanh::lean_closure_set(v___f_228_, 0, v_F_225_);
    v___x_229_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___redArg(
        v___f_228_, v_a_226_, v_b_227_,
    );
    return v___x_229_;
}
pub unsafe fn l_WellFounded_partialExtrinsicFix_u2082(
    mut v_00_u03b1_230_: *mut leanh::LeanObject,
    mut v_00_u03b2_231_: *mut leanh::LeanObject,
    mut v_C_u2082_232_: *mut leanh::LeanObject,
    mut v_inst_233_: *mut leanh::LeanObject,
    mut v_R_234_: *mut leanh::LeanObject,
    mut v_F_235_: *mut leanh::LeanObject,
    mut v_a_236_: *mut leanh::LeanObject,
    mut v_b_237_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_238_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_239_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_238_ = leanh::lean_alloc_closure(
        l_WellFounded_partialExtrinsicFix_u2082___redArg___lam__1 as *mut core::ffi::c_void,
        4,
        1,
    );
    leanh::lean_closure_set(v___f_238_, 0, v_F_235_);
    v___x_239_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___redArg(
        v___f_238_, v_a_236_, v_b_237_,
    );
    return v___x_239_;
}
pub unsafe fn l_WellFounded_partialExtrinsicFix_u2083___redArg___lam__0(
    mut v_recur_240_: *mut leanh::LeanObject,
    mut v_a_x27_241_: *mut leanh::LeanObject,
    mut v_b_x27_242_: *mut leanh::LeanObject,
    mut v_c_x27_243_: *mut leanh::LeanObject,
    mut v_hR_244_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_245_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_245_ = leanh::lean_apply_4(
        v_recur_240_,
        v_a_x27_241_,
        v_b_x27_242_,
        v_c_x27_243_,
        leanh::lean_box(0),
    );
    return v___x_245_;
}
pub unsafe fn l_WellFounded_partialExtrinsicFix_u2083___redArg___lam__1(
    mut v_F_246_: *mut leanh::LeanObject,
    mut v_a_247_: *mut leanh::LeanObject,
    mut v_b_248_: *mut leanh::LeanObject,
    mut v_c_249_: *mut leanh::LeanObject,
    mut v_recur_250_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_251_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_252_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_251_ = leanh::lean_alloc_closure(
        l_WellFounded_partialExtrinsicFix_u2083___redArg___lam__0 as *mut core::ffi::c_void,
        5,
        1,
    );
    leanh::lean_closure_set(v___f_251_, 0, v_recur_250_);
    v___x_252_ = leanh::lean_apply_4(v_F_246_, v_a_247_, v_b_248_, v_c_249_, v___f_251_);
    return v___x_252_;
}
pub unsafe fn l_WellFounded_partialExtrinsicFix_u2083___redArg(
    mut v_F_253_: *mut leanh::LeanObject,
    mut v_a_254_: *mut leanh::LeanObject,
    mut v_b_255_: *mut leanh::LeanObject,
    mut v_c_256_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_257_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_258_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_257_ = leanh::lean_alloc_closure(
        l_WellFounded_partialExtrinsicFix_u2083___redArg___lam__1 as *mut core::ffi::c_void,
        5,
        1,
    );
    leanh::lean_closure_set(v___f_257_, 0, v_F_253_);
    v___x_258_ = l_WellFounded_opaqueFix_u2083___redArg(v___f_257_, v_a_254_, v_b_255_, v_c_256_);
    return v___x_258_;
}
pub unsafe fn l_WellFounded_partialExtrinsicFix_u2083(
    mut v_00_u03b1_259_: *mut leanh::LeanObject,
    mut v_00_u03b2_260_: *mut leanh::LeanObject,
    mut v_00_u03b3_261_: *mut leanh::LeanObject,
    mut v_C_u2083_262_: *mut leanh::LeanObject,
    mut v_inst_263_: *mut leanh::LeanObject,
    mut v_R_264_: *mut leanh::LeanObject,
    mut v_F_265_: *mut leanh::LeanObject,
    mut v_a_266_: *mut leanh::LeanObject,
    mut v_b_267_: *mut leanh::LeanObject,
    mut v_c_268_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_269_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_270_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_269_ = leanh::lean_alloc_closure(
        l_WellFounded_partialExtrinsicFix_u2083___redArg___lam__1 as *mut core::ffi::c_void,
        5,
        1,
    );
    leanh::lean_closure_set(v___f_269_, 0, v_F_265_);
    v___x_270_ = l_WellFounded_opaqueFix_u2083___redArg(v___f_269_, v_a_266_, v_b_267_, v_c_268_);
    return v___x_270_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Init_WFExtrinsicFix(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Init_WF(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Classical(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Ext(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_NotationExtra(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Init_WFExtrinsicFix(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_meta_initialized = true;
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Init_WFExtrinsicFix(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Init_WF(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_Classical(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_Ext(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_NotationExtra(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_WFExtrinsicFix(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = meta_initialize_Init_WFExtrinsicFix(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return initialize_Init_WFExtrinsicFix(builtin);
}