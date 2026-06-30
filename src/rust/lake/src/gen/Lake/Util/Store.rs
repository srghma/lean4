// Lean compiler output
// Module: Lake.Util.Store
// Imports: Init.Prelude
use crate::r#gen::Init::Prelude::{initialize_Init_Prelude, runtime_initialize_Init_Prelude};
pub unsafe fn l_Lake_instMonadStore1OfMonadStore1Of___redArg(
    mut v_inst_124_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_fetch_x3f_125_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_store_126_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_128_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_129_: u8 = 0;
    let mut v___x_131_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_132_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_133_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_fetch_x3f_125_ = leanh::lean_ctor_get(v_inst_124_, 0);
                v_store_126_ = leanh::lean_ctor_get(v_inst_124_, 1);
                v_isSharedCheck_133_ = (!leanh::lean_is_exclusive(v_inst_124_)) as u8;
                if v_isSharedCheck_133_ == 0 {
                    v___x_128_ = v_inst_124_;
                    v_isShared_129_ = v_isSharedCheck_133_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_store_126_);
                    leanh::lean_inc(v_fetch_x3f_125_);
                    leanh::lean_dec(v_inst_124_);
                    v___x_128_ = leanh::lean_box(0);
                    v_isShared_129_ = v_isSharedCheck_133_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                if v_isShared_129_ == 0 {
                    v___x_131_ = v___x_128_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_132_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_132_, 0, v_fetch_x3f_125_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_132_, 1, v_store_126_);
                    v___x_131_ = v_reuseFailAlloc_132_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_131_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lake_instMonadStore1OfMonadStore1Of(
    mut v_00_u03ba_134_: *mut leanh::LeanObject,
    mut v_k_135_: *mut leanh::LeanObject,
    mut v_00_u03b1_136_: *mut leanh::LeanObject,
    mut v_m_137_: *mut leanh::LeanObject,
    mut v_inst_138_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_139_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_139_ = l_Lake_instMonadStore1OfMonadStore1Of___redArg(v_inst_138_);
    return v___x_139_;
}
pub unsafe fn l_Lake_instMonadStore1OfMonadStore1Of___boxed(
    mut v_00_u03ba_140_: *mut leanh::LeanObject,
    mut v_k_141_: *mut leanh::LeanObject,
    mut v_00_u03b1_142_: *mut leanh::LeanObject,
    mut v_m_143_: *mut leanh::LeanObject,
    mut v_inst_144_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_145_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_145_ = l_Lake_instMonadStore1OfMonadStore1Of(
        v_00_u03ba_140_,
        v_k_141_,
        v_00_u03b1_142_,
        v_m_143_,
        v_inst_144_,
    );
    leanh::lean_dec(v_k_141_);
    return v_res_145_;
}
pub unsafe fn l_Lake_instMonadStore1OfOfMonadDStore___redArg___lam__0(
    mut v_store_146_: *mut leanh::LeanObject,
    mut v_k_147_: *mut leanh::LeanObject,
    mut v_o_148_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_149_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_149_ = leanh::lean_apply_2(v_store_146_, v_k_147_, v_o_148_);
    return v___x_149_;
}
pub unsafe fn l_Lake_instMonadStore1OfOfMonadDStore___redArg(
    mut v_k_150_: *mut leanh::LeanObject,
    mut v_inst_151_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_fetch_x3f_152_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_store_153_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_155_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_156_: u8 = 0;
    let mut v___f_157_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_158_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_160_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_161_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_162_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_fetch_x3f_152_ = leanh::lean_ctor_get(v_inst_151_, 0);
                v_store_153_ = leanh::lean_ctor_get(v_inst_151_, 1);
                v_isSharedCheck_162_ = (!leanh::lean_is_exclusive(v_inst_151_)) as u8;
                if v_isSharedCheck_162_ == 0 {
                    v___x_155_ = v_inst_151_;
                    v_isShared_156_ = v_isSharedCheck_162_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_store_153_);
                    leanh::lean_inc(v_fetch_x3f_152_);
                    leanh::lean_dec(v_inst_151_);
                    v___x_155_ = leanh::lean_box(0);
                    v_isShared_156_ = v_isSharedCheck_162_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                leanh::lean_inc(v_k_150_);
                v___f_157_ = leanh::lean_alloc_closure(
                    l_Lake_instMonadStore1OfOfMonadDStore___redArg___lam__0
                        as *mut core::ffi::c_void,
                    3,
                    2,
                );
                leanh::lean_closure_set(v___f_157_, 0, v_store_153_);
                leanh::lean_closure_set(v___f_157_, 1, v_k_150_);
                v___x_158_ = leanh::lean_apply_1(v_fetch_x3f_152_, v_k_150_);
                if v_isShared_156_ == 0 {
                    leanh::lean_ctor_set(v___x_155_, 1, v___f_157_);
                    leanh::lean_ctor_set(v___x_155_, 0, v___x_158_);
                    v___x_160_ = v___x_155_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_161_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_161_, 0, v___x_158_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_161_, 1, v___f_157_);
                    v___x_160_ = v_reuseFailAlloc_161_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_160_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lake_instMonadStore1OfOfMonadDStore(
    mut v_00_u03ba_163_: *mut leanh::LeanObject,
    mut v_00_u03b2_164_: *mut leanh::LeanObject,
    mut v_m_165_: *mut leanh::LeanObject,
    mut v_k_166_: *mut leanh::LeanObject,
    mut v_inst_167_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_168_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_168_ = l_Lake_instMonadStore1OfOfMonadDStore___redArg(v_k_166_, v_inst_167_);
    return v___x_168_;
}
pub unsafe fn l_Lake_instMonadDStoreOfMonadLift___redArg___lam__0(
    mut v_inst_169_: *mut leanh::LeanObject,
    mut v_inst_170_: *mut leanh::LeanObject,
    mut v_k_171_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_fetch_x3f_172_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_173_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_174_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_fetch_x3f_172_ = leanh::lean_ctor_get(v_inst_169_, 0);
    leanh::lean_inc(v_fetch_x3f_172_);
    leanh::lean_dec_ref(v_inst_169_);
    v___x_173_ = leanh::lean_apply_1(v_fetch_x3f_172_, v_k_171_);
    v___x_174_ = leanh::lean_apply_2(v_inst_170_, leanh::lean_box(0), v___x_173_);
    return v___x_174_;
}
pub unsafe fn l_Lake_instMonadDStoreOfMonadLift___redArg___lam__1(
    mut v_inst_175_: *mut leanh::LeanObject,
    mut v_inst_176_: *mut leanh::LeanObject,
    mut v_k_177_: *mut leanh::LeanObject,
    mut v_a_178_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_store_179_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_180_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_181_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_store_179_ = leanh::lean_ctor_get(v_inst_175_, 1);
    leanh::lean_inc(v_store_179_);
    leanh::lean_dec_ref(v_inst_175_);
    v___x_180_ = leanh::lean_apply_2(v_store_179_, v_k_177_, v_a_178_);
    v___x_181_ = leanh::lean_apply_2(v_inst_176_, leanh::lean_box(0), v___x_180_);
    return v___x_181_;
}
pub unsafe fn l_Lake_instMonadDStoreOfMonadLift___redArg(
    mut v_inst_182_: *mut leanh::LeanObject,
    mut v_inst_183_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_184_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_185_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_186_: *mut leanh::LeanObject = core::ptr::null_mut();
    leanh::lean_inc(v_inst_182_);
    leanh::lean_inc_ref(v_inst_183_);
    v___f_184_ = leanh::lean_alloc_closure(
        l_Lake_instMonadDStoreOfMonadLift___redArg___lam__0 as *mut core::ffi::c_void,
        3,
        2,
    );
    leanh::lean_closure_set(v___f_184_, 0, v_inst_183_);
    leanh::lean_closure_set(v___f_184_, 1, v_inst_182_);
    v___f_185_ = leanh::lean_alloc_closure(
        l_Lake_instMonadDStoreOfMonadLift___redArg___lam__1 as *mut core::ffi::c_void,
        4,
        2,
    );
    leanh::lean_closure_set(v___f_185_, 0, v_inst_183_);
    leanh::lean_closure_set(v___f_185_, 1, v_inst_182_);
    v___x_186_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_186_, 0, v___f_184_);
    leanh::lean_ctor_set(v___x_186_, 1, v___f_185_);
    return v___x_186_;
}
pub unsafe fn l_Lake_instMonadDStoreOfMonadLift(
    mut v_m_187_: *mut leanh::LeanObject,
    mut v_n_188_: *mut leanh::LeanObject,
    mut v_00_u03ba_189_: *mut leanh::LeanObject,
    mut v_00_u03b2_190_: *mut leanh::LeanObject,
    mut v_inst_191_: *mut leanh::LeanObject,
    mut v_inst_192_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_193_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_193_ = l_Lake_instMonadDStoreOfMonadLift___redArg(v_inst_191_, v_inst_192_);
    return v___x_193_;
}
pub unsafe fn l_Lake_fetchOrCreate___redArg___lam__0(
    mut v_toPure_194_: *mut leanh::LeanObject,
    mut v_val_195_: *mut leanh::LeanObject,
    mut v_____r_196_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_197_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_197_ = leanh::lean_apply_2(v_toPure_194_, leanh::lean_box(0), v_val_195_);
    return v___x_197_;
}
pub unsafe fn l_Lake_fetchOrCreate___redArg___lam__1(
    mut v_toPure_198_: *mut leanh::LeanObject,
    mut v_store_199_: *mut leanh::LeanObject,
    mut v_toBind_200_: *mut leanh::LeanObject,
    mut v_val_201_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_202_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_203_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_204_: *mut leanh::LeanObject = core::ptr::null_mut();
    leanh::lean_inc(v_val_201_);
    v___f_202_ = leanh::lean_alloc_closure(
        l_Lake_fetchOrCreate___redArg___lam__0 as *mut core::ffi::c_void,
        3,
        2,
    );
    leanh::lean_closure_set(v___f_202_, 0, v_toPure_198_);
    leanh::lean_closure_set(v___f_202_, 1, v_val_201_);
    v___x_203_ = leanh::lean_apply_1(v_store_199_, v_val_201_);
    v___x_204_ = leanh::lean_apply_4(
        v_toBind_200_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v___x_203_,
        v___f_202_,
    );
    return v___x_204_;
}
pub unsafe fn l_Lake_fetchOrCreate___redArg___lam__2(
    mut v_toBind_205_: *mut leanh::LeanObject,
    mut v_create_206_: *mut leanh::LeanObject,
    mut v___f_207_: *mut leanh::LeanObject,
    mut v_toPure_208_: *mut leanh::LeanObject,
    mut v_____do__lift_209_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_____do__lift_209_) == 0 {
        let mut v___x_210_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_toPure_208_);
        v___x_210_ = leanh::lean_apply_4(
            v_toBind_205_,
            leanh::lean_box(0),
            leanh::lean_box(0),
            v_create_206_,
            v___f_207_,
        );
        return v___x_210_;
    } else {
        let mut v_val_211_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_212_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v___f_207_);
        leanh::lean_dec(v_create_206_);
        leanh::lean_dec(v_toBind_205_);
        v_val_211_ = leanh::lean_ctor_get(v_____do__lift_209_, 0);
        leanh::lean_inc(v_val_211_);
        leanh::lean_dec_ref_known(v_____do__lift_209_, 1);
        v___x_212_ =
            leanh::lean_apply_2(v_toPure_208_, leanh::lean_box(0), v_val_211_);
        return v___x_212_;
    }
}
pub unsafe fn l_Lake_fetchOrCreate___redArg(
    mut v_inst_213_: *mut leanh::LeanObject,
    mut v_inst_214_: *mut leanh::LeanObject,
    mut v_create_215_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_toApplicative_216_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_217_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fetch_x3f_218_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_store_219_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_220_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_221_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_222_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_223_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_216_ = leanh::lean_ctor_get(v_inst_213_, 0);
    leanh::lean_inc_ref(v_toApplicative_216_);
    v_toBind_217_ = leanh::lean_ctor_get(v_inst_213_, 1);
    leanh::lean_inc_n(v_toBind_217_, 3);
    leanh::lean_dec_ref(v_inst_213_);
    v_fetch_x3f_218_ = leanh::lean_ctor_get(v_inst_214_, 0);
    leanh::lean_inc(v_fetch_x3f_218_);
    v_store_219_ = leanh::lean_ctor_get(v_inst_214_, 1);
    leanh::lean_inc(v_store_219_);
    leanh::lean_dec_ref(v_inst_214_);
    v_toPure_220_ = leanh::lean_ctor_get(v_toApplicative_216_, 1);
    leanh::lean_inc_n(v_toPure_220_, 2);
    leanh::lean_dec_ref(v_toApplicative_216_);
    v___f_221_ = leanh::lean_alloc_closure(
        l_Lake_fetchOrCreate___redArg___lam__1 as *mut core::ffi::c_void,
        4,
        3,
    );
    leanh::lean_closure_set(v___f_221_, 0, v_toPure_220_);
    leanh::lean_closure_set(v___f_221_, 1, v_store_219_);
    leanh::lean_closure_set(v___f_221_, 2, v_toBind_217_);
    v___f_222_ = leanh::lean_alloc_closure(
        l_Lake_fetchOrCreate___redArg___lam__2 as *mut core::ffi::c_void,
        5,
        4,
    );
    leanh::lean_closure_set(v___f_222_, 0, v_toBind_217_);
    leanh::lean_closure_set(v___f_222_, 1, v_create_215_);
    leanh::lean_closure_set(v___f_222_, 2, v___f_221_);
    leanh::lean_closure_set(v___f_222_, 3, v_toPure_220_);
    v___x_223_ = leanh::lean_apply_4(
        v_toBind_217_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v_fetch_x3f_218_,
        v___f_222_,
    );
    return v___x_223_;
}
pub unsafe fn l_Lake_fetchOrCreate(
    mut v_m_224_: *mut leanh::LeanObject,
    mut v_00_u03ba_225_: *mut leanh::LeanObject,
    mut v_00_u03b1_226_: *mut leanh::LeanObject,
    mut v_inst_227_: *mut leanh::LeanObject,
    mut v_key_228_: *mut leanh::LeanObject,
    mut v_inst_229_: *mut leanh::LeanObject,
    mut v_create_230_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_toApplicative_231_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_232_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fetch_x3f_233_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_store_234_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_235_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_236_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_237_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_238_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_231_ = leanh::lean_ctor_get(v_inst_227_, 0);
    leanh::lean_inc_ref(v_toApplicative_231_);
    v_toBind_232_ = leanh::lean_ctor_get(v_inst_227_, 1);
    leanh::lean_inc_n(v_toBind_232_, 3);
    leanh::lean_dec_ref(v_inst_227_);
    v_fetch_x3f_233_ = leanh::lean_ctor_get(v_inst_229_, 0);
    leanh::lean_inc(v_fetch_x3f_233_);
    v_store_234_ = leanh::lean_ctor_get(v_inst_229_, 1);
    leanh::lean_inc(v_store_234_);
    leanh::lean_dec_ref(v_inst_229_);
    v_toPure_235_ = leanh::lean_ctor_get(v_toApplicative_231_, 1);
    leanh::lean_inc_n(v_toPure_235_, 2);
    leanh::lean_dec_ref(v_toApplicative_231_);
    v___f_236_ = leanh::lean_alloc_closure(
        l_Lake_fetchOrCreate___redArg___lam__1 as *mut core::ffi::c_void,
        4,
        3,
    );
    leanh::lean_closure_set(v___f_236_, 0, v_toPure_235_);
    leanh::lean_closure_set(v___f_236_, 1, v_store_234_);
    leanh::lean_closure_set(v___f_236_, 2, v_toBind_232_);
    v___f_237_ = leanh::lean_alloc_closure(
        l_Lake_fetchOrCreate___redArg___lam__2 as *mut core::ffi::c_void,
        5,
        4,
    );
    leanh::lean_closure_set(v___f_237_, 0, v_toBind_232_);
    leanh::lean_closure_set(v___f_237_, 1, v_create_230_);
    leanh::lean_closure_set(v___f_237_, 2, v___f_236_);
    leanh::lean_closure_set(v___f_237_, 3, v_toPure_235_);
    v___x_238_ = leanh::lean_apply_4(
        v_toBind_232_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v_fetch_x3f_233_,
        v___f_237_,
    );
    return v___x_238_;
}
pub unsafe fn l_Lake_fetchOrCreate___boxed(
    mut v_m_239_: *mut leanh::LeanObject,
    mut v_00_u03ba_240_: *mut leanh::LeanObject,
    mut v_00_u03b1_241_: *mut leanh::LeanObject,
    mut v_inst_242_: *mut leanh::LeanObject,
    mut v_key_243_: *mut leanh::LeanObject,
    mut v_inst_244_: *mut leanh::LeanObject,
    mut v_create_245_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_246_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_246_ = l_Lake_fetchOrCreate(
        v_m_239_,
        v_00_u03ba_240_,
        v_00_u03b1_241_,
        v_inst_242_,
        v_key_243_,
        v_inst_244_,
        v_create_245_,
    );
    leanh::lean_dec(v_key_243_);
    return v_res_246_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lake_Util_Store(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Init_Prelude(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lake_Util_Store(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_meta_initialized = true;
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lake_Util_Store(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Init_Prelude(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lake_Util_Store(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = meta_initialize_Lake_Util_Store(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return initialize_Lake_Util_Store(builtin);
}