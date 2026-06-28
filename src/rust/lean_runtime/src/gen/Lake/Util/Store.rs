// Lean compiler output
// Module: Lake.Util.Store
// Imports: Init.Prelude
use crate::r#gen::Init::Prelude::{initialize_Init_Prelude, runtime_initialize_Init_Prelude};
pub unsafe fn l_Lake_instMonadStore1OfMonadStore1Of___redArg(
    mut v_inst_124_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_fetch_x3f_125_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_store_126_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_128_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_129_: u8 = 0;
    let mut v___x_131_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_132_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_133_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_fetch_x3f_125_ = crate::leanh::lean_ctor_get(v_inst_124_, 0);
                v_store_126_ = crate::leanh::lean_ctor_get(v_inst_124_, 1);
                v_isSharedCheck_133_ = (!crate::leanh::lean_is_exclusive(v_inst_124_)) as u8;
                if v_isSharedCheck_133_ == 0 {
                    v___x_128_ = v_inst_124_;
                    v_isShared_129_ = v_isSharedCheck_133_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_store_126_);
                    crate::leanh::lean_inc(v_fetch_x3f_125_);
                    crate::leanh::lean_dec(v_inst_124_);
                    v___x_128_ = crate::leanh::lean_box(0);
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
                    v_reuseFailAlloc_132_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_132_, 0, v_fetch_x3f_125_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_132_, 1, v_store_126_);
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
    mut v_00_u03ba_134_: *mut crate::leanh::LeanObject,
    mut v_k_135_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_136_: *mut crate::leanh::LeanObject,
    mut v_m_137_: *mut crate::leanh::LeanObject,
    mut v_inst_138_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_139_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_139_ = l_Lake_instMonadStore1OfMonadStore1Of___redArg(v_inst_138_);
    return v___x_139_;
}
pub unsafe fn l_Lake_instMonadStore1OfMonadStore1Of___boxed(
    mut v_00_u03ba_140_: *mut crate::leanh::LeanObject,
    mut v_k_141_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_142_: *mut crate::leanh::LeanObject,
    mut v_m_143_: *mut crate::leanh::LeanObject,
    mut v_inst_144_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_145_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_145_ = l_Lake_instMonadStore1OfMonadStore1Of(
        v_00_u03ba_140_,
        v_k_141_,
        v_00_u03b1_142_,
        v_m_143_,
        v_inst_144_,
    );
    crate::leanh::lean_dec(v_k_141_);
    return v_res_145_;
}
pub unsafe fn l_Lake_instMonadStore1OfOfMonadDStore___redArg___lam__0(
    mut v_store_146_: *mut crate::leanh::LeanObject,
    mut v_k_147_: *mut crate::leanh::LeanObject,
    mut v_o_148_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_149_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_149_ = crate::leanh::lean_apply_2(v_store_146_, v_k_147_, v_o_148_);
    return v___x_149_;
}
pub unsafe fn l_Lake_instMonadStore1OfOfMonadDStore___redArg(
    mut v_k_150_: *mut crate::leanh::LeanObject,
    mut v_inst_151_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_fetch_x3f_152_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_store_153_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_155_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_156_: u8 = 0;
    let mut v___f_157_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_158_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_160_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_161_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_162_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_fetch_x3f_152_ = crate::leanh::lean_ctor_get(v_inst_151_, 0);
                v_store_153_ = crate::leanh::lean_ctor_get(v_inst_151_, 1);
                v_isSharedCheck_162_ = (!crate::leanh::lean_is_exclusive(v_inst_151_)) as u8;
                if v_isSharedCheck_162_ == 0 {
                    v___x_155_ = v_inst_151_;
                    v_isShared_156_ = v_isSharedCheck_162_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_store_153_);
                    crate::leanh::lean_inc(v_fetch_x3f_152_);
                    crate::leanh::lean_dec(v_inst_151_);
                    v___x_155_ = crate::leanh::lean_box(0);
                    v_isShared_156_ = v_isSharedCheck_162_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                crate::leanh::lean_inc(v_k_150_);
                v___f_157_ = crate::leanh::lean_alloc_closure(
                    l_Lake_instMonadStore1OfOfMonadDStore___redArg___lam__0
                        as *mut core::ffi::c_void,
                    3,
                    2,
                );
                crate::leanh::lean_closure_set(v___f_157_, 0, v_store_153_);
                crate::leanh::lean_closure_set(v___f_157_, 1, v_k_150_);
                v___x_158_ = crate::leanh::lean_apply_1(v_fetch_x3f_152_, v_k_150_);
                if v_isShared_156_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_155_, 1, v___f_157_);
                    crate::leanh::lean_ctor_set(v___x_155_, 0, v___x_158_);
                    v___x_160_ = v___x_155_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_161_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_161_, 0, v___x_158_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_161_, 1, v___f_157_);
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
    mut v_00_u03ba_163_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_164_: *mut crate::leanh::LeanObject,
    mut v_m_165_: *mut crate::leanh::LeanObject,
    mut v_k_166_: *mut crate::leanh::LeanObject,
    mut v_inst_167_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_168_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_168_ = l_Lake_instMonadStore1OfOfMonadDStore___redArg(v_k_166_, v_inst_167_);
    return v___x_168_;
}
pub unsafe fn l_Lake_instMonadDStoreOfMonadLift___redArg___lam__0(
    mut v_inst_169_: *mut crate::leanh::LeanObject,
    mut v_inst_170_: *mut crate::leanh::LeanObject,
    mut v_k_171_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_fetch_x3f_172_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_173_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_174_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_fetch_x3f_172_ = crate::leanh::lean_ctor_get(v_inst_169_, 0);
    crate::leanh::lean_inc(v_fetch_x3f_172_);
    crate::leanh::lean_dec_ref(v_inst_169_);
    v___x_173_ = crate::leanh::lean_apply_1(v_fetch_x3f_172_, v_k_171_);
    v___x_174_ = crate::leanh::lean_apply_2(v_inst_170_, crate::leanh::lean_box(0), v___x_173_);
    return v___x_174_;
}
pub unsafe fn l_Lake_instMonadDStoreOfMonadLift___redArg___lam__1(
    mut v_inst_175_: *mut crate::leanh::LeanObject,
    mut v_inst_176_: *mut crate::leanh::LeanObject,
    mut v_k_177_: *mut crate::leanh::LeanObject,
    mut v_a_178_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_store_179_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_180_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_181_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_store_179_ = crate::leanh::lean_ctor_get(v_inst_175_, 1);
    crate::leanh::lean_inc(v_store_179_);
    crate::leanh::lean_dec_ref(v_inst_175_);
    v___x_180_ = crate::leanh::lean_apply_2(v_store_179_, v_k_177_, v_a_178_);
    v___x_181_ = crate::leanh::lean_apply_2(v_inst_176_, crate::leanh::lean_box(0), v___x_180_);
    return v___x_181_;
}
pub unsafe fn l_Lake_instMonadDStoreOfMonadLift___redArg(
    mut v_inst_182_: *mut crate::leanh::LeanObject,
    mut v_inst_183_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_184_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_185_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_186_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    crate::leanh::lean_inc(v_inst_182_);
    crate::leanh::lean_inc_ref(v_inst_183_);
    v___f_184_ = crate::leanh::lean_alloc_closure(
        l_Lake_instMonadDStoreOfMonadLift___redArg___lam__0 as *mut core::ffi::c_void,
        3,
        2,
    );
    crate::leanh::lean_closure_set(v___f_184_, 0, v_inst_183_);
    crate::leanh::lean_closure_set(v___f_184_, 1, v_inst_182_);
    v___f_185_ = crate::leanh::lean_alloc_closure(
        l_Lake_instMonadDStoreOfMonadLift___redArg___lam__1 as *mut core::ffi::c_void,
        4,
        2,
    );
    crate::leanh::lean_closure_set(v___f_185_, 0, v_inst_183_);
    crate::leanh::lean_closure_set(v___f_185_, 1, v_inst_182_);
    v___x_186_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_186_, 0, v___f_184_);
    crate::leanh::lean_ctor_set(v___x_186_, 1, v___f_185_);
    return v___x_186_;
}
pub unsafe fn l_Lake_instMonadDStoreOfMonadLift(
    mut v_m_187_: *mut crate::leanh::LeanObject,
    mut v_n_188_: *mut crate::leanh::LeanObject,
    mut v_00_u03ba_189_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_190_: *mut crate::leanh::LeanObject,
    mut v_inst_191_: *mut crate::leanh::LeanObject,
    mut v_inst_192_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_193_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_193_ = l_Lake_instMonadDStoreOfMonadLift___redArg(v_inst_191_, v_inst_192_);
    return v___x_193_;
}
pub unsafe fn l_Lake_fetchOrCreate___redArg___lam__0(
    mut v_toPure_194_: *mut crate::leanh::LeanObject,
    mut v_val_195_: *mut crate::leanh::LeanObject,
    mut v_____r_196_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_197_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_197_ = crate::leanh::lean_apply_2(v_toPure_194_, crate::leanh::lean_box(0), v_val_195_);
    return v___x_197_;
}
pub unsafe fn l_Lake_fetchOrCreate___redArg___lam__1(
    mut v_toPure_198_: *mut crate::leanh::LeanObject,
    mut v_store_199_: *mut crate::leanh::LeanObject,
    mut v_toBind_200_: *mut crate::leanh::LeanObject,
    mut v_val_201_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_202_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_203_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_204_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    crate::leanh::lean_inc(v_val_201_);
    v___f_202_ = crate::leanh::lean_alloc_closure(
        l_Lake_fetchOrCreate___redArg___lam__0 as *mut core::ffi::c_void,
        3,
        2,
    );
    crate::leanh::lean_closure_set(v___f_202_, 0, v_toPure_198_);
    crate::leanh::lean_closure_set(v___f_202_, 1, v_val_201_);
    v___x_203_ = crate::leanh::lean_apply_1(v_store_199_, v_val_201_);
    v___x_204_ = crate::leanh::lean_apply_4(
        v_toBind_200_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___x_203_,
        v___f_202_,
    );
    return v___x_204_;
}
pub unsafe fn l_Lake_fetchOrCreate___redArg___lam__2(
    mut v_toBind_205_: *mut crate::leanh::LeanObject,
    mut v_create_206_: *mut crate::leanh::LeanObject,
    mut v___f_207_: *mut crate::leanh::LeanObject,
    mut v_toPure_208_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_209_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_____do__lift_209_) == 0 {
        let mut v___x_210_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_toPure_208_);
        v___x_210_ = crate::leanh::lean_apply_4(
            v_toBind_205_,
            crate::leanh::lean_box(0),
            crate::leanh::lean_box(0),
            v_create_206_,
            v___f_207_,
        );
        return v___x_210_;
    } else {
        let mut v_val_211_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_212_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v___f_207_);
        crate::leanh::lean_dec(v_create_206_);
        crate::leanh::lean_dec(v_toBind_205_);
        v_val_211_ = crate::leanh::lean_ctor_get(v_____do__lift_209_, 0);
        crate::leanh::lean_inc(v_val_211_);
        crate::leanh::lean_dec_ref_known(v_____do__lift_209_, 1);
        v___x_212_ =
            crate::leanh::lean_apply_2(v_toPure_208_, crate::leanh::lean_box(0), v_val_211_);
        return v___x_212_;
    }
}
pub unsafe fn l_Lake_fetchOrCreate___redArg(
    mut v_inst_213_: *mut crate::leanh::LeanObject,
    mut v_inst_214_: *mut crate::leanh::LeanObject,
    mut v_create_215_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toApplicative_216_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_217_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fetch_x3f_218_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_store_219_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_220_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_221_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_222_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_223_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_216_ = crate::leanh::lean_ctor_get(v_inst_213_, 0);
    crate::leanh::lean_inc_ref(v_toApplicative_216_);
    v_toBind_217_ = crate::leanh::lean_ctor_get(v_inst_213_, 1);
    crate::leanh::lean_inc_n(v_toBind_217_, 3);
    crate::leanh::lean_dec_ref(v_inst_213_);
    v_fetch_x3f_218_ = crate::leanh::lean_ctor_get(v_inst_214_, 0);
    crate::leanh::lean_inc(v_fetch_x3f_218_);
    v_store_219_ = crate::leanh::lean_ctor_get(v_inst_214_, 1);
    crate::leanh::lean_inc(v_store_219_);
    crate::leanh::lean_dec_ref(v_inst_214_);
    v_toPure_220_ = crate::leanh::lean_ctor_get(v_toApplicative_216_, 1);
    crate::leanh::lean_inc_n(v_toPure_220_, 2);
    crate::leanh::lean_dec_ref(v_toApplicative_216_);
    v___f_221_ = crate::leanh::lean_alloc_closure(
        l_Lake_fetchOrCreate___redArg___lam__1 as *mut core::ffi::c_void,
        4,
        3,
    );
    crate::leanh::lean_closure_set(v___f_221_, 0, v_toPure_220_);
    crate::leanh::lean_closure_set(v___f_221_, 1, v_store_219_);
    crate::leanh::lean_closure_set(v___f_221_, 2, v_toBind_217_);
    v___f_222_ = crate::leanh::lean_alloc_closure(
        l_Lake_fetchOrCreate___redArg___lam__2 as *mut core::ffi::c_void,
        5,
        4,
    );
    crate::leanh::lean_closure_set(v___f_222_, 0, v_toBind_217_);
    crate::leanh::lean_closure_set(v___f_222_, 1, v_create_215_);
    crate::leanh::lean_closure_set(v___f_222_, 2, v___f_221_);
    crate::leanh::lean_closure_set(v___f_222_, 3, v_toPure_220_);
    v___x_223_ = crate::leanh::lean_apply_4(
        v_toBind_217_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v_fetch_x3f_218_,
        v___f_222_,
    );
    return v___x_223_;
}
pub unsafe fn l_Lake_fetchOrCreate(
    mut v_m_224_: *mut crate::leanh::LeanObject,
    mut v_00_u03ba_225_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_226_: *mut crate::leanh::LeanObject,
    mut v_inst_227_: *mut crate::leanh::LeanObject,
    mut v_key_228_: *mut crate::leanh::LeanObject,
    mut v_inst_229_: *mut crate::leanh::LeanObject,
    mut v_create_230_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toApplicative_231_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_232_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fetch_x3f_233_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_store_234_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_235_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_236_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_237_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_238_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_231_ = crate::leanh::lean_ctor_get(v_inst_227_, 0);
    crate::leanh::lean_inc_ref(v_toApplicative_231_);
    v_toBind_232_ = crate::leanh::lean_ctor_get(v_inst_227_, 1);
    crate::leanh::lean_inc_n(v_toBind_232_, 3);
    crate::leanh::lean_dec_ref(v_inst_227_);
    v_fetch_x3f_233_ = crate::leanh::lean_ctor_get(v_inst_229_, 0);
    crate::leanh::lean_inc(v_fetch_x3f_233_);
    v_store_234_ = crate::leanh::lean_ctor_get(v_inst_229_, 1);
    crate::leanh::lean_inc(v_store_234_);
    crate::leanh::lean_dec_ref(v_inst_229_);
    v_toPure_235_ = crate::leanh::lean_ctor_get(v_toApplicative_231_, 1);
    crate::leanh::lean_inc_n(v_toPure_235_, 2);
    crate::leanh::lean_dec_ref(v_toApplicative_231_);
    v___f_236_ = crate::leanh::lean_alloc_closure(
        l_Lake_fetchOrCreate___redArg___lam__1 as *mut core::ffi::c_void,
        4,
        3,
    );
    crate::leanh::lean_closure_set(v___f_236_, 0, v_toPure_235_);
    crate::leanh::lean_closure_set(v___f_236_, 1, v_store_234_);
    crate::leanh::lean_closure_set(v___f_236_, 2, v_toBind_232_);
    v___f_237_ = crate::leanh::lean_alloc_closure(
        l_Lake_fetchOrCreate___redArg___lam__2 as *mut core::ffi::c_void,
        5,
        4,
    );
    crate::leanh::lean_closure_set(v___f_237_, 0, v_toBind_232_);
    crate::leanh::lean_closure_set(v___f_237_, 1, v_create_230_);
    crate::leanh::lean_closure_set(v___f_237_, 2, v___f_236_);
    crate::leanh::lean_closure_set(v___f_237_, 3, v_toPure_235_);
    v___x_238_ = crate::leanh::lean_apply_4(
        v_toBind_232_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v_fetch_x3f_233_,
        v___f_237_,
    );
    return v___x_238_;
}
pub unsafe fn l_Lake_fetchOrCreate___boxed(
    mut v_m_239_: *mut crate::leanh::LeanObject,
    mut v_00_u03ba_240_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_241_: *mut crate::leanh::LeanObject,
    mut v_inst_242_: *mut crate::leanh::LeanObject,
    mut v_key_243_: *mut crate::leanh::LeanObject,
    mut v_inst_244_: *mut crate::leanh::LeanObject,
    mut v_create_245_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_246_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_246_ = l_Lake_fetchOrCreate(
        v_m_239_,
        v_00_u03ba_240_,
        v_00_u03b1_241_,
        v_inst_242_,
        v_key_243_,
        v_inst_244_,
        v_create_245_,
    );
    crate::leanh::lean_dec(v_key_243_);
    return v_res_246_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lake_Util_Store(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Init_Prelude(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lake_Util_Store(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_meta_initialized = true;
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lake_Util_Store(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Init_Prelude(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lake_Util_Store(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Lake_Util_Store(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Lake_Util_Store(builtin);
}
