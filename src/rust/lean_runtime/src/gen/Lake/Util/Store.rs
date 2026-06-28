// Lean compiler output
// Module: Lake.Util.Store
// Imports: Init.Prelude
use crate::r#gen::Init::Prelude::{initialize_Init_Prelude, runtime_initialize_Init_Prelude};
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_alloc_closure, lean_alloc_ctor, lean_apply_1,
    lean_apply_2, lean_apply_4, lean_box, lean_closure_set, lean_ctor_get, lean_ctor_set, lean_dec,
    lean_dec_ref, lean_dec_ref_known, lean_inc, lean_inc_n, lean_inc_ref, lean_io_result_is_error,
    lean_io_result_mk_ok, lean_is_exclusive, lean_obj_tag,
};
pub unsafe fn l_Lake_instMonadStore1OfMonadStore1Of___redArg(
    mut v_inst_124_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_fetch_x3f_125_: *mut LeanObject = core::ptr::null_mut();
    let mut v_store_126_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_128_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_129_: u8 = 0;
    let mut v___x_131_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_132_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_133_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_fetch_x3f_125_ = lean_ctor_get(v_inst_124_, 0);
                v_store_126_ = lean_ctor_get(v_inst_124_, 1);
                v_isSharedCheck_133_ = (!lean_is_exclusive(v_inst_124_)) as u8;
                if v_isSharedCheck_133_ == 0 {
                    v___x_128_ = v_inst_124_;
                    v_isShared_129_ = v_isSharedCheck_133_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_store_126_);
                    lean_inc(v_fetch_x3f_125_);
                    lean_dec(v_inst_124_);
                    v___x_128_ = lean_box(0);
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
                    v_reuseFailAlloc_132_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_132_, 0, v_fetch_x3f_125_);
                    lean_ctor_set(v_reuseFailAlloc_132_, 1, v_store_126_);
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
    mut v_00_u03ba_134_: *mut LeanObject,
    mut v_k_135_: *mut LeanObject,
    mut v_00_u03b1_136_: *mut LeanObject,
    mut v_m_137_: *mut LeanObject,
    mut v_inst_138_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_139_: *mut LeanObject = core::ptr::null_mut();
    v___x_139_ = l_Lake_instMonadStore1OfMonadStore1Of___redArg(v_inst_138_);
    return v___x_139_;
}
pub unsafe fn l_Lake_instMonadStore1OfMonadStore1Of___boxed(
    mut v_00_u03ba_140_: *mut LeanObject,
    mut v_k_141_: *mut LeanObject,
    mut v_00_u03b1_142_: *mut LeanObject,
    mut v_m_143_: *mut LeanObject,
    mut v_inst_144_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_145_: *mut LeanObject = core::ptr::null_mut();
    v_res_145_ = l_Lake_instMonadStore1OfMonadStore1Of(
        v_00_u03ba_140_,
        v_k_141_,
        v_00_u03b1_142_,
        v_m_143_,
        v_inst_144_,
    );
    lean_dec(v_k_141_);
    return v_res_145_;
}
pub unsafe fn l_Lake_instMonadStore1OfOfMonadDStore___redArg___lam__0(
    mut v_store_146_: *mut LeanObject,
    mut v_k_147_: *mut LeanObject,
    mut v_o_148_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_149_: *mut LeanObject = core::ptr::null_mut();
    v___x_149_ = lean_apply_2(v_store_146_, v_k_147_, v_o_148_);
    return v___x_149_;
}
pub unsafe fn l_Lake_instMonadStore1OfOfMonadDStore___redArg(
    mut v_k_150_: *mut LeanObject,
    mut v_inst_151_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_fetch_x3f_152_: *mut LeanObject = core::ptr::null_mut();
    let mut v_store_153_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_155_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_156_: u8 = 0;
    let mut v___f_157_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_158_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_160_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_161_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_162_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_fetch_x3f_152_ = lean_ctor_get(v_inst_151_, 0);
                v_store_153_ = lean_ctor_get(v_inst_151_, 1);
                v_isSharedCheck_162_ = (!lean_is_exclusive(v_inst_151_)) as u8;
                if v_isSharedCheck_162_ == 0 {
                    v___x_155_ = v_inst_151_;
                    v_isShared_156_ = v_isSharedCheck_162_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_store_153_);
                    lean_inc(v_fetch_x3f_152_);
                    lean_dec(v_inst_151_);
                    v___x_155_ = lean_box(0);
                    v_isShared_156_ = v_isSharedCheck_162_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                lean_inc(v_k_150_);
                v___f_157_ = lean_alloc_closure(
                    l_Lake_instMonadStore1OfOfMonadDStore___redArg___lam__0
                        as *mut core::ffi::c_void,
                    3,
                    2,
                );
                lean_closure_set(v___f_157_, 0, v_store_153_);
                lean_closure_set(v___f_157_, 1, v_k_150_);
                v___x_158_ = lean_apply_1(v_fetch_x3f_152_, v_k_150_);
                if v_isShared_156_ == 0 {
                    lean_ctor_set(v___x_155_, 1, v___f_157_);
                    lean_ctor_set(v___x_155_, 0, v___x_158_);
                    v___x_160_ = v___x_155_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_161_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_161_, 0, v___x_158_);
                    lean_ctor_set(v_reuseFailAlloc_161_, 1, v___f_157_);
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
    mut v_00_u03ba_163_: *mut LeanObject,
    mut v_00_u03b2_164_: *mut LeanObject,
    mut v_m_165_: *mut LeanObject,
    mut v_k_166_: *mut LeanObject,
    mut v_inst_167_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_168_: *mut LeanObject = core::ptr::null_mut();
    v___x_168_ = l_Lake_instMonadStore1OfOfMonadDStore___redArg(v_k_166_, v_inst_167_);
    return v___x_168_;
}
pub unsafe fn l_Lake_instMonadDStoreOfMonadLift___redArg___lam__0(
    mut v_inst_169_: *mut LeanObject,
    mut v_inst_170_: *mut LeanObject,
    mut v_k_171_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_fetch_x3f_172_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_173_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_174_: *mut LeanObject = core::ptr::null_mut();
    v_fetch_x3f_172_ = lean_ctor_get(v_inst_169_, 0);
    lean_inc(v_fetch_x3f_172_);
    lean_dec_ref(v_inst_169_);
    v___x_173_ = lean_apply_1(v_fetch_x3f_172_, v_k_171_);
    v___x_174_ = lean_apply_2(v_inst_170_, lean_box(0), v___x_173_);
    return v___x_174_;
}
pub unsafe fn l_Lake_instMonadDStoreOfMonadLift___redArg___lam__1(
    mut v_inst_175_: *mut LeanObject,
    mut v_inst_176_: *mut LeanObject,
    mut v_k_177_: *mut LeanObject,
    mut v_a_178_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_store_179_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_180_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_181_: *mut LeanObject = core::ptr::null_mut();
    v_store_179_ = lean_ctor_get(v_inst_175_, 1);
    lean_inc(v_store_179_);
    lean_dec_ref(v_inst_175_);
    v___x_180_ = lean_apply_2(v_store_179_, v_k_177_, v_a_178_);
    v___x_181_ = lean_apply_2(v_inst_176_, lean_box(0), v___x_180_);
    return v___x_181_;
}
pub unsafe fn l_Lake_instMonadDStoreOfMonadLift___redArg(
    mut v_inst_182_: *mut LeanObject,
    mut v_inst_183_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_184_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_185_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_186_: *mut LeanObject = core::ptr::null_mut();
    lean_inc(v_inst_182_);
    lean_inc_ref(v_inst_183_);
    v___f_184_ = lean_alloc_closure(
        l_Lake_instMonadDStoreOfMonadLift___redArg___lam__0 as *mut core::ffi::c_void,
        3,
        2,
    );
    lean_closure_set(v___f_184_, 0, v_inst_183_);
    lean_closure_set(v___f_184_, 1, v_inst_182_);
    v___f_185_ = lean_alloc_closure(
        l_Lake_instMonadDStoreOfMonadLift___redArg___lam__1 as *mut core::ffi::c_void,
        4,
        2,
    );
    lean_closure_set(v___f_185_, 0, v_inst_183_);
    lean_closure_set(v___f_185_, 1, v_inst_182_);
    v___x_186_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_186_, 0, v___f_184_);
    lean_ctor_set(v___x_186_, 1, v___f_185_);
    return v___x_186_;
}
pub unsafe fn l_Lake_instMonadDStoreOfMonadLift(
    mut v_m_187_: *mut LeanObject,
    mut v_n_188_: *mut LeanObject,
    mut v_00_u03ba_189_: *mut LeanObject,
    mut v_00_u03b2_190_: *mut LeanObject,
    mut v_inst_191_: *mut LeanObject,
    mut v_inst_192_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_193_: *mut LeanObject = core::ptr::null_mut();
    v___x_193_ = l_Lake_instMonadDStoreOfMonadLift___redArg(v_inst_191_, v_inst_192_);
    return v___x_193_;
}
pub unsafe fn l_Lake_fetchOrCreate___redArg___lam__0(
    mut v_toPure_194_: *mut LeanObject,
    mut v_val_195_: *mut LeanObject,
    mut v_____r_196_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_197_: *mut LeanObject = core::ptr::null_mut();
    v___x_197_ = lean_apply_2(v_toPure_194_, lean_box(0), v_val_195_);
    return v___x_197_;
}
pub unsafe fn l_Lake_fetchOrCreate___redArg___lam__1(
    mut v_toPure_198_: *mut LeanObject,
    mut v_store_199_: *mut LeanObject,
    mut v_toBind_200_: *mut LeanObject,
    mut v_val_201_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_202_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_203_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_204_: *mut LeanObject = core::ptr::null_mut();
    lean_inc(v_val_201_);
    v___f_202_ = lean_alloc_closure(
        l_Lake_fetchOrCreate___redArg___lam__0 as *mut core::ffi::c_void,
        3,
        2,
    );
    lean_closure_set(v___f_202_, 0, v_toPure_198_);
    lean_closure_set(v___f_202_, 1, v_val_201_);
    v___x_203_ = lean_apply_1(v_store_199_, v_val_201_);
    v___x_204_ = lean_apply_4(
        v_toBind_200_,
        lean_box(0),
        lean_box(0),
        v___x_203_,
        v___f_202_,
    );
    return v___x_204_;
}
pub unsafe fn l_Lake_fetchOrCreate___redArg___lam__2(
    mut v_toBind_205_: *mut LeanObject,
    mut v_create_206_: *mut LeanObject,
    mut v___f_207_: *mut LeanObject,
    mut v_toPure_208_: *mut LeanObject,
    mut v_____do__lift_209_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_____do__lift_209_) == 0 {
        let mut v___x_210_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_toPure_208_);
        v___x_210_ = lean_apply_4(
            v_toBind_205_,
            lean_box(0),
            lean_box(0),
            v_create_206_,
            v___f_207_,
        );
        return v___x_210_;
    } else {
        let mut v_val_211_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_212_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v___f_207_);
        lean_dec(v_create_206_);
        lean_dec(v_toBind_205_);
        v_val_211_ = lean_ctor_get(v_____do__lift_209_, 0);
        lean_inc(v_val_211_);
        lean_dec_ref_known(v_____do__lift_209_, 1);
        v___x_212_ = lean_apply_2(v_toPure_208_, lean_box(0), v_val_211_);
        return v___x_212_;
    }
}
pub unsafe fn l_Lake_fetchOrCreate___redArg(
    mut v_inst_213_: *mut LeanObject,
    mut v_inst_214_: *mut LeanObject,
    mut v_create_215_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toApplicative_216_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toBind_217_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fetch_x3f_218_: *mut LeanObject = core::ptr::null_mut();
    let mut v_store_219_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toPure_220_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_221_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_222_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_223_: *mut LeanObject = core::ptr::null_mut();
    v_toApplicative_216_ = lean_ctor_get(v_inst_213_, 0);
    lean_inc_ref(v_toApplicative_216_);
    v_toBind_217_ = lean_ctor_get(v_inst_213_, 1);
    lean_inc_n(v_toBind_217_, 3);
    lean_dec_ref(v_inst_213_);
    v_fetch_x3f_218_ = lean_ctor_get(v_inst_214_, 0);
    lean_inc(v_fetch_x3f_218_);
    v_store_219_ = lean_ctor_get(v_inst_214_, 1);
    lean_inc(v_store_219_);
    lean_dec_ref(v_inst_214_);
    v_toPure_220_ = lean_ctor_get(v_toApplicative_216_, 1);
    lean_inc_n(v_toPure_220_, 2);
    lean_dec_ref(v_toApplicative_216_);
    v___f_221_ = lean_alloc_closure(
        l_Lake_fetchOrCreate___redArg___lam__1 as *mut core::ffi::c_void,
        4,
        3,
    );
    lean_closure_set(v___f_221_, 0, v_toPure_220_);
    lean_closure_set(v___f_221_, 1, v_store_219_);
    lean_closure_set(v___f_221_, 2, v_toBind_217_);
    v___f_222_ = lean_alloc_closure(
        l_Lake_fetchOrCreate___redArg___lam__2 as *mut core::ffi::c_void,
        5,
        4,
    );
    lean_closure_set(v___f_222_, 0, v_toBind_217_);
    lean_closure_set(v___f_222_, 1, v_create_215_);
    lean_closure_set(v___f_222_, 2, v___f_221_);
    lean_closure_set(v___f_222_, 3, v_toPure_220_);
    v___x_223_ = lean_apply_4(
        v_toBind_217_,
        lean_box(0),
        lean_box(0),
        v_fetch_x3f_218_,
        v___f_222_,
    );
    return v___x_223_;
}
pub unsafe fn l_Lake_fetchOrCreate(
    mut v_m_224_: *mut LeanObject,
    mut v_00_u03ba_225_: *mut LeanObject,
    mut v_00_u03b1_226_: *mut LeanObject,
    mut v_inst_227_: *mut LeanObject,
    mut v_key_228_: *mut LeanObject,
    mut v_inst_229_: *mut LeanObject,
    mut v_create_230_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toApplicative_231_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toBind_232_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fetch_x3f_233_: *mut LeanObject = core::ptr::null_mut();
    let mut v_store_234_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toPure_235_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_236_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_237_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_238_: *mut LeanObject = core::ptr::null_mut();
    v_toApplicative_231_ = lean_ctor_get(v_inst_227_, 0);
    lean_inc_ref(v_toApplicative_231_);
    v_toBind_232_ = lean_ctor_get(v_inst_227_, 1);
    lean_inc_n(v_toBind_232_, 3);
    lean_dec_ref(v_inst_227_);
    v_fetch_x3f_233_ = lean_ctor_get(v_inst_229_, 0);
    lean_inc(v_fetch_x3f_233_);
    v_store_234_ = lean_ctor_get(v_inst_229_, 1);
    lean_inc(v_store_234_);
    lean_dec_ref(v_inst_229_);
    v_toPure_235_ = lean_ctor_get(v_toApplicative_231_, 1);
    lean_inc_n(v_toPure_235_, 2);
    lean_dec_ref(v_toApplicative_231_);
    v___f_236_ = lean_alloc_closure(
        l_Lake_fetchOrCreate___redArg___lam__1 as *mut core::ffi::c_void,
        4,
        3,
    );
    lean_closure_set(v___f_236_, 0, v_toPure_235_);
    lean_closure_set(v___f_236_, 1, v_store_234_);
    lean_closure_set(v___f_236_, 2, v_toBind_232_);
    v___f_237_ = lean_alloc_closure(
        l_Lake_fetchOrCreate___redArg___lam__2 as *mut core::ffi::c_void,
        5,
        4,
    );
    lean_closure_set(v___f_237_, 0, v_toBind_232_);
    lean_closure_set(v___f_237_, 1, v_create_230_);
    lean_closure_set(v___f_237_, 2, v___f_236_);
    lean_closure_set(v___f_237_, 3, v_toPure_235_);
    v___x_238_ = lean_apply_4(
        v_toBind_232_,
        lean_box(0),
        lean_box(0),
        v_fetch_x3f_233_,
        v___f_237_,
    );
    return v___x_238_;
}
pub unsafe fn l_Lake_fetchOrCreate___boxed(
    mut v_m_239_: *mut LeanObject,
    mut v_00_u03ba_240_: *mut LeanObject,
    mut v_00_u03b1_241_: *mut LeanObject,
    mut v_inst_242_: *mut LeanObject,
    mut v_key_243_: *mut LeanObject,
    mut v_inst_244_: *mut LeanObject,
    mut v_create_245_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_246_: *mut LeanObject = core::ptr::null_mut();
    v_res_246_ = l_Lake_fetchOrCreate(
        v_m_239_,
        v_00_u03ba_240_,
        v_00_u03b1_241_,
        v_inst_242_,
        v_key_243_,
        v_inst_244_,
        v_create_245_,
    );
    lean_dec(v_key_243_);
    return v_res_246_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lake_Util_Store(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Init_Prelude(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lake_Util_Store(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_meta_initialized = true;
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lake_Util_Store(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Init_Prelude(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lake_Util_Store(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Lake_Util_Store(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Lake_Util_Store(builtin);
}
