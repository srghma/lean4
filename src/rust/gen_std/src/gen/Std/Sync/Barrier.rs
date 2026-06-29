// Lean compiler output
// Module: Std.Sync.Barrier
// Imports: Std.Sync.Mutex
use crate::ffi::{
    lean_io_basemutex_lock, lean_io_basemutex_unlock, lean_io_condvar_new,
    lean_io_condvar_notify_all, lean_io_condvar_wait, lean_nat_add, lean_nat_dec_eq,
    lean_nat_dec_lt, lean_st_ref_get, lean_st_ref_set, lean_st_ref_take,
};
use crate::r#gen::Std::Sync::Mutex::{
    initialize_Std_Sync_Mutex, l_Std_Mutex_new___redArg, runtime_initialize_Std_Sync_Mutex,
};
pub static l_Std_Barrier_new___closed__0_value: crate::leanh::LeanCtorObject<2> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 0,
        },
        m_objs: [
            (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
            (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Std_Barrier_new___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Barrier_new___closed__0_value) as *mut crate::leanh::LeanObject;
pub unsafe fn l_Std_Barrier_new(
    mut v_numThreads_160_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_162_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_163_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_164_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_165_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_162_ = l_Std_Barrier_new___closed__0;
    v___x_163_ = l_Std_Mutex_new___redArg(v___x_162_);
    v___x_164_ = lean_io_condvar_new();
    v___x_165_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_165_, 0, v___x_163_);
    crate::leanh::lean_ctor_set(v___x_165_, 1, v___x_164_);
    crate::leanh::lean_ctor_set(v___x_165_, 2, v_numThreads_160_);
    return v___x_165_;
}
pub unsafe fn l_Std_Barrier_new___boxed(
    mut v_numThreads_166_: *mut crate::leanh::LeanObject,
    mut v_a_167_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_168_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_168_ = l_Std_Barrier_new(v_numThreads_166_);
    return v_res_168_;
}
pub unsafe fn l_Std_Mutex_atomically___at___00Std_Barrier_wait_spec__1___redArg(
    mut v_mutex_169_: *mut crate::leanh::LeanObject,
    mut v_k_170_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_ref_172_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_mutex_173_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_174_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_175_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_176_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_ref_172_ = crate::leanh::lean_ctor_get(v_mutex_169_, 0);
    crate::leanh::lean_inc(v_ref_172_);
    v_mutex_173_ = crate::leanh::lean_ctor_get(v_mutex_169_, 1);
    crate::leanh::lean_inc(v_mutex_173_);
    crate::leanh::lean_dec_ref(v_mutex_169_);
    v___x_174_ = lean_io_basemutex_lock(v_mutex_173_);
    v___x_175_ = crate::leanh::lean_apply_2(v_k_170_, v_ref_172_, crate::leanh::lean_box(0));
    v___x_176_ = lean_io_basemutex_unlock(v_mutex_173_);
    crate::leanh::lean_dec(v_mutex_173_);
    return v___x_175_;
}
pub unsafe fn l_Std_Mutex_atomically___at___00Std_Barrier_wait_spec__1___redArg___boxed(
    mut v_mutex_177_: *mut crate::leanh::LeanObject,
    mut v_k_178_: *mut crate::leanh::LeanObject,
    mut v___y_179_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_180_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_180_ =
        l_Std_Mutex_atomically___at___00Std_Barrier_wait_spec__1___redArg(v_mutex_177_, v_k_178_);
    return v_res_180_;
}
pub unsafe fn l_Std_Mutex_atomically___at___00Std_Barrier_wait_spec__1(
    mut v_00_u03b1_181_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_182_: *mut crate::leanh::LeanObject,
    mut v_mutex_183_: *mut crate::leanh::LeanObject,
    mut v_k_184_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_186_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_186_ =
        l_Std_Mutex_atomically___at___00Std_Barrier_wait_spec__1___redArg(v_mutex_183_, v_k_184_);
    return v___x_186_;
}
pub unsafe fn l_Std_Mutex_atomically___at___00Std_Barrier_wait_spec__1___boxed(
    mut v_00_u03b1_187_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_188_: *mut crate::leanh::LeanObject,
    mut v_mutex_189_: *mut crate::leanh::LeanObject,
    mut v_k_190_: *mut crate::leanh::LeanObject,
    mut v___y_191_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_192_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_192_ = l_Std_Mutex_atomically___at___00Std_Barrier_wait_spec__1(
        v_00_u03b1_187_,
        v_00_u03b2_188_,
        v_mutex_189_,
        v_k_190_,
    );
    return v_res_192_;
}
pub unsafe fn l_Std_Barrier_wait___lam__0(
    mut v_generationId_193_: *mut crate::leanh::LeanObject,
    mut v___x_194_: u8,
    mut v___y_195_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_197_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_generationId_198_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_199_: u8 = 0;
    v___x_197_ = lean_st_ref_get(v___y_195_);
    v_generationId_198_ = crate::leanh::lean_ctor_get(v___x_197_, 1);
    crate::leanh::lean_inc(v_generationId_198_);
    crate::leanh::lean_dec(v___x_197_);
    v___x_199_ = lean_nat_dec_eq(v_generationId_198_, v_generationId_193_);
    crate::leanh::lean_dec(v_generationId_198_);
    if v___x_199_ == 0 {
        return v___x_194_;
    } else {
        let mut v___x_200_: u8 = 0;
        v___x_200_ = 0;
        return v___x_200_;
    }
}
pub unsafe fn l_Std_Barrier_wait___lam__0___boxed(
    mut v_generationId_201_: *mut crate::leanh::LeanObject,
    mut v___x_202_: *mut crate::leanh::LeanObject,
    mut v___y_203_: *mut crate::leanh::LeanObject,
    mut v___y_204_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2442__boxed_205_: u8 = 0;
    let mut v_res_206_: u8 = 0;
    let mut v_r_207_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2442__boxed_205_ = (crate::leanh::lean_unbox(v___x_202_) as u8);
    v_res_206_ =
        l_Std_Barrier_wait___lam__0(v_generationId_201_, v___x_2442__boxed_205_, v___y_203_);
    crate::leanh::lean_dec(v___y_203_);
    crate::leanh::lean_dec(v_generationId_201_);
    v_r_207_ = crate::leanh::lean_box((v_res_206_) as usize);
    return v_r_207_;
}
pub unsafe fn l___private_Init_While_0__whileM_erased___at___00Std_Condvar_waitUntil___at___00Std_Barrier_wait_spec__0_spec__0___redArg(
    mut v_pred_208_: *mut crate::leanh::LeanObject,
    mut v_condvar_209_: *mut crate::leanh::LeanObject,
    mut v_mutex_210_: *mut crate::leanh::LeanObject,
    mut v___y_211_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_213_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_214_: u8 = 0;
    let mut v___x_215_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_217_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                crate::leanh::lean_inc_ref(v_pred_208_);
                crate::leanh::lean_inc(v___y_211_);
                v___x_213_ =
                    crate::leanh::lean_apply_2(v_pred_208_, v___y_211_, crate::leanh::lean_box(0));
                v___x_214_ = (crate::leanh::lean_unbox(v___x_213_) as u8);
                if v___x_214_ == 0 {
                    v___x_215_ = lean_io_condvar_wait(v_condvar_209_, v_mutex_210_);
                    state = 0;
                    continue;
                } else {
                    crate::leanh::lean_dec_ref(v_pred_208_);
                    v___x_217_ = crate::leanh::lean_box(0);
                    return v___x_217_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_While_0__whileM_erased___at___00Std_Condvar_waitUntil___at___00Std_Barrier_wait_spec__0_spec__0___redArg___boxed(
    mut v_pred_218_: *mut crate::leanh::LeanObject,
    mut v_condvar_219_: *mut crate::leanh::LeanObject,
    mut v_mutex_220_: *mut crate::leanh::LeanObject,
    mut v___y_221_: *mut crate::leanh::LeanObject,
    mut v___y_222_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_223_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_223_ = l___private_Init_While_0__whileM_erased___at___00Std_Condvar_waitUntil___at___00Std_Barrier_wait_spec__0_spec__0___redArg(v_pred_218_, v_condvar_219_, v_mutex_220_, v___y_221_);
    crate::leanh::lean_dec(v___y_221_);
    crate::leanh::lean_dec(v_mutex_220_);
    crate::leanh::lean_dec(v_condvar_219_);
    return v_res_223_;
}
pub unsafe fn l_Std_Condvar_waitUntil___at___00Std_Barrier_wait_spec__0(
    mut v_condvar_224_: *mut crate::leanh::LeanObject,
    mut v_mutex_225_: *mut crate::leanh::LeanObject,
    mut v_pred_226_: *mut crate::leanh::LeanObject,
    mut v___y_227_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_229_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_230_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_229_ = l___private_Init_While_0__whileM_erased___at___00Std_Condvar_waitUntil___at___00Std_Barrier_wait_spec__0_spec__0___redArg(v_pred_226_, v_condvar_224_, v_mutex_225_, v___y_227_);
    v___x_230_ = crate::leanh::lean_box(0);
    return v___x_230_;
}
pub unsafe fn l_Std_Condvar_waitUntil___at___00Std_Barrier_wait_spec__0___boxed(
    mut v_condvar_231_: *mut crate::leanh::LeanObject,
    mut v_mutex_232_: *mut crate::leanh::LeanObject,
    mut v_pred_233_: *mut crate::leanh::LeanObject,
    mut v___y_234_: *mut crate::leanh::LeanObject,
    mut v___y_235_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_236_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_236_ = l_Std_Condvar_waitUntil___at___00Std_Barrier_wait_spec__0(
        v_condvar_231_,
        v_mutex_232_,
        v_pred_233_,
        v___y_234_,
    );
    crate::leanh::lean_dec(v___y_234_);
    crate::leanh::lean_dec(v_mutex_232_);
    crate::leanh::lean_dec(v_condvar_231_);
    return v_res_236_;
}
pub unsafe fn l_Std_Barrier_wait___lam__1(
    mut v_numThreads_237_: *mut crate::leanh::LeanObject,
    mut v_cvar_238_: *mut crate::leanh::LeanObject,
    mut v_lock_239_: *mut crate::leanh::LeanObject,
    mut v___y_240_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_242_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_243_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_count_244_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_generationId_245_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_247_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_248_: u8 = 0;
    let mut v___x_249_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_250_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_252_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_253_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_254_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_count_255_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_256_: u8 = 0;
    let mut v___x_257_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_generationId_258_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_260_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_261_: u8 = 0;
    let mut v___x_262_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_263_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_265_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_266_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_267_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_268_: u8 = 0;
    let mut v_reuseFailAlloc_269_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_270_: u8 = 0;
    let mut v_unused_271_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_generationId_272_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_mutex_273_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_274_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_275_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_276_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_277_: u8 = 0;
    let mut v_reuseFailAlloc_278_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_279_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_242_ = lean_st_ref_get(v___y_240_);
                v___x_243_ = lean_st_ref_take(v___y_240_);
                v_count_244_ = crate::leanh::lean_ctor_get(v___x_243_, 0);
                v_generationId_245_ = crate::leanh::lean_ctor_get(v___x_243_, 1);
                v_isSharedCheck_279_ = (!crate::leanh::lean_is_exclusive(v___x_243_)) as u8;
                if v_isSharedCheck_279_ == 0 {
                    v___x_247_ = v___x_243_;
                    v_isShared_248_ = v_isSharedCheck_279_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_generationId_245_);
                    crate::leanh::lean_inc(v_count_244_);
                    crate::leanh::lean_dec(v___x_243_);
                    v___x_247_ = crate::leanh::lean_box(0);
                    v_isShared_248_ = v_isSharedCheck_279_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_249_ = crate::leanh::lean_unsigned_to_nat(1);
                v___x_250_ = lean_nat_add(v_count_244_, v___x_249_);
                crate::leanh::lean_dec(v_count_244_);
                if v_isShared_248_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_247_, 0, v___x_250_);
                    v___x_252_ = v___x_247_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_278_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_278_, 0, v___x_250_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_278_, 1, v_generationId_245_);
                    v___x_252_ = v_reuseFailAlloc_278_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_253_ = lean_st_ref_set(v___y_240_, v___x_252_);
                v___x_254_ = lean_st_ref_get(v___y_240_);
                v_count_255_ = crate::leanh::lean_ctor_get(v___x_254_, 0);
                crate::leanh::lean_inc(v_count_255_);
                crate::leanh::lean_dec(v___x_254_);
                v___x_256_ = lean_nat_dec_lt(v_count_255_, v_numThreads_237_);
                crate::leanh::lean_dec(v_count_255_);
                if v___x_256_ == 0 {
                    crate::leanh::lean_dec(v___x_242_);
                    v___x_257_ = lean_st_ref_take(v___y_240_);
                    v_generationId_258_ = crate::leanh::lean_ctor_get(v___x_257_, 1);
                    v_isSharedCheck_270_ = (!crate::leanh::lean_is_exclusive(v___x_257_)) as u8;
                    if v_isSharedCheck_270_ == 0 {
                        v_unused_271_ = crate::leanh::lean_ctor_get(v___x_257_, 0);
                        crate::leanh::lean_dec(v_unused_271_);
                        v___x_260_ = v___x_257_;
                        v_isShared_261_ = v_isSharedCheck_270_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_generationId_258_);
                        crate::leanh::lean_dec(v___x_257_);
                        v___x_260_ = crate::leanh::lean_box(0);
                        v_isShared_261_ = v_isSharedCheck_270_;
                        state = 3;
                        continue;
                    }
                } else {
                    v_generationId_272_ = crate::leanh::lean_ctor_get(v___x_242_, 1);
                    crate::leanh::lean_inc(v_generationId_272_);
                    crate::leanh::lean_dec(v___x_242_);
                    v_mutex_273_ = crate::leanh::lean_ctor_get(v_lock_239_, 1);
                    v___x_274_ = crate::leanh::lean_box((v___x_256_) as usize);
                    v___f_275_ = crate::leanh::lean_alloc_closure(
                        l_Std_Barrier_wait___lam__0___boxed as *mut core::ffi::c_void,
                        4,
                        2,
                    );
                    crate::leanh::lean_closure_set(v___f_275_, 0, v_generationId_272_);
                    crate::leanh::lean_closure_set(v___f_275_, 1, v___x_274_);
                    v___x_276_ = l_Std_Condvar_waitUntil___at___00Std_Barrier_wait_spec__0(
                        v_cvar_238_,
                        v_mutex_273_,
                        v___f_275_,
                        v___y_240_,
                    );
                    v___x_277_ = 0;
                    return v___x_277_;
                }
            }
            3 => {
                v___x_262_ = crate::leanh::lean_unsigned_to_nat(0);
                v___x_263_ = lean_nat_add(v_generationId_258_, v___x_249_);
                crate::leanh::lean_dec(v_generationId_258_);
                if v_isShared_261_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_260_, 1, v___x_263_);
                    crate::leanh::lean_ctor_set(v___x_260_, 0, v___x_262_);
                    v___x_265_ = v___x_260_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_269_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_269_, 0, v___x_262_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_269_, 1, v___x_263_);
                    v___x_265_ = v_reuseFailAlloc_269_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_266_ = lean_st_ref_set(v___y_240_, v___x_265_);
                v___x_267_ = lean_io_condvar_notify_all(v_cvar_238_);
                v___x_268_ = 1;
                return v___x_268_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Barrier_wait___lam__1___boxed(
    mut v_numThreads_280_: *mut crate::leanh::LeanObject,
    mut v_cvar_281_: *mut crate::leanh::LeanObject,
    mut v_lock_282_: *mut crate::leanh::LeanObject,
    mut v___y_283_: *mut crate::leanh::LeanObject,
    mut v___y_284_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_285_: u8 = 0;
    let mut v_r_286_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_285_ =
        l_Std_Barrier_wait___lam__1(v_numThreads_280_, v_cvar_281_, v_lock_282_, v___y_283_);
    crate::leanh::lean_dec(v___y_283_);
    crate::leanh::lean_dec_ref(v_lock_282_);
    crate::leanh::lean_dec(v_cvar_281_);
    crate::leanh::lean_dec(v_numThreads_280_);
    v_r_286_ = crate::leanh::lean_box((v_res_285_) as usize);
    return v_r_286_;
}
pub unsafe fn l_Std_Barrier_wait(mut v_barrier_287_: *mut crate::leanh::LeanObject) -> u8 {
    let mut v_lock_289_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_cvar_290_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_numThreads_291_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_292_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_293_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_294_: u8 = 0;
    v_lock_289_ = crate::leanh::lean_ctor_get(v_barrier_287_, 0);
    crate::leanh::lean_inc_ref_n(v_lock_289_, 2);
    v_cvar_290_ = crate::leanh::lean_ctor_get(v_barrier_287_, 1);
    crate::leanh::lean_inc(v_cvar_290_);
    v_numThreads_291_ = crate::leanh::lean_ctor_get(v_barrier_287_, 2);
    crate::leanh::lean_inc(v_numThreads_291_);
    crate::leanh::lean_dec_ref(v_barrier_287_);
    v___f_292_ = crate::leanh::lean_alloc_closure(
        l_Std_Barrier_wait___lam__1___boxed as *mut core::ffi::c_void,
        5,
        3,
    );
    crate::leanh::lean_closure_set(v___f_292_, 0, v_numThreads_291_);
    crate::leanh::lean_closure_set(v___f_292_, 1, v_cvar_290_);
    crate::leanh::lean_closure_set(v___f_292_, 2, v_lock_289_);
    v___x_293_ =
        l_Std_Mutex_atomically___at___00Std_Barrier_wait_spec__1___redArg(v_lock_289_, v___f_292_);
    v___x_294_ = (crate::leanh::lean_unbox(v___x_293_) as u8);
    crate::leanh::lean_dec(v___x_293_);
    return v___x_294_;
}
pub unsafe fn l_Std_Barrier_wait___boxed(
    mut v_barrier_295_: *mut crate::leanh::LeanObject,
    mut v_a_296_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_297_: u8 = 0;
    let mut v_r_298_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_297_ = l_Std_Barrier_wait(v_barrier_295_);
    v_r_298_ = crate::leanh::lean_box((v_res_297_) as usize);
    return v_r_298_;
}
pub unsafe fn l___private_Init_While_0__whileM_erased___at___00Std_Condvar_waitUntil___at___00Std_Barrier_wait_spec__0_spec__0(
    mut v_pred_299_: *mut crate::leanh::LeanObject,
    mut v_condvar_300_: *mut crate::leanh::LeanObject,
    mut v_mutex_301_: *mut crate::leanh::LeanObject,
    mut v_inst_302_: *mut crate::leanh::LeanObject,
    mut v_a_303_: *mut crate::leanh::LeanObject,
    mut v___y_304_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_306_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_306_ = l___private_Init_While_0__whileM_erased___at___00Std_Condvar_waitUntil___at___00Std_Barrier_wait_spec__0_spec__0___redArg(v_pred_299_, v_condvar_300_, v_mutex_301_, v___y_304_);
    return v___x_306_;
}
pub unsafe fn l___private_Init_While_0__whileM_erased___at___00Std_Condvar_waitUntil___at___00Std_Barrier_wait_spec__0_spec__0___boxed(
    mut v_pred_307_: *mut crate::leanh::LeanObject,
    mut v_condvar_308_: *mut crate::leanh::LeanObject,
    mut v_mutex_309_: *mut crate::leanh::LeanObject,
    mut v_inst_310_: *mut crate::leanh::LeanObject,
    mut v_a_311_: *mut crate::leanh::LeanObject,
    mut v___y_312_: *mut crate::leanh::LeanObject,
    mut v___y_313_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_314_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_314_ = l___private_Init_While_0__whileM_erased___at___00Std_Condvar_waitUntil___at___00Std_Barrier_wait_spec__0_spec__0(v_pred_307_, v_condvar_308_, v_mutex_309_, v_inst_310_, v_a_311_, v___y_312_);
    crate::leanh::lean_dec(v___y_312_);
    crate::leanh::lean_dec(v_mutex_309_);
    crate::leanh::lean_dec(v_condvar_308_);
    return v_res_314_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Std_Sync_Barrier(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Std_Sync_Mutex(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Std_Sync_Barrier(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_meta_initialized = true;
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Std_Sync_Barrier(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Std_Sync_Mutex(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Std_Sync_Barrier(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Std_Sync_Barrier(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Std_Sync_Barrier(builtin);
}
