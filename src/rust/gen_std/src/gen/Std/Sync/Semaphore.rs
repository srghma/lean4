// Lean compiler output
// Module: Std.Sync.Semaphore
// Imports: Init.Data.Queue Init.System.Promise Std.Sync.Mutex
use crate::ffi::{
    lean_io_basemutex_lock, lean_io_basemutex_unlock, lean_io_promise_new, lean_io_promise_resolve,
    lean_nat_add, lean_nat_dec_lt, lean_nat_sub, lean_st_ref_get, lean_st_ref_set,
};
use crate::r#gen::Init::Data::Queue::{
    initialize_Init_Data_Queue, l_Std_Queue_dequeue_x3f___redArg, l_Std_Queue_empty,
    l_Std_Queue_enqueue___redArg, runtime_initialize_Init_Data_Queue,
};
use crate::r#gen::Init::System::Promise::{
    initialize_Init_System_Promise, runtime_initialize_Init_System_Promise,
};
use crate::r#gen::Std::Sync::Mutex::{
    initialize_Std_Sync_Mutex, l_Std_Mutex_new___redArg, runtime_initialize_Std_Sync_Mutex,
};
static mut l_Std_Semaphore_new___closed__0_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Semaphore_new___closed__0: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Std_Semaphore_acquire___closed__0_value: crate::leanh::LeanClosureObject<0> =
    crate::leanh::LeanClosureObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0)
                as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Std_Semaphore_acquire___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Std_Semaphore_acquire___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Semaphore_acquire___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_Std_Semaphore_tryAcquire___closed__0_value: crate::leanh::LeanClosureObject<0> =
    crate::leanh::LeanClosureObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0)
                as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Std_Semaphore_tryAcquire___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Std_Semaphore_tryAcquire___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Semaphore_tryAcquire___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Semaphore_release___closed__0_value: crate::leanh::LeanClosureObject<0> =
    crate::leanh::LeanClosureObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0)
                as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Std_Semaphore_release___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Std_Semaphore_release___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Semaphore_release___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_Std_Semaphore_availablePermits___closed__0_value: crate::leanh::LeanClosureObject<0> =
    crate::leanh::LeanClosureObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0)
                as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Std_Semaphore_availablePermits___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Std_Semaphore_availablePermits___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Semaphore_availablePermits___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub unsafe fn l___private_Std_Sync_Semaphore_0__Std_mkResolvedPromise___redArg(
    mut v_a_179_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_181_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_182_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_181_ = lean_io_promise_new();
    v___x_182_ = lean_io_promise_resolve(v_a_179_, v___x_181_);
    return v___x_181_;
}
pub unsafe fn l___private_Std_Sync_Semaphore_0__Std_mkResolvedPromise___redArg___boxed(
    mut v_a_183_: *mut crate::leanh::LeanObject,
    mut v_a_184_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_185_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_185_ = l___private_Std_Sync_Semaphore_0__Std_mkResolvedPromise___redArg(v_a_183_);
    return v_res_185_;
}
pub unsafe fn l___private_Std_Sync_Semaphore_0__Std_mkResolvedPromise(
    mut v_00_u03b1_186_: *mut crate::leanh::LeanObject,
    mut v_inst_187_: *mut crate::leanh::LeanObject,
    mut v_a_188_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_190_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_190_ = l___private_Std_Sync_Semaphore_0__Std_mkResolvedPromise___redArg(v_a_188_);
    return v___x_190_;
}
pub unsafe fn l___private_Std_Sync_Semaphore_0__Std_mkResolvedPromise___boxed(
    mut v_00_u03b1_191_: *mut crate::leanh::LeanObject,
    mut v_inst_192_: *mut crate::leanh::LeanObject,
    mut v_a_193_: *mut crate::leanh::LeanObject,
    mut v_a_194_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_195_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_195_ = l___private_Std_Sync_Semaphore_0__Std_mkResolvedPromise(
        v_00_u03b1_191_,
        v_inst_192_,
        v_a_193_,
    );
    return v_res_195_;
}
pub unsafe fn _init_l_Std_Semaphore_new___closed__0() -> *mut crate::leanh::LeanObject {
    let mut v___x_196_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_196_ = l_Std_Queue_empty(crate::leanh::lean_box(0));
    return v___x_196_;
}
pub unsafe fn l_Std_Semaphore_new(
    mut v_permits_197_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_199_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_200_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_201_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_199_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Semaphore_new___closed__0),
        core::ptr::addr_of_mut!(l_Std_Semaphore_new___closed__0_once),
        _init_l_Std_Semaphore_new___closed__0,
    );
    v___x_200_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_200_, 0, v_permits_197_);
    crate::leanh::lean_ctor_set(v___x_200_, 1, v___x_199_);
    v___x_201_ = l_Std_Mutex_new___redArg(v___x_200_);
    return v___x_201_;
}
pub unsafe fn l_Std_Semaphore_new___boxed(
    mut v_permits_202_: *mut crate::leanh::LeanObject,
    mut v_a_203_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_204_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_204_ = l_Std_Semaphore_new(v_permits_202_);
    return v_res_204_;
}
pub unsafe fn l_Std_Mutex_atomically___at___00Std_Semaphore_acquire_spec__0___redArg(
    mut v_mutex_205_: *mut crate::leanh::LeanObject,
    mut v_k_206_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_ref_208_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_mutex_209_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_210_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_211_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_212_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_ref_208_ = crate::leanh::lean_ctor_get(v_mutex_205_, 0);
    crate::leanh::lean_inc(v_ref_208_);
    v_mutex_209_ = crate::leanh::lean_ctor_get(v_mutex_205_, 1);
    crate::leanh::lean_inc(v_mutex_209_);
    crate::leanh::lean_dec_ref(v_mutex_205_);
    v___x_210_ = lean_io_basemutex_lock(v_mutex_209_);
    v___x_211_ = crate::leanh::lean_apply_2(v_k_206_, v_ref_208_, crate::leanh::lean_box(0));
    v___x_212_ = lean_io_basemutex_unlock(v_mutex_209_);
    crate::leanh::lean_dec(v_mutex_209_);
    return v___x_211_;
}
pub unsafe fn l_Std_Mutex_atomically___at___00Std_Semaphore_acquire_spec__0___redArg___boxed(
    mut v_mutex_213_: *mut crate::leanh::LeanObject,
    mut v_k_214_: *mut crate::leanh::LeanObject,
    mut v___y_215_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_216_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_216_ = l_Std_Mutex_atomically___at___00Std_Semaphore_acquire_spec__0___redArg(
        v_mutex_213_,
        v_k_214_,
    );
    return v_res_216_;
}
pub unsafe fn l_Std_Mutex_atomically___at___00Std_Semaphore_acquire_spec__0(
    mut v_00_u03b1_217_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_218_: *mut crate::leanh::LeanObject,
    mut v_mutex_219_: *mut crate::leanh::LeanObject,
    mut v_k_220_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_222_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_222_ = l_Std_Mutex_atomically___at___00Std_Semaphore_acquire_spec__0___redArg(
        v_mutex_219_,
        v_k_220_,
    );
    return v___x_222_;
}
pub unsafe fn l_Std_Mutex_atomically___at___00Std_Semaphore_acquire_spec__0___boxed(
    mut v_00_u03b1_223_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_224_: *mut crate::leanh::LeanObject,
    mut v_mutex_225_: *mut crate::leanh::LeanObject,
    mut v_k_226_: *mut crate::leanh::LeanObject,
    mut v___y_227_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_228_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_228_ = l_Std_Mutex_atomically___at___00Std_Semaphore_acquire_spec__0(
        v_00_u03b1_223_,
        v_00_u03b2_224_,
        v_mutex_225_,
        v_k_226_,
    );
    return v_res_228_;
}
pub unsafe fn l_Std_Semaphore_acquire___lam__0(
    mut v___y_229_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_231_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_permits_232_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_waiters_233_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_235_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_236_: u8 = 0;
    let mut v___x_237_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_238_: u8 = 0;
    let mut v___x_239_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_240_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_242_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_243_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_244_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_245_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_246_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_248_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_249_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_250_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_251_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_252_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_253_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_231_ = lean_st_ref_get(v___y_229_);
                v_permits_232_ = crate::leanh::lean_ctor_get(v___x_231_, 0);
                v_waiters_233_ = crate::leanh::lean_ctor_get(v___x_231_, 1);
                v_isSharedCheck_253_ = (!crate::leanh::lean_is_exclusive(v___x_231_)) as u8;
                if v_isSharedCheck_253_ == 0 {
                    v___x_235_ = v___x_231_;
                    v_isShared_236_ = v_isSharedCheck_253_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_waiters_233_);
                    crate::leanh::lean_inc(v_permits_232_);
                    crate::leanh::lean_dec(v___x_231_);
                    v___x_235_ = crate::leanh::lean_box(0);
                    v_isShared_236_ = v_isSharedCheck_253_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_237_ = crate::leanh::lean_unsigned_to_nat(0);
                v___x_238_ = lean_nat_dec_lt(v___x_237_, v_permits_232_);
                if v___x_238_ == 0 {
                    v___x_239_ = lean_io_promise_new();
                    crate::leanh::lean_inc(v___x_239_);
                    v___x_240_ = l_Std_Queue_enqueue___redArg(v___x_239_, v_waiters_233_);
                    if v_isShared_236_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_235_, 1, v___x_240_);
                        v___x_242_ = v___x_235_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_244_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_244_, 0, v_permits_232_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_244_, 1, v___x_240_);
                        v___x_242_ = v_reuseFailAlloc_244_;
                        state = 2;
                        continue;
                    }
                } else {
                    v___x_245_ = crate::leanh::lean_unsigned_to_nat(1);
                    v___x_246_ = lean_nat_sub(v_permits_232_, v___x_245_);
                    crate::leanh::lean_dec(v_permits_232_);
                    if v_isShared_236_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_235_, 0, v___x_246_);
                        v___x_248_ = v___x_235_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_252_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_252_, 0, v___x_246_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_252_, 1, v_waiters_233_);
                        v___x_248_ = v_reuseFailAlloc_252_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                v___x_243_ = lean_st_ref_set(v___y_229_, v___x_242_);
                return v___x_239_;
            }
            3 => {
                v___x_249_ = lean_st_ref_set(v___y_229_, v___x_248_);
                v___x_250_ = crate::leanh::lean_box(0);
                v___x_251_ =
                    l___private_Std_Sync_Semaphore_0__Std_mkResolvedPromise___redArg(v___x_250_);
                return v___x_251_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Semaphore_acquire___lam__0___boxed(
    mut v___y_254_: *mut crate::leanh::LeanObject,
    mut v___y_255_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_256_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_256_ = l_Std_Semaphore_acquire___lam__0(v___y_254_);
    crate::leanh::lean_dec(v___y_254_);
    return v_res_256_;
}
pub unsafe fn l_Std_Semaphore_acquire(
    mut v_sem_258_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_260_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_261_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_260_ = l_Std_Semaphore_acquire___closed__0;
    v___x_261_ = l_Std_Mutex_atomically___at___00Std_Semaphore_acquire_spec__0___redArg(
        v_sem_258_, v___f_260_,
    );
    return v___x_261_;
}
pub unsafe fn l_Std_Semaphore_acquire___boxed(
    mut v_sem_262_: *mut crate::leanh::LeanObject,
    mut v_a_263_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_264_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_264_ = l_Std_Semaphore_acquire(v_sem_262_);
    return v_res_264_;
}
pub unsafe fn l_Std_Semaphore_tryAcquire___lam__0(
    mut v___y_265_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_267_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_permits_268_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_waiters_269_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_271_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_272_: u8 = 0;
    let mut v___x_273_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_274_: u8 = 0;
    let mut v___x_275_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_276_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_278_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_279_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_280_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_281_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_267_ = lean_st_ref_get(v___y_265_);
                v_permits_268_ = crate::leanh::lean_ctor_get(v___x_267_, 0);
                v_waiters_269_ = crate::leanh::lean_ctor_get(v___x_267_, 1);
                v_isSharedCheck_281_ = (!crate::leanh::lean_is_exclusive(v___x_267_)) as u8;
                if v_isSharedCheck_281_ == 0 {
                    v___x_271_ = v___x_267_;
                    v_isShared_272_ = v_isSharedCheck_281_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_waiters_269_);
                    crate::leanh::lean_inc(v_permits_268_);
                    crate::leanh::lean_dec(v___x_267_);
                    v___x_271_ = crate::leanh::lean_box(0);
                    v_isShared_272_ = v_isSharedCheck_281_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_273_ = crate::leanh::lean_unsigned_to_nat(0);
                v___x_274_ = lean_nat_dec_lt(v___x_273_, v_permits_268_);
                if v___x_274_ == 0 {
                    crate::leanh::lean_del_object(v___x_271_);
                    crate::leanh::lean_dec_ref(v_waiters_269_);
                    crate::leanh::lean_dec(v_permits_268_);
                    return v___x_274_;
                } else {
                    v___x_275_ = crate::leanh::lean_unsigned_to_nat(1);
                    v___x_276_ = lean_nat_sub(v_permits_268_, v___x_275_);
                    crate::leanh::lean_dec(v_permits_268_);
                    if v_isShared_272_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_271_, 0, v___x_276_);
                        v___x_278_ = v___x_271_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_280_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_280_, 0, v___x_276_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_280_, 1, v_waiters_269_);
                        v___x_278_ = v_reuseFailAlloc_280_;
                        state = 2;
                        continue;
                    }
                }
            }
            2 => {
                v___x_279_ = lean_st_ref_set(v___y_265_, v___x_278_);
                return v___x_274_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Semaphore_tryAcquire___lam__0___boxed(
    mut v___y_282_: *mut crate::leanh::LeanObject,
    mut v___y_283_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_284_: u8 = 0;
    let mut v_r_285_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_284_ = l_Std_Semaphore_tryAcquire___lam__0(v___y_282_);
    crate::leanh::lean_dec(v___y_282_);
    v_r_285_ = crate::leanh::lean_box((v_res_284_) as usize);
    return v_r_285_;
}
pub unsafe fn l_Std_Semaphore_tryAcquire(mut v_sem_287_: *mut crate::leanh::LeanObject) -> u8 {
    let mut v___f_289_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_290_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_291_: u8 = 0;
    v___f_289_ = l_Std_Semaphore_tryAcquire___closed__0;
    v___x_290_ = l_Std_Mutex_atomically___at___00Std_Semaphore_acquire_spec__0___redArg(
        v_sem_287_, v___f_289_,
    );
    v___x_291_ = (crate::leanh::lean_unbox(v___x_290_) as u8);
    crate::leanh::lean_dec(v___x_290_);
    return v___x_291_;
}
pub unsafe fn l_Std_Semaphore_tryAcquire___boxed(
    mut v_sem_292_: *mut crate::leanh::LeanObject,
    mut v_a_293_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_294_: u8 = 0;
    let mut v_r_295_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_294_ = l_Std_Semaphore_tryAcquire(v_sem_292_);
    v_r_295_ = crate::leanh::lean_box((v_res_294_) as usize);
    return v_r_295_;
}
pub unsafe fn l_Std_Semaphore_release___lam__0(
    mut v___y_296_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_298_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_permits_299_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_waiters_300_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_302_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_303_: u8 = 0;
    let mut v___x_304_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_305_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_306_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_308_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_309_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_310_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_311_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_312_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_314_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_315_: u8 = 0;
    let mut v_fst_316_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_317_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_319_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_320_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_322_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_323_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_324_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_325_: u8 = 0;
    let mut v_isSharedCheck_326_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_298_ = lean_st_ref_get(v___y_296_);
                v_permits_299_ = crate::leanh::lean_ctor_get(v___x_298_, 0);
                v_waiters_300_ = crate::leanh::lean_ctor_get(v___x_298_, 1);
                v_isSharedCheck_326_ = (!crate::leanh::lean_is_exclusive(v___x_298_)) as u8;
                if v_isSharedCheck_326_ == 0 {
                    v___x_302_ = v___x_298_;
                    v_isShared_303_ = v_isSharedCheck_326_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_waiters_300_);
                    crate::leanh::lean_inc(v_permits_299_);
                    crate::leanh::lean_dec(v___x_298_);
                    v___x_302_ = crate::leanh::lean_box(0);
                    v_isShared_303_ = v_isSharedCheck_326_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                crate::leanh::lean_inc_ref(v_waiters_300_);
                v___x_304_ = l_Std_Queue_dequeue_x3f___redArg(v_waiters_300_);
                if crate::leanh::lean_obj_tag(v___x_304_) == 0 {
                    v___x_305_ = crate::leanh::lean_unsigned_to_nat(1);
                    v___x_306_ = lean_nat_add(v_permits_299_, v___x_305_);
                    crate::leanh::lean_dec(v_permits_299_);
                    if v_isShared_303_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_302_, 0, v___x_306_);
                        v___x_308_ = v___x_302_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_311_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_311_, 0, v___x_306_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_311_, 1, v_waiters_300_);
                        v___x_308_ = v_reuseFailAlloc_311_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_waiters_300_);
                    v_val_312_ = crate::leanh::lean_ctor_get(v___x_304_, 0);
                    v_isSharedCheck_325_ = (!crate::leanh::lean_is_exclusive(v___x_304_)) as u8;
                    if v_isSharedCheck_325_ == 0 {
                        v___x_314_ = v___x_304_;
                        v_isShared_315_ = v_isSharedCheck_325_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_val_312_);
                        crate::leanh::lean_dec(v___x_304_);
                        v___x_314_ = crate::leanh::lean_box(0);
                        v_isShared_315_ = v_isSharedCheck_325_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                v___x_309_ = lean_st_ref_set(v___y_296_, v___x_308_);
                v___x_310_ = crate::leanh::lean_box(0);
                return v___x_310_;
            }
            3 => {
                v_fst_316_ = crate::leanh::lean_ctor_get(v_val_312_, 0);
                crate::leanh::lean_inc(v_fst_316_);
                v_snd_317_ = crate::leanh::lean_ctor_get(v_val_312_, 1);
                crate::leanh::lean_inc(v_snd_317_);
                crate::leanh::lean_dec(v_val_312_);
                if v_isShared_303_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_302_, 1, v_snd_317_);
                    v___x_319_ = v___x_302_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_324_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_324_, 0, v_permits_299_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_324_, 1, v_snd_317_);
                    v___x_319_ = v_reuseFailAlloc_324_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_320_ = lean_st_ref_set(v___y_296_, v___x_319_);
                if v_isShared_315_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_314_, 0, v_fst_316_);
                    v___x_322_ = v___x_314_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_323_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_323_, 0, v_fst_316_);
                    v___x_322_ = v_reuseFailAlloc_323_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_322_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Semaphore_release___lam__0___boxed(
    mut v___y_327_: *mut crate::leanh::LeanObject,
    mut v___y_328_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_329_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_329_ = l_Std_Semaphore_release___lam__0(v___y_327_);
    crate::leanh::lean_dec(v___y_327_);
    return v_res_329_;
}
pub unsafe fn l_Std_Semaphore_release(
    mut v_sem_331_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_333_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_334_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_333_ = l_Std_Semaphore_release___closed__0;
    v___x_334_ = l_Std_Mutex_atomically___at___00Std_Semaphore_acquire_spec__0___redArg(
        v_sem_331_, v___f_333_,
    );
    if crate::leanh::lean_obj_tag(v___x_334_) == 1 {
        let mut v_val_335_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_336_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_337_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_val_335_ = crate::leanh::lean_ctor_get(v___x_334_, 0);
        crate::leanh::lean_inc(v_val_335_);
        crate::leanh::lean_dec_ref_known(v___x_334_, 1);
        v___x_336_ = crate::leanh::lean_box(0);
        v___x_337_ = lean_io_promise_resolve(v___x_336_, v_val_335_);
        crate::leanh::lean_dec(v_val_335_);
        return v___x_337_;
    } else {
        let mut v___x_338_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v___x_334_);
        v___x_338_ = crate::leanh::lean_box(0);
        return v___x_338_;
    }
}
pub unsafe fn l_Std_Semaphore_release___boxed(
    mut v_sem_339_: *mut crate::leanh::LeanObject,
    mut v_a_340_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_341_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_341_ = l_Std_Semaphore_release(v_sem_339_);
    return v_res_341_;
}
pub unsafe fn l_Std_Semaphore_availablePermits___lam__0(
    mut v___y_342_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_344_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_permits_345_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_344_ = lean_st_ref_get(v___y_342_);
    v_permits_345_ = crate::leanh::lean_ctor_get(v___x_344_, 0);
    crate::leanh::lean_inc(v_permits_345_);
    crate::leanh::lean_dec(v___x_344_);
    return v_permits_345_;
}
pub unsafe fn l_Std_Semaphore_availablePermits___lam__0___boxed(
    mut v___y_346_: *mut crate::leanh::LeanObject,
    mut v___y_347_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_348_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_348_ = l_Std_Semaphore_availablePermits___lam__0(v___y_346_);
    crate::leanh::lean_dec(v___y_346_);
    return v_res_348_;
}
pub unsafe fn l_Std_Semaphore_availablePermits(
    mut v_sem_350_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_352_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_353_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_352_ = l_Std_Semaphore_availablePermits___closed__0;
    v___x_353_ = l_Std_Mutex_atomically___at___00Std_Semaphore_acquire_spec__0___redArg(
        v_sem_350_, v___f_352_,
    );
    return v___x_353_;
}
pub unsafe fn l_Std_Semaphore_availablePermits___boxed(
    mut v_sem_354_: *mut crate::leanh::LeanObject,
    mut v_a_355_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_356_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_356_ = l_Std_Semaphore_availablePermits(v_sem_354_);
    return v_res_356_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Std_Sync_Semaphore(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Init_Data_Queue(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_System_Promise(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Std_Sync_Mutex(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Std_Sync_Semaphore(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_meta_initialized = true;
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Std_Sync_Semaphore(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Init_Data_Queue(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_System_Promise(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Std_Sync_Mutex(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Std_Sync_Semaphore(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Std_Sync_Semaphore(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Std_Sync_Semaphore(builtin);
}
