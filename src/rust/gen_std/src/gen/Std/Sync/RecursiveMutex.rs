// Lean compiler output
// Module: Std.Sync.RecursiveMutex
// Imports: Std.Sync.Basic
use crate::ffi::{
    lean_io_baserecmutex_lock, lean_io_baserecmutex_new, lean_io_baserecmutex_try_lock,
    lean_io_baserecmutex_unlock, lean_st_mk_ref,
};
use crate::r#gen::Std::Sync::Basic::{
    initialize_Std_Sync_Basic, runtime_initialize_Std_Sync_Basic,
};
pub static mut l___private_Std_Sync_RecursiveMutex_0__Std_RecursiveMutexImpl:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Std_instCoeOutRecursiveMutexBaseRecursiveMutex___closed__0_value:
    crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Std_instCoeOutRecursiveMutexBaseRecursiveMutex___lam__0___boxed
        as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_instCoeOutRecursiveMutexBaseRecursiveMutex___closed__0:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_instCoeOutRecursiveMutexBaseRecursiveMutex___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_RecursiveMutex_atomically___redArg___closed__0_value:
    crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Std_RecursiveMutex_atomically___redArg___lam__1___boxed as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_RecursiveMutex_atomically___redArg___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_RecursiveMutex_atomically___redArg___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_RecursiveMutex_tryAtomically___redArg___closed__0_value:
    crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Std_RecursiveMutex_tryAtomically___redArg___lam__0___boxed as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_RecursiveMutex_tryAtomically___redArg___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_RecursiveMutex_tryAtomically___redArg___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_RecursiveMutex_tryAtomically___redArg___closed__1_value:
    crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Std_RecursiveMutex_tryAtomically___redArg___lam__1 as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_RecursiveMutex_tryAtomically___redArg___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_RecursiveMutex_tryAtomically___redArg___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub unsafe fn _init_l___private_Std_Sync_RecursiveMutex_0__Std_RecursiveMutexImpl()
-> *mut crate::leanh::LeanObject {
    let mut v___x_157_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_157_ = crate::leanh::lean_box(0);
    return v___x_157_;
}
pub unsafe fn l_Std_BaseRecursiveMutex_new___boxed(
    mut v_a_00___x40___internal___hyg_159_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_160_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_160_ = lean_io_baserecmutex_new();
    return v_res_160_;
}
pub unsafe fn l_Std_BaseRecursiveMutex_lock___boxed(
    mut v_mutex_163_: *mut crate::leanh::LeanObject,
    mut v_a_00___x40___internal___hyg_164_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_165_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_165_ = lean_io_baserecmutex_lock(v_mutex_163_);
    crate::leanh::lean_dec(v_mutex_163_);
    return v_res_165_;
}
pub unsafe fn l_Std_BaseRecursiveMutex_tryLock___boxed(
    mut v_mutex_168_: *mut crate::leanh::LeanObject,
    mut v_a_00___x40___internal___hyg_169_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_170_: u8 = 0;
    let mut v_r_171_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_170_ = lean_io_baserecmutex_try_lock(v_mutex_168_);
    crate::leanh::lean_dec(v_mutex_168_);
    v_r_171_ = crate::leanh::lean_box((v_res_170_) as usize);
    return v_r_171_;
}
pub unsafe fn l_Std_BaseRecursiveMutex_unlock___boxed(
    mut v_mutex_174_: *mut crate::leanh::LeanObject,
    mut v_a_00___x40___internal___hyg_175_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_176_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_176_ = lean_io_baserecmutex_unlock(v_mutex_174_);
    crate::leanh::lean_dec(v_mutex_174_);
    return v_res_176_;
}
pub unsafe fn l_Std_instCoeOutRecursiveMutexBaseRecursiveMutex___lam__0(
    mut v_self_177_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_mutex_178_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_mutex_178_ = crate::leanh::lean_ctor_get(v_self_177_, 1);
    crate::leanh::lean_inc(v_mutex_178_);
    return v_mutex_178_;
}
pub unsafe fn l_Std_instCoeOutRecursiveMutexBaseRecursiveMutex___lam__0___boxed(
    mut v_self_179_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_180_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_180_ = l_Std_instCoeOutRecursiveMutexBaseRecursiveMutex___lam__0(v_self_179_);
    crate::leanh::lean_dec_ref(v_self_179_);
    return v_res_180_;
}
pub unsafe fn l_Std_instCoeOutRecursiveMutexBaseRecursiveMutex(
    mut v_00_u03b1_182_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_183_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_183_ = l_Std_instCoeOutRecursiveMutexBaseRecursiveMutex___closed__0;
    return v___f_183_;
}
pub unsafe fn l_Std_RecursiveMutex_new___redArg(
    mut v_a_184_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_186_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_187_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_188_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_186_ = lean_st_mk_ref(v_a_184_);
    v___x_187_ = lean_io_baserecmutex_new();
    v___x_188_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_188_, 0, v___x_186_);
    crate::leanh::lean_ctor_set(v___x_188_, 1, v___x_187_);
    return v___x_188_;
}
pub unsafe fn l_Std_RecursiveMutex_new___redArg___boxed(
    mut v_a_189_: *mut crate::leanh::LeanObject,
    mut v_a_190_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_191_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_191_ = l_Std_RecursiveMutex_new___redArg(v_a_189_);
    return v_res_191_;
}
pub unsafe fn l_Std_RecursiveMutex_new(
    mut v_00_u03b1_192_: *mut crate::leanh::LeanObject,
    mut v_a_193_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_195_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_195_ = l_Std_RecursiveMutex_new___redArg(v_a_193_);
    return v___x_195_;
}
pub unsafe fn l_Std_RecursiveMutex_new___boxed(
    mut v_00_u03b1_196_: *mut crate::leanh::LeanObject,
    mut v_a_197_: *mut crate::leanh::LeanObject,
    mut v_a_198_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_199_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_199_ = l_Std_RecursiveMutex_new(v_00_u03b1_196_, v_a_197_);
    return v_res_199_;
}
pub unsafe fn l_Std_RecursiveMutex_atomically___redArg___lam__0(
    mut v_k_200_: *mut crate::leanh::LeanObject,
    mut v_ref_201_: *mut crate::leanh::LeanObject,
    mut v_____r_202_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_203_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_203_ = crate::leanh::lean_apply_1(v_k_200_, v_ref_201_);
    return v___x_203_;
}
pub unsafe fn l_Std_RecursiveMutex_atomically___redArg___lam__1(
    mut v_x_204_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_fst_205_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_fst_205_ = crate::leanh::lean_ctor_get(v_x_204_, 0);
    crate::leanh::lean_inc(v_fst_205_);
    return v_fst_205_;
}
pub unsafe fn l_Std_RecursiveMutex_atomically___redArg___lam__1___boxed(
    mut v_x_206_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_207_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_207_ = l_Std_RecursiveMutex_atomically___redArg___lam__1(v_x_206_);
    crate::leanh::lean_dec_ref(v_x_206_);
    return v_res_207_;
}
pub unsafe fn l_Std_RecursiveMutex_atomically___redArg___lam__2(
    mut v___x_208_: *mut crate::leanh::LeanObject,
    mut v_x_209_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v___x_208_);
    return v___x_208_;
}
pub unsafe fn l_Std_RecursiveMutex_atomically___redArg___lam__2___boxed(
    mut v___x_210_: *mut crate::leanh::LeanObject,
    mut v_x_211_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_212_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_212_ = l_Std_RecursiveMutex_atomically___redArg___lam__2(v___x_210_, v_x_211_);
    crate::leanh::lean_dec(v_x_211_);
    crate::leanh::lean_dec(v___x_210_);
    return v_res_212_;
}
pub unsafe fn l_Std_RecursiveMutex_atomically___redArg(
    mut v_inst_214_: *mut crate::leanh::LeanObject,
    mut v_inst_215_: *mut crate::leanh::LeanObject,
    mut v_inst_216_: *mut crate::leanh::LeanObject,
    mut v_mutex_217_: *mut crate::leanh::LeanObject,
    mut v_k_218_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toApplicative_219_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toFunctor_220_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_221_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_222_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_mutex_223_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_map_224_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_225_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_226_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_227_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_228_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_229_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_230_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_231_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_232_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_y_233_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_234_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_219_ = crate::leanh::lean_ctor_get(v_inst_214_, 0);
    v_toFunctor_220_ = crate::leanh::lean_ctor_get(v_toApplicative_219_, 0);
    crate::leanh::lean_inc_ref(v_toFunctor_220_);
    v_toBind_221_ = crate::leanh::lean_ctor_get(v_inst_214_, 1);
    crate::leanh::lean_inc(v_toBind_221_);
    crate::leanh::lean_dec_ref(v_inst_214_);
    v_ref_222_ = crate::leanh::lean_ctor_get(v_mutex_217_, 0);
    crate::leanh::lean_inc(v_ref_222_);
    v_mutex_223_ = crate::leanh::lean_ctor_get(v_mutex_217_, 1);
    crate::leanh::lean_inc_n(v_mutex_223_, 2);
    crate::leanh::lean_dec_ref(v_mutex_217_);
    v_map_224_ = crate::leanh::lean_ctor_get(v_toFunctor_220_, 0);
    crate::leanh::lean_inc(v_map_224_);
    crate::leanh::lean_dec_ref(v_toFunctor_220_);
    v___x_225_ = crate::leanh::lean_alloc_closure(
        l_Std_BaseRecursiveMutex_lock___boxed as *mut core::ffi::c_void,
        2,
        1,
    );
    crate::leanh::lean_closure_set(v___x_225_, 0, v_mutex_223_);
    crate::leanh::lean_inc(v_inst_215_);
    v___x_226_ = crate::leanh::lean_apply_2(v_inst_215_, crate::leanh::lean_box(0), v___x_225_);
    v___f_227_ = crate::leanh::lean_alloc_closure(
        l_Std_RecursiveMutex_atomically___redArg___lam__0 as *mut core::ffi::c_void,
        3,
        2,
    );
    crate::leanh::lean_closure_set(v___f_227_, 0, v_k_218_);
    crate::leanh::lean_closure_set(v___f_227_, 1, v_ref_222_);
    v___f_228_ = l_Std_RecursiveMutex_atomically___redArg___closed__0;
    v___x_229_ = crate::leanh::lean_apply_4(
        v_toBind_221_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___x_226_,
        v___f_227_,
    );
    v___x_230_ = crate::leanh::lean_alloc_closure(
        l_Std_BaseRecursiveMutex_unlock___boxed as *mut core::ffi::c_void,
        2,
        1,
    );
    crate::leanh::lean_closure_set(v___x_230_, 0, v_mutex_223_);
    v___x_231_ = crate::leanh::lean_apply_2(v_inst_215_, crate::leanh::lean_box(0), v___x_230_);
    v___f_232_ = crate::leanh::lean_alloc_closure(
        l_Std_RecursiveMutex_atomically___redArg___lam__2___boxed as *mut core::ffi::c_void,
        2,
        1,
    );
    crate::leanh::lean_closure_set(v___f_232_, 0, v___x_231_);
    v_y_233_ = crate::leanh::lean_apply_4(
        v_inst_216_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___x_229_,
        v___f_232_,
    );
    v___x_234_ = crate::leanh::lean_apply_4(
        v_map_224_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___f_228_,
        v_y_233_,
    );
    return v___x_234_;
}
pub unsafe fn l_Std_RecursiveMutex_atomically(
    mut v_m_235_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_236_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_237_: *mut crate::leanh::LeanObject,
    mut v_inst_238_: *mut crate::leanh::LeanObject,
    mut v_inst_239_: *mut crate::leanh::LeanObject,
    mut v_inst_240_: *mut crate::leanh::LeanObject,
    mut v_mutex_241_: *mut crate::leanh::LeanObject,
    mut v_k_242_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_243_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_243_ = l_Std_RecursiveMutex_atomically___redArg(
        v_inst_238_,
        v_inst_239_,
        v_inst_240_,
        v_mutex_241_,
        v_k_242_,
    );
    return v___x_243_;
}
pub unsafe fn l_Std_RecursiveMutex_tryAtomically___redArg___lam__0(
    mut v_x_244_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_fst_245_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_fst_245_ = crate::leanh::lean_ctor_get(v_x_244_, 0);
    crate::leanh::lean_inc(v_fst_245_);
    return v_fst_245_;
}
pub unsafe fn l_Std_RecursiveMutex_tryAtomically___redArg___lam__0___boxed(
    mut v_x_246_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_247_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_247_ = l_Std_RecursiveMutex_tryAtomically___redArg___lam__0(v_x_246_);
    crate::leanh::lean_dec_ref(v_x_246_);
    return v_res_247_;
}
pub unsafe fn l_Std_RecursiveMutex_tryAtomically___redArg___lam__1(
    mut v_val_248_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_249_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_249_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_249_, 0, v_val_248_);
    return v___x_249_;
}
pub unsafe fn l_Std_RecursiveMutex_tryAtomically___redArg___lam__2(
    mut v___x_250_: *mut crate::leanh::LeanObject,
    mut v_x_251_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v___x_250_);
    return v___x_250_;
}
pub unsafe fn l_Std_RecursiveMutex_tryAtomically___redArg___lam__2___boxed(
    mut v___x_252_: *mut crate::leanh::LeanObject,
    mut v_x_253_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_254_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_254_ = l_Std_RecursiveMutex_tryAtomically___redArg___lam__2(v___x_252_, v_x_253_);
    crate::leanh::lean_dec(v_x_253_);
    crate::leanh::lean_dec(v___x_252_);
    return v_res_254_;
}
pub unsafe fn l_Std_RecursiveMutex_tryAtomically___redArg___lam__3(
    mut v_toApplicative_255_: *mut crate::leanh::LeanObject,
    mut v_k_256_: *mut crate::leanh::LeanObject,
    mut v_ref_257_: *mut crate::leanh::LeanObject,
    mut v___f_258_: *mut crate::leanh::LeanObject,
    mut v_mutex_259_: *mut crate::leanh::LeanObject,
    mut v_inst_260_: *mut crate::leanh::LeanObject,
    mut v_inst_261_: *mut crate::leanh::LeanObject,
    mut v___f_262_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_263_: u8,
) -> *mut crate::leanh::LeanObject {
    if v_____do__lift_263_ == 0 {
        let mut v_toPure_264_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_265_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_266_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec_ref(v___f_262_);
        crate::leanh::lean_dec(v_inst_261_);
        crate::leanh::lean_dec(v_inst_260_);
        crate::leanh::lean_dec(v_mutex_259_);
        crate::leanh::lean_dec_ref(v___f_258_);
        crate::leanh::lean_dec(v_ref_257_);
        crate::leanh::lean_dec(v_k_256_);
        v_toPure_264_ = crate::leanh::lean_ctor_get(v_toApplicative_255_, 1);
        crate::leanh::lean_inc(v_toPure_264_);
        crate::leanh::lean_dec_ref(v_toApplicative_255_);
        v___x_265_ = crate::leanh::lean_box(0);
        v___x_266_ =
            crate::leanh::lean_apply_2(v_toPure_264_, crate::leanh::lean_box(0), v___x_265_);
        return v___x_266_;
    } else {
        let mut v_toFunctor_267_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_map_268_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_269_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_270_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_271_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_272_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___f_273_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_y_274_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_275_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_toFunctor_267_ = crate::leanh::lean_ctor_get(v_toApplicative_255_, 0);
        crate::leanh::lean_inc_ref(v_toFunctor_267_);
        crate::leanh::lean_dec_ref(v_toApplicative_255_);
        v_map_268_ = crate::leanh::lean_ctor_get(v_toFunctor_267_, 0);
        crate::leanh::lean_inc_n(v_map_268_, 2);
        crate::leanh::lean_dec_ref(v_toFunctor_267_);
        v___x_269_ = crate::leanh::lean_apply_1(v_k_256_, v_ref_257_);
        v___x_270_ = crate::leanh::lean_apply_4(
            v_map_268_,
            crate::leanh::lean_box(0),
            crate::leanh::lean_box(0),
            v___f_258_,
            v___x_269_,
        );
        v___x_271_ = crate::leanh::lean_alloc_closure(
            l_Std_BaseRecursiveMutex_unlock___boxed as *mut core::ffi::c_void,
            2,
            1,
        );
        crate::leanh::lean_closure_set(v___x_271_, 0, v_mutex_259_);
        v___x_272_ = crate::leanh::lean_apply_2(v_inst_260_, crate::leanh::lean_box(0), v___x_271_);
        v___f_273_ = crate::leanh::lean_alloc_closure(
            l_Std_RecursiveMutex_tryAtomically___redArg___lam__2___boxed as *mut core::ffi::c_void,
            2,
            1,
        );
        crate::leanh::lean_closure_set(v___f_273_, 0, v___x_272_);
        v_y_274_ = crate::leanh::lean_apply_4(
            v_inst_261_,
            crate::leanh::lean_box(0),
            crate::leanh::lean_box(0),
            v___x_270_,
            v___f_273_,
        );
        v___x_275_ = crate::leanh::lean_apply_4(
            v_map_268_,
            crate::leanh::lean_box(0),
            crate::leanh::lean_box(0),
            v___f_262_,
            v_y_274_,
        );
        return v___x_275_;
    }
}
pub unsafe fn l_Std_RecursiveMutex_tryAtomically___redArg___lam__3___boxed(
    mut v_toApplicative_276_: *mut crate::leanh::LeanObject,
    mut v_k_277_: *mut crate::leanh::LeanObject,
    mut v_ref_278_: *mut crate::leanh::LeanObject,
    mut v___f_279_: *mut crate::leanh::LeanObject,
    mut v_mutex_280_: *mut crate::leanh::LeanObject,
    mut v_inst_281_: *mut crate::leanh::LeanObject,
    mut v_inst_282_: *mut crate::leanh::LeanObject,
    mut v___f_283_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_284_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_____do__lift_140__boxed_285_: u8 = 0;
    let mut v_res_286_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_____do__lift_140__boxed_285_ = (crate::leanh::lean_unbox(v_____do__lift_284_) as u8);
    v_res_286_ = l_Std_RecursiveMutex_tryAtomically___redArg___lam__3(
        v_toApplicative_276_,
        v_k_277_,
        v_ref_278_,
        v___f_279_,
        v_mutex_280_,
        v_inst_281_,
        v_inst_282_,
        v___f_283_,
        v_____do__lift_140__boxed_285_,
    );
    return v_res_286_;
}
pub unsafe fn l_Std_RecursiveMutex_tryAtomically___redArg(
    mut v_inst_289_: *mut crate::leanh::LeanObject,
    mut v_inst_290_: *mut crate::leanh::LeanObject,
    mut v_inst_291_: *mut crate::leanh::LeanObject,
    mut v_mutex_292_: *mut crate::leanh::LeanObject,
    mut v_k_293_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toApplicative_294_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_295_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_296_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_mutex_297_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_298_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_299_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_300_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_301_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_302_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_303_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_294_ = crate::leanh::lean_ctor_get(v_inst_289_, 0);
    crate::leanh::lean_inc_ref(v_toApplicative_294_);
    v_toBind_295_ = crate::leanh::lean_ctor_get(v_inst_289_, 1);
    crate::leanh::lean_inc(v_toBind_295_);
    crate::leanh::lean_dec_ref(v_inst_289_);
    v_ref_296_ = crate::leanh::lean_ctor_get(v_mutex_292_, 0);
    crate::leanh::lean_inc(v_ref_296_);
    v_mutex_297_ = crate::leanh::lean_ctor_get(v_mutex_292_, 1);
    crate::leanh::lean_inc_n(v_mutex_297_, 2);
    crate::leanh::lean_dec_ref(v_mutex_292_);
    v___f_298_ = l_Std_RecursiveMutex_tryAtomically___redArg___closed__0;
    v___f_299_ = l_Std_RecursiveMutex_tryAtomically___redArg___closed__1;
    crate::leanh::lean_inc(v_inst_290_);
    v___f_300_ = crate::leanh::lean_alloc_closure(
        l_Std_RecursiveMutex_tryAtomically___redArg___lam__3___boxed as *mut core::ffi::c_void,
        9,
        8,
    );
    crate::leanh::lean_closure_set(v___f_300_, 0, v_toApplicative_294_);
    crate::leanh::lean_closure_set(v___f_300_, 1, v_k_293_);
    crate::leanh::lean_closure_set(v___f_300_, 2, v_ref_296_);
    crate::leanh::lean_closure_set(v___f_300_, 3, v___f_299_);
    crate::leanh::lean_closure_set(v___f_300_, 4, v_mutex_297_);
    crate::leanh::lean_closure_set(v___f_300_, 5, v_inst_290_);
    crate::leanh::lean_closure_set(v___f_300_, 6, v_inst_291_);
    crate::leanh::lean_closure_set(v___f_300_, 7, v___f_298_);
    v___x_301_ = crate::leanh::lean_alloc_closure(
        l_Std_BaseRecursiveMutex_tryLock___boxed as *mut core::ffi::c_void,
        2,
        1,
    );
    crate::leanh::lean_closure_set(v___x_301_, 0, v_mutex_297_);
    v___x_302_ = crate::leanh::lean_apply_2(v_inst_290_, crate::leanh::lean_box(0), v___x_301_);
    v___x_303_ = crate::leanh::lean_apply_4(
        v_toBind_295_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___x_302_,
        v___f_300_,
    );
    return v___x_303_;
}
pub unsafe fn l_Std_RecursiveMutex_tryAtomically(
    mut v_m_304_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_305_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_306_: *mut crate::leanh::LeanObject,
    mut v_inst_307_: *mut crate::leanh::LeanObject,
    mut v_inst_308_: *mut crate::leanh::LeanObject,
    mut v_inst_309_: *mut crate::leanh::LeanObject,
    mut v_mutex_310_: *mut crate::leanh::LeanObject,
    mut v_k_311_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_312_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_312_ = l_Std_RecursiveMutex_tryAtomically___redArg(
        v_inst_307_,
        v_inst_308_,
        v_inst_309_,
        v_mutex_310_,
        v_k_311_,
    );
    return v___x_312_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Std_Sync_RecursiveMutex(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Std_Sync_Basic(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    l___private_Std_Sync_RecursiveMutex_0__Std_RecursiveMutexImpl =
        _init_l___private_Std_Sync_RecursiveMutex_0__Std_RecursiveMutexImpl();
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Std_Sync_RecursiveMutex(
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
pub unsafe fn initialize_Std_Sync_RecursiveMutex(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Std_Sync_Basic(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Std_Sync_RecursiveMutex(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Std_Sync_RecursiveMutex(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Std_Sync_RecursiveMutex(builtin);
}
