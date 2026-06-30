// Lean compiler output
// Module: Std.Do.WP.Monad
// Imports: Std.Do.WP.Basic Std.Do.WP.Basic
use crate::r#gen::Std::Do::WP::Basic::{
    initialize_Std_Do_WP_Basic, l_Std_Do_EStateM_instWP, l_Std_Do_Except_instWP___aux__1,
    l_Std_Do_ExceptT_instWP___redArg___lam__0, l_Std_Do_Id_instWP___lam__0,
    l_Std_Do_Option_instWP___aux__1, l_Std_Do_OptionT_instWP___redArg___lam__0,
    l_Std_Do_Reader_instWP, l_Std_Do_ReaderT_instWP___redArg___lam__2,
    l_Std_Do_State_instWP___lam__1, l_Std_Do_StateT_instWP___redArg___lam__1,
    runtime_initialize_Std_Do_WP_Basic,
};
pub static l_Std_Do_Id_instWPMonad___closed__0_value: leanh::LeanClosureObject<0> =
    leanh::LeanClosureObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut leanh::LeanObject>() * 0)
                as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Std_Do_Id_instWP___lam__0 as *const core::ffi::c_void,
        m_arity: 3,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Std_Do_Id_instWPMonad___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Do_Id_instWPMonad___closed__0_value) as *mut leanh::LeanObject;
pub static mut l_Std_Do_Id_instWPMonad: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Do_Id_instWPMonad___closed__0_value) as *mut leanh::LeanObject;
static mut l_Std_Do_EStateM_instWPMonad___closed__0_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Do_EStateM_instWPMonad___closed__0: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Std_Do_Except_instWPMonad___closed__0_value: leanh::LeanClosureObject<1> =
    leanh::LeanClosureObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut leanh::LeanObject>() * 1)
                as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Std_Do_Except_instWP___aux__1 as *const core::ffi::c_void,
        m_arity: 3,
        m_num_fixed: 1,
        m_objs: [(((0 as usize) << 1) | 1) as *mut leanh::LeanObject],
    };
static mut l_Std_Do_Except_instWPMonad___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Do_Except_instWPMonad___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Std_Do_Option_instWPMonad___closed__0_value: leanh::LeanClosureObject<0> =
    leanh::LeanClosureObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut leanh::LeanObject>() * 0)
                as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Std_Do_Option_instWP___aux__1 as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Std_Do_Option_instWPMonad___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Do_Option_instWPMonad___closed__0_value)
        as *mut leanh::LeanObject;
pub static mut l_Std_Do_Option_instWPMonad: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Do_Option_instWPMonad___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Std_Do_State_instWPMonad___closed__0_value: leanh::LeanClosureObject<0> =
    leanh::LeanClosureObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut leanh::LeanObject>() * 0)
                as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Std_Do_State_instWP___lam__1 as *const core::ffi::c_void,
        m_arity: 3,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Std_Do_State_instWPMonad___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Do_State_instWPMonad___closed__0_value)
        as *mut leanh::LeanObject;
static mut l_Std_Do_Reader_instWPMonad___closed__0_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Do_Reader_instWPMonad___closed__0: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub unsafe fn l_Std_Do_StateT_instWPMonad___redArg(
    mut v_inst_188_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_189_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_189_ = leanh::lean_alloc_closure(
        l_Std_Do_StateT_instWP___redArg___lam__1 as *mut core::ffi::c_void,
        4,
        1,
    );
    leanh::lean_closure_set(v___f_189_, 0, v_inst_188_);
    return v___f_189_;
}
pub unsafe fn l_Std_Do_StateT_instWPMonad(
    mut v_m_190_: *mut leanh::LeanObject,
    mut v_ps_191_: *mut leanh::LeanObject,
    mut v_00_u03c3_192_: *mut leanh::LeanObject,
    mut v_inst_193_: *mut leanh::LeanObject,
    mut v_inst_194_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_195_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_195_ = leanh::lean_alloc_closure(
        l_Std_Do_StateT_instWP___redArg___lam__1 as *mut core::ffi::c_void,
        4,
        1,
    );
    leanh::lean_closure_set(v___f_195_, 0, v_inst_194_);
    return v___f_195_;
}
pub unsafe fn l_Std_Do_StateT_instWPMonad___boxed(
    mut v_m_196_: *mut leanh::LeanObject,
    mut v_ps_197_: *mut leanh::LeanObject,
    mut v_00_u03c3_198_: *mut leanh::LeanObject,
    mut v_inst_199_: *mut leanh::LeanObject,
    mut v_inst_200_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_201_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_201_ = l_Std_Do_StateT_instWPMonad(
        v_m_196_,
        v_ps_197_,
        v_00_u03c3_198_,
        v_inst_199_,
        v_inst_200_,
    );
    leanh::lean_dec_ref(v_inst_199_);
    leanh::lean_dec(v_ps_197_);
    return v_res_201_;
}
pub unsafe fn l_Std_Do_ReaderT_instWPMonad___redArg(
    mut v_ps_202_: *mut leanh::LeanObject,
    mut v_inst_203_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_204_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_204_ = leanh::lean_alloc_closure(
        l_Std_Do_ReaderT_instWP___redArg___lam__2 as *mut core::ffi::c_void,
        5,
        2,
    );
    leanh::lean_closure_set(v___f_204_, 0, v_inst_203_);
    leanh::lean_closure_set(v___f_204_, 1, v_ps_202_);
    return v___f_204_;
}
pub unsafe fn l_Std_Do_ReaderT_instWPMonad(
    mut v_m_205_: *mut leanh::LeanObject,
    mut v_ps_206_: *mut leanh::LeanObject,
    mut v_00_u03c1_207_: *mut leanh::LeanObject,
    mut v_inst_208_: *mut leanh::LeanObject,
    mut v_inst_209_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_210_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_210_ = leanh::lean_alloc_closure(
        l_Std_Do_ReaderT_instWP___redArg___lam__2 as *mut core::ffi::c_void,
        5,
        2,
    );
    leanh::lean_closure_set(v___f_210_, 0, v_inst_209_);
    leanh::lean_closure_set(v___f_210_, 1, v_ps_206_);
    return v___f_210_;
}
pub unsafe fn l_Std_Do_ReaderT_instWPMonad___boxed(
    mut v_m_211_: *mut leanh::LeanObject,
    mut v_ps_212_: *mut leanh::LeanObject,
    mut v_00_u03c1_213_: *mut leanh::LeanObject,
    mut v_inst_214_: *mut leanh::LeanObject,
    mut v_inst_215_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_216_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_216_ = l_Std_Do_ReaderT_instWPMonad(
        v_m_211_,
        v_ps_212_,
        v_00_u03c1_213_,
        v_inst_214_,
        v_inst_215_,
    );
    leanh::lean_dec_ref(v_inst_214_);
    return v_res_216_;
}
pub unsafe fn l___private_Std_Do_WP_Monad_0__Std_Do_PredTrans_pushExcept_match__1_splitter___redArg(
    mut v_x_217_: *mut leanh::LeanObject,
    mut v_h__1_218_: *mut leanh::LeanObject,
    mut v_h__2_219_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_x_217_) == 0 {
        let mut v_a_220_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_221_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__1_218_);
        v_a_220_ = leanh::lean_ctor_get(v_x_217_, 0);
        leanh::lean_inc(v_a_220_);
        leanh::lean_dec_ref_known(v_x_217_, 1);
        v___x_221_ = leanh::lean_apply_1(v_h__2_219_, v_a_220_);
        return v___x_221_;
    } else {
        let mut v_a_222_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_223_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__2_219_);
        v_a_222_ = leanh::lean_ctor_get(v_x_217_, 0);
        leanh::lean_inc(v_a_222_);
        leanh::lean_dec_ref_known(v_x_217_, 1);
        v___x_223_ = leanh::lean_apply_1(v_h__1_218_, v_a_222_);
        return v___x_223_;
    }
}
pub unsafe fn l___private_Std_Do_WP_Monad_0__Std_Do_PredTrans_pushExcept_match__1_splitter(
    mut v_00_u03b1_224_: *mut leanh::LeanObject,
    mut v_00_u03b5_225_: *mut leanh::LeanObject,
    mut v_motive_226_: *mut leanh::LeanObject,
    mut v_x_227_: *mut leanh::LeanObject,
    mut v_h__1_228_: *mut leanh::LeanObject,
    mut v_h__2_229_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_x_227_) == 0 {
        let mut v_a_230_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_231_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__1_228_);
        v_a_230_ = leanh::lean_ctor_get(v_x_227_, 0);
        leanh::lean_inc(v_a_230_);
        leanh::lean_dec_ref_known(v_x_227_, 1);
        v___x_231_ = leanh::lean_apply_1(v_h__2_229_, v_a_230_);
        return v___x_231_;
    } else {
        let mut v_a_232_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_233_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__2_229_);
        v_a_232_ = leanh::lean_ctor_get(v_x_227_, 0);
        leanh::lean_inc(v_a_232_);
        leanh::lean_dec_ref_known(v_x_227_, 1);
        v___x_233_ = leanh::lean_apply_1(v_h__1_228_, v_a_232_);
        return v___x_233_;
    }
}
pub unsafe fn l___private_Std_Do_WP_Monad_0__ExceptT_run__bind_match__1_splitter___redArg(
    mut v_x_234_: *mut leanh::LeanObject,
    mut v_h__1_235_: *mut leanh::LeanObject,
    mut v_h__2_236_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_x_234_) == 0 {
        let mut v_a_237_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_238_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__1_235_);
        v_a_237_ = leanh::lean_ctor_get(v_x_234_, 0);
        leanh::lean_inc(v_a_237_);
        leanh::lean_dec_ref_known(v_x_234_, 1);
        v___x_238_ = leanh::lean_apply_1(v_h__2_236_, v_a_237_);
        return v___x_238_;
    } else {
        let mut v_a_239_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_240_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__2_236_);
        v_a_239_ = leanh::lean_ctor_get(v_x_234_, 0);
        leanh::lean_inc(v_a_239_);
        leanh::lean_dec_ref_known(v_x_234_, 1);
        v___x_240_ = leanh::lean_apply_1(v_h__1_235_, v_a_239_);
        return v___x_240_;
    }
}
pub unsafe fn l___private_Std_Do_WP_Monad_0__ExceptT_run__bind_match__1_splitter(
    mut v_00_u03b5_241_: *mut leanh::LeanObject,
    mut v_00_u03b1_242_: *mut leanh::LeanObject,
    mut v_motive_243_: *mut leanh::LeanObject,
    mut v_x_244_: *mut leanh::LeanObject,
    mut v_h__1_245_: *mut leanh::LeanObject,
    mut v_h__2_246_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_x_244_) == 0 {
        let mut v_a_247_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_248_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__1_245_);
        v_a_247_ = leanh::lean_ctor_get(v_x_244_, 0);
        leanh::lean_inc(v_a_247_);
        leanh::lean_dec_ref_known(v_x_244_, 1);
        v___x_248_ = leanh::lean_apply_1(v_h__2_246_, v_a_247_);
        return v___x_248_;
    } else {
        let mut v_a_249_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_250_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__2_246_);
        v_a_249_ = leanh::lean_ctor_get(v_x_244_, 0);
        leanh::lean_inc(v_a_249_);
        leanh::lean_dec_ref_known(v_x_244_, 1);
        v___x_250_ = leanh::lean_apply_1(v_h__1_245_, v_a_249_);
        return v___x_250_;
    }
}
pub unsafe fn l_Std_Do_ExceptT_instWPMonad___redArg(
    mut v_inst_251_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_252_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_252_ = leanh::lean_alloc_closure(
        l_Std_Do_ExceptT_instWP___redArg___lam__0 as *mut core::ffi::c_void,
        4,
        1,
    );
    leanh::lean_closure_set(v___f_252_, 0, v_inst_251_);
    return v___f_252_;
}
pub unsafe fn l_Std_Do_ExceptT_instWPMonad(
    mut v_m_253_: *mut leanh::LeanObject,
    mut v_ps_254_: *mut leanh::LeanObject,
    mut v_00_u03b5_255_: *mut leanh::LeanObject,
    mut v_inst_256_: *mut leanh::LeanObject,
    mut v_inst_257_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_258_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_258_ = leanh::lean_alloc_closure(
        l_Std_Do_ExceptT_instWP___redArg___lam__0 as *mut core::ffi::c_void,
        4,
        1,
    );
    leanh::lean_closure_set(v___f_258_, 0, v_inst_257_);
    return v___f_258_;
}
pub unsafe fn l_Std_Do_ExceptT_instWPMonad___boxed(
    mut v_m_259_: *mut leanh::LeanObject,
    mut v_ps_260_: *mut leanh::LeanObject,
    mut v_00_u03b5_261_: *mut leanh::LeanObject,
    mut v_inst_262_: *mut leanh::LeanObject,
    mut v_inst_263_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_264_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_264_ = l_Std_Do_ExceptT_instWPMonad(
        v_m_259_,
        v_ps_260_,
        v_00_u03b5_261_,
        v_inst_262_,
        v_inst_263_,
    );
    leanh::lean_dec_ref(v_inst_262_);
    leanh::lean_dec(v_ps_260_);
    return v_res_264_;
}
pub unsafe fn l___private_Std_Do_WP_Monad_0__Std_Do_PredTrans_pushOption_match__1_splitter___redArg(
    mut v_x_265_: *mut leanh::LeanObject,
    mut v_h__1_266_: *mut leanh::LeanObject,
    mut v_h__2_267_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_x_265_) == 0 {
        let mut v___x_268_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_269_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__1_266_);
        v___x_268_ = leanh::lean_box(0);
        v___x_269_ = leanh::lean_apply_1(v_h__2_267_, v___x_268_);
        return v___x_269_;
    } else {
        let mut v_val_270_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_271_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__2_267_);
        v_val_270_ = leanh::lean_ctor_get(v_x_265_, 0);
        leanh::lean_inc(v_val_270_);
        leanh::lean_dec_ref_known(v_x_265_, 1);
        v___x_271_ = leanh::lean_apply_1(v_h__1_266_, v_val_270_);
        return v___x_271_;
    }
}
pub unsafe fn l___private_Std_Do_WP_Monad_0__Std_Do_PredTrans_pushOption_match__1_splitter(
    mut v_00_u03b1_272_: *mut leanh::LeanObject,
    mut v_motive_273_: *mut leanh::LeanObject,
    mut v_x_274_: *mut leanh::LeanObject,
    mut v_h__1_275_: *mut leanh::LeanObject,
    mut v_h__2_276_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_x_274_) == 0 {
        let mut v___x_277_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_278_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__1_275_);
        v___x_277_ = leanh::lean_box(0);
        v___x_278_ = leanh::lean_apply_1(v_h__2_276_, v___x_277_);
        return v___x_278_;
    } else {
        let mut v_val_279_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_280_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__2_276_);
        v_val_279_ = leanh::lean_ctor_get(v_x_274_, 0);
        leanh::lean_inc(v_val_279_);
        leanh::lean_dec_ref_known(v_x_274_, 1);
        v___x_280_ = leanh::lean_apply_1(v_h__1_275_, v_val_279_);
        return v___x_280_;
    }
}
pub unsafe fn l___private_Std_Do_WP_Monad_0__Option_elim_match__1_splitter___redArg(
    mut v_x_281_: *mut leanh::LeanObject,
    mut v_x_282_: *mut leanh::LeanObject,
    mut v_x_283_: *mut leanh::LeanObject,
    mut v_h__1_284_: *mut leanh::LeanObject,
    mut v_h__2_285_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_x_281_) == 0 {
        let mut v___x_286_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__1_284_);
        v___x_286_ = leanh::lean_apply_2(v_h__2_285_, v_x_282_, v_x_283_);
        return v___x_286_;
    } else {
        let mut v_val_287_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_288_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__2_285_);
        v_val_287_ = leanh::lean_ctor_get(v_x_281_, 0);
        leanh::lean_inc(v_val_287_);
        leanh::lean_dec_ref_known(v_x_281_, 1);
        v___x_288_ = leanh::lean_apply_3(v_h__1_284_, v_val_287_, v_x_282_, v_x_283_);
        return v___x_288_;
    }
}
pub unsafe fn l___private_Std_Do_WP_Monad_0__Option_elim_match__1_splitter(
    mut v_00_u03b1_289_: *mut leanh::LeanObject,
    mut v_00_u03b2_290_: *mut leanh::LeanObject,
    mut v_motive_291_: *mut leanh::LeanObject,
    mut v_x_292_: *mut leanh::LeanObject,
    mut v_x_293_: *mut leanh::LeanObject,
    mut v_x_294_: *mut leanh::LeanObject,
    mut v_h__1_295_: *mut leanh::LeanObject,
    mut v_h__2_296_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_x_292_) == 0 {
        let mut v___x_297_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__1_295_);
        v___x_297_ = leanh::lean_apply_2(v_h__2_296_, v_x_293_, v_x_294_);
        return v___x_297_;
    } else {
        let mut v_val_298_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_299_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__2_296_);
        v_val_298_ = leanh::lean_ctor_get(v_x_292_, 0);
        leanh::lean_inc(v_val_298_);
        leanh::lean_dec_ref_known(v_x_292_, 1);
        v___x_299_ = leanh::lean_apply_3(v_h__1_295_, v_val_298_, v_x_293_, v_x_294_);
        return v___x_299_;
    }
}
pub unsafe fn l_Std_Do_OptionT_instWPMonad___redArg(
    mut v_inst_300_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_301_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_301_ = leanh::lean_alloc_closure(
        l_Std_Do_OptionT_instWP___redArg___lam__0 as *mut core::ffi::c_void,
        4,
        1,
    );
    leanh::lean_closure_set(v___f_301_, 0, v_inst_300_);
    return v___f_301_;
}
pub unsafe fn l_Std_Do_OptionT_instWPMonad(
    mut v_m_302_: *mut leanh::LeanObject,
    mut v_ps_303_: *mut leanh::LeanObject,
    mut v_inst_304_: *mut leanh::LeanObject,
    mut v_inst_305_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_306_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_306_ = leanh::lean_alloc_closure(
        l_Std_Do_OptionT_instWP___redArg___lam__0 as *mut core::ffi::c_void,
        4,
        1,
    );
    leanh::lean_closure_set(v___f_306_, 0, v_inst_305_);
    return v___f_306_;
}
pub unsafe fn l_Std_Do_OptionT_instWPMonad___boxed(
    mut v_m_307_: *mut leanh::LeanObject,
    mut v_ps_308_: *mut leanh::LeanObject,
    mut v_inst_309_: *mut leanh::LeanObject,
    mut v_inst_310_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_311_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_311_ = l_Std_Do_OptionT_instWPMonad(v_m_307_, v_ps_308_, v_inst_309_, v_inst_310_);
    leanh::lean_dec_ref(v_inst_309_);
    leanh::lean_dec(v_ps_308_);
    return v_res_311_;
}
pub unsafe fn l___private_Std_Do_WP_Monad_0__EStateM_run__bind_match__1_splitter___redArg(
    mut v_x_312_: *mut leanh::LeanObject,
    mut v_h__1_313_: *mut leanh::LeanObject,
    mut v_h__2_314_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_x_312_) == 0 {
        let mut v_a_315_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_a_316_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_317_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__2_314_);
        v_a_315_ = leanh::lean_ctor_get(v_x_312_, 0);
        leanh::lean_inc(v_a_315_);
        v_a_316_ = leanh::lean_ctor_get(v_x_312_, 1);
        leanh::lean_inc(v_a_316_);
        leanh::lean_dec_ref_known(v_x_312_, 2);
        v___x_317_ = leanh::lean_apply_2(v_h__1_313_, v_a_315_, v_a_316_);
        return v___x_317_;
    } else {
        let mut v_a_318_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_a_319_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_320_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__1_313_);
        v_a_318_ = leanh::lean_ctor_get(v_x_312_, 0);
        leanh::lean_inc(v_a_318_);
        v_a_319_ = leanh::lean_ctor_get(v_x_312_, 1);
        leanh::lean_inc(v_a_319_);
        leanh::lean_dec_ref_known(v_x_312_, 2);
        v___x_320_ = leanh::lean_apply_2(v_h__2_314_, v_a_318_, v_a_319_);
        return v___x_320_;
    }
}
pub unsafe fn l___private_Std_Do_WP_Monad_0__EStateM_run__bind_match__1_splitter(
    mut v_00_u03b5_321_: *mut leanh::LeanObject,
    mut v_00_u03c3_322_: *mut leanh::LeanObject,
    mut v_00_u03b1_323_: *mut leanh::LeanObject,
    mut v_motive_324_: *mut leanh::LeanObject,
    mut v_x_325_: *mut leanh::LeanObject,
    mut v_h__1_326_: *mut leanh::LeanObject,
    mut v_h__2_327_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_x_325_) == 0 {
        let mut v_a_328_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_a_329_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_330_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__2_327_);
        v_a_328_ = leanh::lean_ctor_get(v_x_325_, 0);
        leanh::lean_inc(v_a_328_);
        v_a_329_ = leanh::lean_ctor_get(v_x_325_, 1);
        leanh::lean_inc(v_a_329_);
        leanh::lean_dec_ref_known(v_x_325_, 2);
        v___x_330_ = leanh::lean_apply_2(v_h__1_326_, v_a_328_, v_a_329_);
        return v___x_330_;
    } else {
        let mut v_a_331_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_a_332_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_333_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__1_326_);
        v_a_331_ = leanh::lean_ctor_get(v_x_325_, 0);
        leanh::lean_inc(v_a_331_);
        v_a_332_ = leanh::lean_ctor_get(v_x_325_, 1);
        leanh::lean_inc(v_a_332_);
        leanh::lean_dec_ref_known(v_x_325_, 2);
        v___x_333_ = leanh::lean_apply_2(v_h__2_327_, v_a_331_, v_a_332_);
        return v___x_333_;
    }
}
pub unsafe fn l___private_Std_Do_WP_Monad_0__Std_Do_EStateM_instWP_match__1_splitter___redArg(
    mut v_x_334_: *mut leanh::LeanObject,
    mut v_h__1_335_: *mut leanh::LeanObject,
    mut v_h__2_336_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_x_334_) == 0 {
        let mut v_a_337_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_a_338_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_339_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__2_336_);
        v_a_337_ = leanh::lean_ctor_get(v_x_334_, 0);
        leanh::lean_inc(v_a_337_);
        v_a_338_ = leanh::lean_ctor_get(v_x_334_, 1);
        leanh::lean_inc(v_a_338_);
        leanh::lean_dec_ref_known(v_x_334_, 2);
        v___x_339_ = leanh::lean_apply_2(v_h__1_335_, v_a_337_, v_a_338_);
        return v___x_339_;
    } else {
        let mut v_a_340_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_a_341_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_342_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__1_335_);
        v_a_340_ = leanh::lean_ctor_get(v_x_334_, 0);
        leanh::lean_inc(v_a_340_);
        v_a_341_ = leanh::lean_ctor_get(v_x_334_, 1);
        leanh::lean_inc(v_a_341_);
        leanh::lean_dec_ref_known(v_x_334_, 2);
        v___x_342_ = leanh::lean_apply_2(v_h__2_336_, v_a_340_, v_a_341_);
        return v___x_342_;
    }
}
pub unsafe fn l___private_Std_Do_WP_Monad_0__Std_Do_EStateM_instWP_match__1_splitter(
    mut v_00_u03b5_343_: *mut leanh::LeanObject,
    mut v_00_u03c3_344_: *mut leanh::LeanObject,
    mut v_00_u03b1_345_: *mut leanh::LeanObject,
    mut v_motive_346_: *mut leanh::LeanObject,
    mut v_x_347_: *mut leanh::LeanObject,
    mut v_h__1_348_: *mut leanh::LeanObject,
    mut v_h__2_349_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_x_347_) == 0 {
        let mut v_a_350_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_a_351_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_352_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__2_349_);
        v_a_350_ = leanh::lean_ctor_get(v_x_347_, 0);
        leanh::lean_inc(v_a_350_);
        v_a_351_ = leanh::lean_ctor_get(v_x_347_, 1);
        leanh::lean_inc(v_a_351_);
        leanh::lean_dec_ref_known(v_x_347_, 2);
        v___x_352_ = leanh::lean_apply_2(v_h__1_348_, v_a_350_, v_a_351_);
        return v___x_352_;
    } else {
        let mut v_a_353_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_a_354_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_355_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__1_348_);
        v_a_353_ = leanh::lean_ctor_get(v_x_347_, 0);
        leanh::lean_inc(v_a_353_);
        v_a_354_ = leanh::lean_ctor_get(v_x_347_, 1);
        leanh::lean_inc(v_a_354_);
        leanh::lean_dec_ref_known(v_x_347_, 2);
        v___x_355_ = leanh::lean_apply_2(v_h__2_349_, v_a_353_, v_a_354_);
        return v___x_355_;
    }
}
pub unsafe fn _init_l_Std_Do_EStateM_instWPMonad___closed__0() -> *mut leanh::LeanObject {
    let mut v___x_356_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_356_ = l_Std_Do_EStateM_instWP(leanh::lean_box(0), leanh::lean_box(0));
    return v___x_356_;
}
pub unsafe fn l_Std_Do_EStateM_instWPMonad(
    mut v_00_u03b5_357_: *mut leanh::LeanObject,
    mut v_00_u03c3_358_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_359_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_359_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Do_EStateM_instWPMonad___closed__0),
        core::ptr::addr_of_mut!(l_Std_Do_EStateM_instWPMonad___closed__0_once),
        _init_l_Std_Do_EStateM_instWPMonad___closed__0,
    );
    return v___x_359_;
}
pub unsafe fn l_Std_Do_Except_instWPMonad(
    mut v_00_u03b5_361_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_362_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_362_ = l_Std_Do_Except_instWPMonad___closed__0;
    return v___x_362_;
}
pub unsafe fn l_Std_Do_State_instWPMonad(
    mut v_00_u03c3_366_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_367_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_367_ = l_Std_Do_State_instWPMonad___closed__0;
    return v___f_367_;
}
pub unsafe fn _init_l_Std_Do_Reader_instWPMonad___closed__0() -> *mut leanh::LeanObject {
    let mut v___x_368_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_368_ = l_Std_Do_Reader_instWP(leanh::lean_box(0));
    return v___x_368_;
}
pub unsafe fn l_Std_Do_Reader_instWPMonad(
    mut v_00_u03c1_369_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_370_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_370_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Do_Reader_instWPMonad___closed__0),
        core::ptr::addr_of_mut!(l_Std_Do_Reader_instWPMonad___closed__0_once),
        _init_l_Std_Do_Reader_instWPMonad___closed__0,
    );
    return v___x_370_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Std_Do_WP_Monad(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Std_Do_WP_Basic(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Std_Do_WP_Basic(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Std_Do_WP_Monad(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_meta_initialized = true;
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Std_Do_WP_Monad(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Std_Do_WP_Basic(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Std_Do_WP_Basic(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Std_Do_WP_Monad(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = meta_initialize_Std_Do_WP_Monad(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return initialize_Std_Do_WP_Monad(builtin);
}