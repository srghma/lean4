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
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_alloc_closure, lean_apply_1, lean_apply_2, lean_apply_3,
    lean_box, lean_closure_set, lean_ctor_get, lean_dec, lean_dec_ref, lean_dec_ref_known,
    lean_inc, lean_io_result_is_error, lean_io_result_mk_ok, lean_obj_once, lean_obj_tag,
};
pub static l_Std_Do_Id_instWPMonad___closed__0_value: LeanClosureObject<0> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Std_Do_Id_instWP___lam__0 as *const core::ffi::c_void,
    m_arity: 3,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_Do_Id_instWPMonad___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Do_Id_instWPMonad___closed__0_value) as *mut LeanObject;
pub static mut l_Std_Do_Id_instWPMonad: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Do_Id_instWPMonad___closed__0_value) as *mut LeanObject;
static mut l_Std_Do_EStateM_instWPMonad___closed__0_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_Do_EStateM_instWPMonad___closed__0: *mut LeanObject = core::ptr::null_mut();
pub static l_Std_Do_Except_instWPMonad___closed__0_value: LeanClosureObject<1> =
    LeanClosureObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut LeanObject>() * 1) as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Std_Do_Except_instWP___aux__1 as *const core::ffi::c_void,
        m_arity: 3,
        m_num_fixed: 1,
        m_objs: [(((0 as usize) << 1) | 1) as *mut LeanObject],
    };
static mut l_Std_Do_Except_instWPMonad___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Do_Except_instWPMonad___closed__0_value) as *mut LeanObject;
pub static l_Std_Do_Option_instWPMonad___closed__0_value: LeanClosureObject<0> =
    LeanClosureObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Std_Do_Option_instWP___aux__1 as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Std_Do_Option_instWPMonad___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Do_Option_instWPMonad___closed__0_value) as *mut LeanObject;
pub static mut l_Std_Do_Option_instWPMonad: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Do_Option_instWPMonad___closed__0_value) as *mut LeanObject;
pub static l_Std_Do_State_instWPMonad___closed__0_value: LeanClosureObject<0> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Std_Do_State_instWP___lam__1 as *const core::ffi::c_void,
    m_arity: 3,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_Do_State_instWPMonad___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Do_State_instWPMonad___closed__0_value) as *mut LeanObject;
static mut l_Std_Do_Reader_instWPMonad___closed__0_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_Do_Reader_instWPMonad___closed__0: *mut LeanObject = core::ptr::null_mut();
pub unsafe fn l_Std_Do_StateT_instWPMonad___redArg(
    mut v_inst_188_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_189_: *mut LeanObject = core::ptr::null_mut();
    v___f_189_ = lean_alloc_closure(
        l_Std_Do_StateT_instWP___redArg___lam__1 as *mut core::ffi::c_void,
        4,
        1,
    );
    lean_closure_set(v___f_189_, 0, v_inst_188_);
    return v___f_189_;
}
pub unsafe fn l_Std_Do_StateT_instWPMonad(
    mut v_m_190_: *mut LeanObject,
    mut v_ps_191_: *mut LeanObject,
    mut v_00_u03c3_192_: *mut LeanObject,
    mut v_inst_193_: *mut LeanObject,
    mut v_inst_194_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_195_: *mut LeanObject = core::ptr::null_mut();
    v___f_195_ = lean_alloc_closure(
        l_Std_Do_StateT_instWP___redArg___lam__1 as *mut core::ffi::c_void,
        4,
        1,
    );
    lean_closure_set(v___f_195_, 0, v_inst_194_);
    return v___f_195_;
}
pub unsafe fn l_Std_Do_StateT_instWPMonad___boxed(
    mut v_m_196_: *mut LeanObject,
    mut v_ps_197_: *mut LeanObject,
    mut v_00_u03c3_198_: *mut LeanObject,
    mut v_inst_199_: *mut LeanObject,
    mut v_inst_200_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_201_: *mut LeanObject = core::ptr::null_mut();
    v_res_201_ = l_Std_Do_StateT_instWPMonad(
        v_m_196_,
        v_ps_197_,
        v_00_u03c3_198_,
        v_inst_199_,
        v_inst_200_,
    );
    lean_dec_ref(v_inst_199_);
    lean_dec(v_ps_197_);
    return v_res_201_;
}
pub unsafe fn l_Std_Do_ReaderT_instWPMonad___redArg(
    mut v_ps_202_: *mut LeanObject,
    mut v_inst_203_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_204_: *mut LeanObject = core::ptr::null_mut();
    v___f_204_ = lean_alloc_closure(
        l_Std_Do_ReaderT_instWP___redArg___lam__2 as *mut core::ffi::c_void,
        5,
        2,
    );
    lean_closure_set(v___f_204_, 0, v_inst_203_);
    lean_closure_set(v___f_204_, 1, v_ps_202_);
    return v___f_204_;
}
pub unsafe fn l_Std_Do_ReaderT_instWPMonad(
    mut v_m_205_: *mut LeanObject,
    mut v_ps_206_: *mut LeanObject,
    mut v_00_u03c1_207_: *mut LeanObject,
    mut v_inst_208_: *mut LeanObject,
    mut v_inst_209_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_210_: *mut LeanObject = core::ptr::null_mut();
    v___f_210_ = lean_alloc_closure(
        l_Std_Do_ReaderT_instWP___redArg___lam__2 as *mut core::ffi::c_void,
        5,
        2,
    );
    lean_closure_set(v___f_210_, 0, v_inst_209_);
    lean_closure_set(v___f_210_, 1, v_ps_206_);
    return v___f_210_;
}
pub unsafe fn l_Std_Do_ReaderT_instWPMonad___boxed(
    mut v_m_211_: *mut LeanObject,
    mut v_ps_212_: *mut LeanObject,
    mut v_00_u03c1_213_: *mut LeanObject,
    mut v_inst_214_: *mut LeanObject,
    mut v_inst_215_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_216_: *mut LeanObject = core::ptr::null_mut();
    v_res_216_ = l_Std_Do_ReaderT_instWPMonad(
        v_m_211_,
        v_ps_212_,
        v_00_u03c1_213_,
        v_inst_214_,
        v_inst_215_,
    );
    lean_dec_ref(v_inst_214_);
    return v_res_216_;
}
pub unsafe fn l___private_Std_Do_WP_Monad_0__Std_Do_PredTrans_pushExcept_match__1_splitter___redArg(
    mut v_x_217_: *mut LeanObject,
    mut v_h__1_218_: *mut LeanObject,
    mut v_h__2_219_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_217_) == 0 {
        let mut v_a_220_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_221_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_218_);
        v_a_220_ = lean_ctor_get(v_x_217_, 0);
        lean_inc(v_a_220_);
        lean_dec_ref_known(v_x_217_, 1);
        v___x_221_ = lean_apply_1(v_h__2_219_, v_a_220_);
        return v___x_221_;
    } else {
        let mut v_a_222_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_223_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_219_);
        v_a_222_ = lean_ctor_get(v_x_217_, 0);
        lean_inc(v_a_222_);
        lean_dec_ref_known(v_x_217_, 1);
        v___x_223_ = lean_apply_1(v_h__1_218_, v_a_222_);
        return v___x_223_;
    }
}
pub unsafe fn l___private_Std_Do_WP_Monad_0__Std_Do_PredTrans_pushExcept_match__1_splitter(
    mut v_00_u03b1_224_: *mut LeanObject,
    mut v_00_u03b5_225_: *mut LeanObject,
    mut v_motive_226_: *mut LeanObject,
    mut v_x_227_: *mut LeanObject,
    mut v_h__1_228_: *mut LeanObject,
    mut v_h__2_229_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_227_) == 0 {
        let mut v_a_230_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_231_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_228_);
        v_a_230_ = lean_ctor_get(v_x_227_, 0);
        lean_inc(v_a_230_);
        lean_dec_ref_known(v_x_227_, 1);
        v___x_231_ = lean_apply_1(v_h__2_229_, v_a_230_);
        return v___x_231_;
    } else {
        let mut v_a_232_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_233_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_229_);
        v_a_232_ = lean_ctor_get(v_x_227_, 0);
        lean_inc(v_a_232_);
        lean_dec_ref_known(v_x_227_, 1);
        v___x_233_ = lean_apply_1(v_h__1_228_, v_a_232_);
        return v___x_233_;
    }
}
pub unsafe fn l___private_Std_Do_WP_Monad_0__ExceptT_run__bind_match__1_splitter___redArg(
    mut v_x_234_: *mut LeanObject,
    mut v_h__1_235_: *mut LeanObject,
    mut v_h__2_236_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_234_) == 0 {
        let mut v_a_237_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_238_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_235_);
        v_a_237_ = lean_ctor_get(v_x_234_, 0);
        lean_inc(v_a_237_);
        lean_dec_ref_known(v_x_234_, 1);
        v___x_238_ = lean_apply_1(v_h__2_236_, v_a_237_);
        return v___x_238_;
    } else {
        let mut v_a_239_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_240_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_236_);
        v_a_239_ = lean_ctor_get(v_x_234_, 0);
        lean_inc(v_a_239_);
        lean_dec_ref_known(v_x_234_, 1);
        v___x_240_ = lean_apply_1(v_h__1_235_, v_a_239_);
        return v___x_240_;
    }
}
pub unsafe fn l___private_Std_Do_WP_Monad_0__ExceptT_run__bind_match__1_splitter(
    mut v_00_u03b5_241_: *mut LeanObject,
    mut v_00_u03b1_242_: *mut LeanObject,
    mut v_motive_243_: *mut LeanObject,
    mut v_x_244_: *mut LeanObject,
    mut v_h__1_245_: *mut LeanObject,
    mut v_h__2_246_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_244_) == 0 {
        let mut v_a_247_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_248_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_245_);
        v_a_247_ = lean_ctor_get(v_x_244_, 0);
        lean_inc(v_a_247_);
        lean_dec_ref_known(v_x_244_, 1);
        v___x_248_ = lean_apply_1(v_h__2_246_, v_a_247_);
        return v___x_248_;
    } else {
        let mut v_a_249_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_250_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_246_);
        v_a_249_ = lean_ctor_get(v_x_244_, 0);
        lean_inc(v_a_249_);
        lean_dec_ref_known(v_x_244_, 1);
        v___x_250_ = lean_apply_1(v_h__1_245_, v_a_249_);
        return v___x_250_;
    }
}
pub unsafe fn l_Std_Do_ExceptT_instWPMonad___redArg(
    mut v_inst_251_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_252_: *mut LeanObject = core::ptr::null_mut();
    v___f_252_ = lean_alloc_closure(
        l_Std_Do_ExceptT_instWP___redArg___lam__0 as *mut core::ffi::c_void,
        4,
        1,
    );
    lean_closure_set(v___f_252_, 0, v_inst_251_);
    return v___f_252_;
}
pub unsafe fn l_Std_Do_ExceptT_instWPMonad(
    mut v_m_253_: *mut LeanObject,
    mut v_ps_254_: *mut LeanObject,
    mut v_00_u03b5_255_: *mut LeanObject,
    mut v_inst_256_: *mut LeanObject,
    mut v_inst_257_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_258_: *mut LeanObject = core::ptr::null_mut();
    v___f_258_ = lean_alloc_closure(
        l_Std_Do_ExceptT_instWP___redArg___lam__0 as *mut core::ffi::c_void,
        4,
        1,
    );
    lean_closure_set(v___f_258_, 0, v_inst_257_);
    return v___f_258_;
}
pub unsafe fn l_Std_Do_ExceptT_instWPMonad___boxed(
    mut v_m_259_: *mut LeanObject,
    mut v_ps_260_: *mut LeanObject,
    mut v_00_u03b5_261_: *mut LeanObject,
    mut v_inst_262_: *mut LeanObject,
    mut v_inst_263_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_264_: *mut LeanObject = core::ptr::null_mut();
    v_res_264_ = l_Std_Do_ExceptT_instWPMonad(
        v_m_259_,
        v_ps_260_,
        v_00_u03b5_261_,
        v_inst_262_,
        v_inst_263_,
    );
    lean_dec_ref(v_inst_262_);
    lean_dec(v_ps_260_);
    return v_res_264_;
}
pub unsafe fn l___private_Std_Do_WP_Monad_0__Std_Do_PredTrans_pushOption_match__1_splitter___redArg(
    mut v_x_265_: *mut LeanObject,
    mut v_h__1_266_: *mut LeanObject,
    mut v_h__2_267_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_265_) == 0 {
        let mut v___x_268_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_269_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_266_);
        v___x_268_ = lean_box(0);
        v___x_269_ = lean_apply_1(v_h__2_267_, v___x_268_);
        return v___x_269_;
    } else {
        let mut v_val_270_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_271_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_267_);
        v_val_270_ = lean_ctor_get(v_x_265_, 0);
        lean_inc(v_val_270_);
        lean_dec_ref_known(v_x_265_, 1);
        v___x_271_ = lean_apply_1(v_h__1_266_, v_val_270_);
        return v___x_271_;
    }
}
pub unsafe fn l___private_Std_Do_WP_Monad_0__Std_Do_PredTrans_pushOption_match__1_splitter(
    mut v_00_u03b1_272_: *mut LeanObject,
    mut v_motive_273_: *mut LeanObject,
    mut v_x_274_: *mut LeanObject,
    mut v_h__1_275_: *mut LeanObject,
    mut v_h__2_276_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_274_) == 0 {
        let mut v___x_277_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_278_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_275_);
        v___x_277_ = lean_box(0);
        v___x_278_ = lean_apply_1(v_h__2_276_, v___x_277_);
        return v___x_278_;
    } else {
        let mut v_val_279_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_280_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_276_);
        v_val_279_ = lean_ctor_get(v_x_274_, 0);
        lean_inc(v_val_279_);
        lean_dec_ref_known(v_x_274_, 1);
        v___x_280_ = lean_apply_1(v_h__1_275_, v_val_279_);
        return v___x_280_;
    }
}
pub unsafe fn l___private_Std_Do_WP_Monad_0__Option_elim_match__1_splitter___redArg(
    mut v_x_281_: *mut LeanObject,
    mut v_x_282_: *mut LeanObject,
    mut v_x_283_: *mut LeanObject,
    mut v_h__1_284_: *mut LeanObject,
    mut v_h__2_285_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_281_) == 0 {
        let mut v___x_286_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_284_);
        v___x_286_ = lean_apply_2(v_h__2_285_, v_x_282_, v_x_283_);
        return v___x_286_;
    } else {
        let mut v_val_287_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_288_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_285_);
        v_val_287_ = lean_ctor_get(v_x_281_, 0);
        lean_inc(v_val_287_);
        lean_dec_ref_known(v_x_281_, 1);
        v___x_288_ = lean_apply_3(v_h__1_284_, v_val_287_, v_x_282_, v_x_283_);
        return v___x_288_;
    }
}
pub unsafe fn l___private_Std_Do_WP_Monad_0__Option_elim_match__1_splitter(
    mut v_00_u03b1_289_: *mut LeanObject,
    mut v_00_u03b2_290_: *mut LeanObject,
    mut v_motive_291_: *mut LeanObject,
    mut v_x_292_: *mut LeanObject,
    mut v_x_293_: *mut LeanObject,
    mut v_x_294_: *mut LeanObject,
    mut v_h__1_295_: *mut LeanObject,
    mut v_h__2_296_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_292_) == 0 {
        let mut v___x_297_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_295_);
        v___x_297_ = lean_apply_2(v_h__2_296_, v_x_293_, v_x_294_);
        return v___x_297_;
    } else {
        let mut v_val_298_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_299_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_296_);
        v_val_298_ = lean_ctor_get(v_x_292_, 0);
        lean_inc(v_val_298_);
        lean_dec_ref_known(v_x_292_, 1);
        v___x_299_ = lean_apply_3(v_h__1_295_, v_val_298_, v_x_293_, v_x_294_);
        return v___x_299_;
    }
}
pub unsafe fn l_Std_Do_OptionT_instWPMonad___redArg(
    mut v_inst_300_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_301_: *mut LeanObject = core::ptr::null_mut();
    v___f_301_ = lean_alloc_closure(
        l_Std_Do_OptionT_instWP___redArg___lam__0 as *mut core::ffi::c_void,
        4,
        1,
    );
    lean_closure_set(v___f_301_, 0, v_inst_300_);
    return v___f_301_;
}
pub unsafe fn l_Std_Do_OptionT_instWPMonad(
    mut v_m_302_: *mut LeanObject,
    mut v_ps_303_: *mut LeanObject,
    mut v_inst_304_: *mut LeanObject,
    mut v_inst_305_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_306_: *mut LeanObject = core::ptr::null_mut();
    v___f_306_ = lean_alloc_closure(
        l_Std_Do_OptionT_instWP___redArg___lam__0 as *mut core::ffi::c_void,
        4,
        1,
    );
    lean_closure_set(v___f_306_, 0, v_inst_305_);
    return v___f_306_;
}
pub unsafe fn l_Std_Do_OptionT_instWPMonad___boxed(
    mut v_m_307_: *mut LeanObject,
    mut v_ps_308_: *mut LeanObject,
    mut v_inst_309_: *mut LeanObject,
    mut v_inst_310_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_311_: *mut LeanObject = core::ptr::null_mut();
    v_res_311_ = l_Std_Do_OptionT_instWPMonad(v_m_307_, v_ps_308_, v_inst_309_, v_inst_310_);
    lean_dec_ref(v_inst_309_);
    lean_dec(v_ps_308_);
    return v_res_311_;
}
pub unsafe fn l___private_Std_Do_WP_Monad_0__EStateM_run__bind_match__1_splitter___redArg(
    mut v_x_312_: *mut LeanObject,
    mut v_h__1_313_: *mut LeanObject,
    mut v_h__2_314_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_312_) == 0 {
        let mut v_a_315_: *mut LeanObject = core::ptr::null_mut();
        let mut v_a_316_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_317_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_314_);
        v_a_315_ = lean_ctor_get(v_x_312_, 0);
        lean_inc(v_a_315_);
        v_a_316_ = lean_ctor_get(v_x_312_, 1);
        lean_inc(v_a_316_);
        lean_dec_ref_known(v_x_312_, 2);
        v___x_317_ = lean_apply_2(v_h__1_313_, v_a_315_, v_a_316_);
        return v___x_317_;
    } else {
        let mut v_a_318_: *mut LeanObject = core::ptr::null_mut();
        let mut v_a_319_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_320_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_313_);
        v_a_318_ = lean_ctor_get(v_x_312_, 0);
        lean_inc(v_a_318_);
        v_a_319_ = lean_ctor_get(v_x_312_, 1);
        lean_inc(v_a_319_);
        lean_dec_ref_known(v_x_312_, 2);
        v___x_320_ = lean_apply_2(v_h__2_314_, v_a_318_, v_a_319_);
        return v___x_320_;
    }
}
pub unsafe fn l___private_Std_Do_WP_Monad_0__EStateM_run__bind_match__1_splitter(
    mut v_00_u03b5_321_: *mut LeanObject,
    mut v_00_u03c3_322_: *mut LeanObject,
    mut v_00_u03b1_323_: *mut LeanObject,
    mut v_motive_324_: *mut LeanObject,
    mut v_x_325_: *mut LeanObject,
    mut v_h__1_326_: *mut LeanObject,
    mut v_h__2_327_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_325_) == 0 {
        let mut v_a_328_: *mut LeanObject = core::ptr::null_mut();
        let mut v_a_329_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_330_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_327_);
        v_a_328_ = lean_ctor_get(v_x_325_, 0);
        lean_inc(v_a_328_);
        v_a_329_ = lean_ctor_get(v_x_325_, 1);
        lean_inc(v_a_329_);
        lean_dec_ref_known(v_x_325_, 2);
        v___x_330_ = lean_apply_2(v_h__1_326_, v_a_328_, v_a_329_);
        return v___x_330_;
    } else {
        let mut v_a_331_: *mut LeanObject = core::ptr::null_mut();
        let mut v_a_332_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_333_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_326_);
        v_a_331_ = lean_ctor_get(v_x_325_, 0);
        lean_inc(v_a_331_);
        v_a_332_ = lean_ctor_get(v_x_325_, 1);
        lean_inc(v_a_332_);
        lean_dec_ref_known(v_x_325_, 2);
        v___x_333_ = lean_apply_2(v_h__2_327_, v_a_331_, v_a_332_);
        return v___x_333_;
    }
}
pub unsafe fn l___private_Std_Do_WP_Monad_0__Std_Do_EStateM_instWP_match__1_splitter___redArg(
    mut v_x_334_: *mut LeanObject,
    mut v_h__1_335_: *mut LeanObject,
    mut v_h__2_336_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_334_) == 0 {
        let mut v_a_337_: *mut LeanObject = core::ptr::null_mut();
        let mut v_a_338_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_339_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_336_);
        v_a_337_ = lean_ctor_get(v_x_334_, 0);
        lean_inc(v_a_337_);
        v_a_338_ = lean_ctor_get(v_x_334_, 1);
        lean_inc(v_a_338_);
        lean_dec_ref_known(v_x_334_, 2);
        v___x_339_ = lean_apply_2(v_h__1_335_, v_a_337_, v_a_338_);
        return v___x_339_;
    } else {
        let mut v_a_340_: *mut LeanObject = core::ptr::null_mut();
        let mut v_a_341_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_342_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_335_);
        v_a_340_ = lean_ctor_get(v_x_334_, 0);
        lean_inc(v_a_340_);
        v_a_341_ = lean_ctor_get(v_x_334_, 1);
        lean_inc(v_a_341_);
        lean_dec_ref_known(v_x_334_, 2);
        v___x_342_ = lean_apply_2(v_h__2_336_, v_a_340_, v_a_341_);
        return v___x_342_;
    }
}
pub unsafe fn l___private_Std_Do_WP_Monad_0__Std_Do_EStateM_instWP_match__1_splitter(
    mut v_00_u03b5_343_: *mut LeanObject,
    mut v_00_u03c3_344_: *mut LeanObject,
    mut v_00_u03b1_345_: *mut LeanObject,
    mut v_motive_346_: *mut LeanObject,
    mut v_x_347_: *mut LeanObject,
    mut v_h__1_348_: *mut LeanObject,
    mut v_h__2_349_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_347_) == 0 {
        let mut v_a_350_: *mut LeanObject = core::ptr::null_mut();
        let mut v_a_351_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_352_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_349_);
        v_a_350_ = lean_ctor_get(v_x_347_, 0);
        lean_inc(v_a_350_);
        v_a_351_ = lean_ctor_get(v_x_347_, 1);
        lean_inc(v_a_351_);
        lean_dec_ref_known(v_x_347_, 2);
        v___x_352_ = lean_apply_2(v_h__1_348_, v_a_350_, v_a_351_);
        return v___x_352_;
    } else {
        let mut v_a_353_: *mut LeanObject = core::ptr::null_mut();
        let mut v_a_354_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_355_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_348_);
        v_a_353_ = lean_ctor_get(v_x_347_, 0);
        lean_inc(v_a_353_);
        v_a_354_ = lean_ctor_get(v_x_347_, 1);
        lean_inc(v_a_354_);
        lean_dec_ref_known(v_x_347_, 2);
        v___x_355_ = lean_apply_2(v_h__2_349_, v_a_353_, v_a_354_);
        return v___x_355_;
    }
}
pub unsafe fn _init_l_Std_Do_EStateM_instWPMonad___closed__0() -> *mut LeanObject {
    let mut v___x_356_: *mut LeanObject = core::ptr::null_mut();
    v___x_356_ = l_Std_Do_EStateM_instWP(lean_box(0), lean_box(0));
    return v___x_356_;
}
pub unsafe fn l_Std_Do_EStateM_instWPMonad(
    mut v_00_u03b5_357_: *mut LeanObject,
    mut v_00_u03c3_358_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_359_: *mut LeanObject = core::ptr::null_mut();
    v___x_359_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Do_EStateM_instWPMonad___closed__0),
        core::ptr::addr_of_mut!(l_Std_Do_EStateM_instWPMonad___closed__0_once),
        _init_l_Std_Do_EStateM_instWPMonad___closed__0,
    );
    return v___x_359_;
}
pub unsafe fn l_Std_Do_Except_instWPMonad(mut v_00_u03b5_361_: *mut LeanObject) -> *mut LeanObject {
    let mut v___x_362_: *mut LeanObject = core::ptr::null_mut();
    v___x_362_ = l_Std_Do_Except_instWPMonad___closed__0;
    return v___x_362_;
}
pub unsafe fn l_Std_Do_State_instWPMonad(mut v_00_u03c3_366_: *mut LeanObject) -> *mut LeanObject {
    let mut v___f_367_: *mut LeanObject = core::ptr::null_mut();
    v___f_367_ = l_Std_Do_State_instWPMonad___closed__0;
    return v___f_367_;
}
pub unsafe fn _init_l_Std_Do_Reader_instWPMonad___closed__0() -> *mut LeanObject {
    let mut v___x_368_: *mut LeanObject = core::ptr::null_mut();
    v___x_368_ = l_Std_Do_Reader_instWP(lean_box(0));
    return v___x_368_;
}
pub unsafe fn l_Std_Do_Reader_instWPMonad(mut v_00_u03c1_369_: *mut LeanObject) -> *mut LeanObject {
    let mut v___x_370_: *mut LeanObject = core::ptr::null_mut();
    v___x_370_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Do_Reader_instWPMonad___closed__0),
        core::ptr::addr_of_mut!(l_Std_Do_Reader_instWPMonad___closed__0_once),
        _init_l_Std_Do_Reader_instWPMonad___closed__0,
    );
    return v___x_370_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Std_Do_WP_Monad(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Std_Do_WP_Basic(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Std_Do_WP_Monad(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_meta_initialized = true;
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Std_Do_WP_Monad(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Std_Do_WP_Basic(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Std_Do_WP_Monad(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Std_Do_WP_Monad(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Std_Do_WP_Monad(builtin);
}
