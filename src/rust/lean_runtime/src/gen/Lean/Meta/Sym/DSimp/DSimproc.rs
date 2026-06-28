// Lean compiler output
// Module: Lean.Meta.Sym.DSimp.DSimproc
// Imports: Lean.Meta.Sym.DSimp.Result
use crate::r#gen::Lean::CoreM::l_Lean_Exception_isRuntime;
use crate::r#gen::Lean::Exception::l_Lean_Exception_isInterrupt;
use crate::r#gen::Lean::Meta::Sym::DSimp::Result::{
    initialize_Lean_Meta_Sym_DSimp_Result, runtime_initialize_Lean_Meta_Sym_DSimp_Result,
};
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_alloc_ctor, lean_apply_11, lean_apply_12, lean_box,
    lean_ctor_get, lean_ctor_get_uint8, lean_ctor_set, lean_ctor_set_tag, lean_ctor_set_uint8,
    lean_dec, lean_dec_ref, lean_dec_ref_known, lean_del_object, lean_inc, lean_inc_ref,
    lean_io_result_is_error, lean_io_result_mk_ok, lean_is_exclusive, lean_obj_tag,
};
pub static l_Lean_Meta_Sym_DSimp_instAndThenDSimproc___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_Lean_Meta_Sym_DSimp_instAndThenDSimproc___lam__0___boxed
            as *const core::ffi::c_void,
        m_arity: 13,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Meta_Sym_DSimp_instAndThenDSimproc___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Sym_DSimp_instAndThenDSimproc___closed__0_value)
        as *mut LeanObject;
pub static mut l_Lean_Meta_Sym_DSimp_instAndThenDSimproc: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Sym_DSimp_instAndThenDSimproc___closed__0_value)
        as *mut LeanObject;
pub static l_Lean_Meta_Sym_DSimp_instOrElseDSimproc___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_Lean_Meta_Sym_DSimp_instOrElseDSimproc___lam__0___boxed
            as *const core::ffi::c_void,
        m_arity: 13,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Meta_Sym_DSimp_instOrElseDSimproc___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Sym_DSimp_instOrElseDSimproc___closed__0_value)
        as *mut LeanObject;
pub static mut l_Lean_Meta_Sym_DSimp_instOrElseDSimproc: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Sym_DSimp_instOrElseDSimproc___closed__0_value)
        as *mut LeanObject;
pub unsafe fn l_Lean_Meta_Sym_DSimp_DSimproc_andThen(
    mut v_f_211_: *mut LeanObject,
    mut v_g_212_: *mut LeanObject,
    mut v_e_u2081_213_: *mut LeanObject,
    mut v_a_214_: *mut LeanObject,
    mut v_a_215_: *mut LeanObject,
    mut v_a_216_: *mut LeanObject,
    mut v_a_217_: *mut LeanObject,
    mut v_a_218_: *mut LeanObject,
    mut v_a_219_: *mut LeanObject,
    mut v_a_220_: *mut LeanObject,
    mut v_a_221_: *mut LeanObject,
    mut v_a_222_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_224_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_225_: *mut LeanObject = core::ptr::null_mut();
    let mut v_done_226_: u8 = 0;
    let mut v___x_227_: *mut LeanObject = core::ptr::null_mut();
    let mut v_done_228_: u8 = 0;
    let mut v_e_x27_229_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_231_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_232_: u8 = 0;
    let mut v___x_233_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_234_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_236_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_237_: u8 = 0;
    let mut v_done_238_: u8 = 0;
    let mut v___x_240_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_242_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_243_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_244_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_245_: u8 = 0;
    let mut v_unused_246_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_247_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                lean_inc(v_a_222_);
                lean_inc_ref(v_a_221_);
                lean_inc(v_a_220_);
                lean_inc_ref(v_a_219_);
                lean_inc(v_a_218_);
                lean_inc_ref(v_a_217_);
                lean_inc(v_a_216_);
                lean_inc(v_a_215_);
                lean_inc(v_a_214_);
                lean_inc_ref(v_e_u2081_213_);
                v___x_224_ = lean_apply_11(
                    v_f_211_,
                    v_e_u2081_213_,
                    v_a_214_,
                    v_a_215_,
                    v_a_216_,
                    v_a_217_,
                    v_a_218_,
                    v_a_219_,
                    v_a_220_,
                    v_a_221_,
                    v_a_222_,
                    lean_box(0),
                );
                if lean_obj_tag(v___x_224_) == 0 {
                    v_a_225_ = lean_ctor_get(v___x_224_, 0);
                    lean_inc(v_a_225_);
                    if lean_obj_tag(v_a_225_) == 0 {
                        v_done_226_ = lean_ctor_get_uint8(v_a_225_, 0 as u32);
                        lean_dec_ref_known(v_a_225_, 0);
                        if v_done_226_ == 0 {
                            lean_dec_ref_known(v___x_224_, 1);
                            lean_inc(v_a_222_);
                            lean_inc_ref(v_a_221_);
                            lean_inc(v_a_220_);
                            lean_inc_ref(v_a_219_);
                            lean_inc(v_a_218_);
                            lean_inc_ref(v_a_217_);
                            lean_inc(v_a_216_);
                            lean_inc(v_a_215_);
                            lean_inc(v_a_214_);
                            v___x_227_ = lean_apply_11(
                                v_g_212_,
                                v_e_u2081_213_,
                                v_a_214_,
                                v_a_215_,
                                v_a_216_,
                                v_a_217_,
                                v_a_218_,
                                v_a_219_,
                                v_a_220_,
                                v_a_221_,
                                v_a_222_,
                                lean_box(0),
                            );
                            return v___x_227_;
                        } else {
                            lean_dec_ref(v_e_u2081_213_);
                            lean_dec_ref(v_g_212_);
                            return v___x_224_;
                        }
                    } else {
                        lean_dec_ref(v_e_u2081_213_);
                        v_done_228_ = lean_ctor_get_uint8(
                            v_a_225_,
                            (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                        );
                        if v_done_228_ == 0 {
                            lean_dec_ref_known(v___x_224_, 1);
                            v_e_x27_229_ = lean_ctor_get(v_a_225_, 0);
                            v_isSharedCheck_247_ = (!lean_is_exclusive(v_a_225_)) as u8;
                            if v_isSharedCheck_247_ == 0 {
                                v___x_231_ = v_a_225_;
                                v_isShared_232_ = v_isSharedCheck_247_;
                                state = 1;
                                continue;
                            } else {
                                lean_inc(v_e_x27_229_);
                                lean_dec(v_a_225_);
                                v___x_231_ = lean_box(0);
                                v_isShared_232_ = v_isSharedCheck_247_;
                                state = 1;
                                continue;
                            }
                        } else {
                            lean_dec_ref_known(v_a_225_, 1);
                            lean_dec_ref(v_g_212_);
                            return v___x_224_;
                        }
                    }
                } else {
                    lean_dec_ref(v_e_u2081_213_);
                    lean_dec_ref(v_g_212_);
                    return v___x_224_;
                }
            }
            1 => {
                lean_inc(v_a_222_);
                lean_inc_ref(v_a_221_);
                lean_inc(v_a_220_);
                lean_inc_ref(v_a_219_);
                lean_inc(v_a_218_);
                lean_inc_ref(v_a_217_);
                lean_inc(v_a_216_);
                lean_inc(v_a_215_);
                lean_inc(v_a_214_);
                lean_inc_ref(v_e_x27_229_);
                v___x_233_ = lean_apply_11(
                    v_g_212_,
                    v_e_x27_229_,
                    v_a_214_,
                    v_a_215_,
                    v_a_216_,
                    v_a_217_,
                    v_a_218_,
                    v_a_219_,
                    v_a_220_,
                    v_a_221_,
                    v_a_222_,
                    lean_box(0),
                );
                if lean_obj_tag(v___x_233_) == 0 {
                    v_a_234_ = lean_ctor_get(v___x_233_, 0);
                    lean_inc(v_a_234_);
                    if lean_obj_tag(v_a_234_) == 0 {
                        v_isSharedCheck_245_ = (!lean_is_exclusive(v___x_233_)) as u8;
                        if v_isSharedCheck_245_ == 0 {
                            v_unused_246_ = lean_ctor_get(v___x_233_, 0);
                            lean_dec(v_unused_246_);
                            v___x_236_ = v___x_233_;
                            v_isShared_237_ = v_isSharedCheck_245_;
                            state = 2;
                            continue;
                        } else {
                            lean_dec(v___x_233_);
                            v___x_236_ = lean_box(0);
                            v_isShared_237_ = v_isSharedCheck_245_;
                            state = 2;
                            continue;
                        }
                    } else {
                        lean_dec_ref_known(v_a_234_, 1);
                        lean_del_object(v___x_231_);
                        lean_dec_ref(v_e_x27_229_);
                        return v___x_233_;
                    }
                } else {
                    lean_del_object(v___x_231_);
                    lean_dec_ref(v_e_x27_229_);
                    return v___x_233_;
                }
            }
            2 => {
                v_done_238_ = lean_ctor_get_uint8(v_a_234_, 0 as u32);
                lean_dec_ref_known(v_a_234_, 0);
                if v_isShared_232_ == 0 {
                    v___x_240_ = v___x_231_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_244_ = lean_alloc_ctor(1, 1, (1) as u32);
                    lean_ctor_set(v_reuseFailAlloc_244_, 0, v_e_x27_229_);
                    v___x_240_ = v_reuseFailAlloc_244_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                lean_ctor_set_uint8(
                    v___x_240_,
                    (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                    v_done_238_,
                );
                if v_isShared_237_ == 0 {
                    lean_ctor_set(v___x_236_, 0, v___x_240_);
                    v___x_242_ = v___x_236_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_243_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_243_, 0, v___x_240_);
                    v___x_242_ = v_reuseFailAlloc_243_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_242_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Sym_DSimp_DSimproc_andThen___boxed(
    mut v_f_248_: *mut LeanObject,
    mut v_g_249_: *mut LeanObject,
    mut v_e_u2081_250_: *mut LeanObject,
    mut v_a_251_: *mut LeanObject,
    mut v_a_252_: *mut LeanObject,
    mut v_a_253_: *mut LeanObject,
    mut v_a_254_: *mut LeanObject,
    mut v_a_255_: *mut LeanObject,
    mut v_a_256_: *mut LeanObject,
    mut v_a_257_: *mut LeanObject,
    mut v_a_258_: *mut LeanObject,
    mut v_a_259_: *mut LeanObject,
    mut v_a_260_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_261_: *mut LeanObject = core::ptr::null_mut();
    v_res_261_ = l_Lean_Meta_Sym_DSimp_DSimproc_andThen(
        v_f_248_,
        v_g_249_,
        v_e_u2081_250_,
        v_a_251_,
        v_a_252_,
        v_a_253_,
        v_a_254_,
        v_a_255_,
        v_a_256_,
        v_a_257_,
        v_a_258_,
        v_a_259_,
    );
    lean_dec(v_a_259_);
    lean_dec_ref(v_a_258_);
    lean_dec(v_a_257_);
    lean_dec_ref(v_a_256_);
    lean_dec(v_a_255_);
    lean_dec_ref(v_a_254_);
    lean_dec(v_a_253_);
    lean_dec(v_a_252_);
    lean_dec(v_a_251_);
    return v_res_261_;
}
pub unsafe fn l_Lean_Meta_Sym_DSimp_instAndThenDSimproc___lam__0(
    mut v_f_262_: *mut LeanObject,
    mut v_g_263_: *mut LeanObject,
    mut v___y_264_: *mut LeanObject,
    mut v___y_265_: *mut LeanObject,
    mut v___y_266_: *mut LeanObject,
    mut v___y_267_: *mut LeanObject,
    mut v___y_268_: *mut LeanObject,
    mut v___y_269_: *mut LeanObject,
    mut v___y_270_: *mut LeanObject,
    mut v___y_271_: *mut LeanObject,
    mut v___y_272_: *mut LeanObject,
    mut v___y_273_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_275_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_276_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_277_: *mut LeanObject = core::ptr::null_mut();
    let mut v_done_278_: u8 = 0;
    let mut v___x_279_: *mut LeanObject = core::ptr::null_mut();
    let mut v_done_280_: u8 = 0;
    let mut v_e_x27_281_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_283_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_284_: u8 = 0;
    let mut v___x_285_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_286_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_288_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_289_: u8 = 0;
    let mut v_done_290_: u8 = 0;
    let mut v___x_292_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_294_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_295_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_296_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_297_: u8 = 0;
    let mut v_unused_298_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_299_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                lean_inc(v___y_273_);
                lean_inc_ref(v___y_272_);
                lean_inc(v___y_271_);
                lean_inc_ref(v___y_270_);
                lean_inc(v___y_269_);
                lean_inc_ref(v___y_268_);
                lean_inc(v___y_267_);
                lean_inc(v___y_266_);
                lean_inc(v___y_265_);
                lean_inc_ref(v___y_264_);
                v___x_275_ = lean_apply_11(
                    v_f_262_,
                    v___y_264_,
                    v___y_265_,
                    v___y_266_,
                    v___y_267_,
                    v___y_268_,
                    v___y_269_,
                    v___y_270_,
                    v___y_271_,
                    v___y_272_,
                    v___y_273_,
                    lean_box(0),
                );
                if lean_obj_tag(v___x_275_) == 0 {
                    v_a_276_ = lean_ctor_get(v___x_275_, 0);
                    lean_inc(v_a_276_);
                    v___x_277_ = lean_box(0);
                    if lean_obj_tag(v_a_276_) == 0 {
                        v_done_278_ = lean_ctor_get_uint8(v_a_276_, 0 as u32);
                        lean_dec_ref_known(v_a_276_, 0);
                        if v_done_278_ == 0 {
                            lean_dec_ref_known(v___x_275_, 1);
                            lean_inc(v___y_273_);
                            lean_inc_ref(v___y_272_);
                            lean_inc(v___y_271_);
                            lean_inc_ref(v___y_270_);
                            lean_inc(v___y_269_);
                            lean_inc_ref(v___y_268_);
                            lean_inc(v___y_267_);
                            lean_inc(v___y_266_);
                            lean_inc(v___y_265_);
                            v___x_279_ = lean_apply_12(
                                v_g_263_,
                                v___x_277_,
                                v___y_264_,
                                v___y_265_,
                                v___y_266_,
                                v___y_267_,
                                v___y_268_,
                                v___y_269_,
                                v___y_270_,
                                v___y_271_,
                                v___y_272_,
                                v___y_273_,
                                lean_box(0),
                            );
                            return v___x_279_;
                        } else {
                            lean_dec_ref(v___y_264_);
                            lean_dec_ref(v_g_263_);
                            return v___x_275_;
                        }
                    } else {
                        lean_dec_ref(v___y_264_);
                        v_done_280_ = lean_ctor_get_uint8(
                            v_a_276_,
                            (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                        );
                        if v_done_280_ == 0 {
                            lean_dec_ref_known(v___x_275_, 1);
                            v_e_x27_281_ = lean_ctor_get(v_a_276_, 0);
                            v_isSharedCheck_299_ = (!lean_is_exclusive(v_a_276_)) as u8;
                            if v_isSharedCheck_299_ == 0 {
                                v___x_283_ = v_a_276_;
                                v_isShared_284_ = v_isSharedCheck_299_;
                                state = 1;
                                continue;
                            } else {
                                lean_inc(v_e_x27_281_);
                                lean_dec(v_a_276_);
                                v___x_283_ = lean_box(0);
                                v_isShared_284_ = v_isSharedCheck_299_;
                                state = 1;
                                continue;
                            }
                        } else {
                            lean_dec_ref_known(v_a_276_, 1);
                            lean_dec_ref(v_g_263_);
                            return v___x_275_;
                        }
                    }
                } else {
                    lean_dec_ref(v___y_264_);
                    lean_dec_ref(v_g_263_);
                    return v___x_275_;
                }
            }
            1 => {
                lean_inc(v___y_273_);
                lean_inc_ref(v___y_272_);
                lean_inc(v___y_271_);
                lean_inc_ref(v___y_270_);
                lean_inc(v___y_269_);
                lean_inc_ref(v___y_268_);
                lean_inc(v___y_267_);
                lean_inc(v___y_266_);
                lean_inc(v___y_265_);
                lean_inc_ref(v_e_x27_281_);
                v___x_285_ = lean_apply_12(
                    v_g_263_,
                    v___x_277_,
                    v_e_x27_281_,
                    v___y_265_,
                    v___y_266_,
                    v___y_267_,
                    v___y_268_,
                    v___y_269_,
                    v___y_270_,
                    v___y_271_,
                    v___y_272_,
                    v___y_273_,
                    lean_box(0),
                );
                if lean_obj_tag(v___x_285_) == 0 {
                    v_a_286_ = lean_ctor_get(v___x_285_, 0);
                    lean_inc(v_a_286_);
                    if lean_obj_tag(v_a_286_) == 0 {
                        v_isSharedCheck_297_ = (!lean_is_exclusive(v___x_285_)) as u8;
                        if v_isSharedCheck_297_ == 0 {
                            v_unused_298_ = lean_ctor_get(v___x_285_, 0);
                            lean_dec(v_unused_298_);
                            v___x_288_ = v___x_285_;
                            v_isShared_289_ = v_isSharedCheck_297_;
                            state = 2;
                            continue;
                        } else {
                            lean_dec(v___x_285_);
                            v___x_288_ = lean_box(0);
                            v_isShared_289_ = v_isSharedCheck_297_;
                            state = 2;
                            continue;
                        }
                    } else {
                        lean_dec_ref_known(v_a_286_, 1);
                        lean_del_object(v___x_283_);
                        lean_dec_ref(v_e_x27_281_);
                        return v___x_285_;
                    }
                } else {
                    lean_del_object(v___x_283_);
                    lean_dec_ref(v_e_x27_281_);
                    return v___x_285_;
                }
            }
            2 => {
                v_done_290_ = lean_ctor_get_uint8(v_a_286_, 0 as u32);
                lean_dec_ref_known(v_a_286_, 0);
                if v_isShared_284_ == 0 {
                    v___x_292_ = v___x_283_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_296_ = lean_alloc_ctor(1, 1, (1) as u32);
                    lean_ctor_set(v_reuseFailAlloc_296_, 0, v_e_x27_281_);
                    v___x_292_ = v_reuseFailAlloc_296_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                lean_ctor_set_uint8(
                    v___x_292_,
                    (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                    v_done_290_,
                );
                if v_isShared_289_ == 0 {
                    lean_ctor_set(v___x_288_, 0, v___x_292_);
                    v___x_294_ = v___x_288_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_295_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_295_, 0, v___x_292_);
                    v___x_294_ = v_reuseFailAlloc_295_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_294_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Sym_DSimp_instAndThenDSimproc___lam__0___boxed(
    mut v_f_300_: *mut LeanObject,
    mut v_g_301_: *mut LeanObject,
    mut v___y_302_: *mut LeanObject,
    mut v___y_303_: *mut LeanObject,
    mut v___y_304_: *mut LeanObject,
    mut v___y_305_: *mut LeanObject,
    mut v___y_306_: *mut LeanObject,
    mut v___y_307_: *mut LeanObject,
    mut v___y_308_: *mut LeanObject,
    mut v___y_309_: *mut LeanObject,
    mut v___y_310_: *mut LeanObject,
    mut v___y_311_: *mut LeanObject,
    mut v___y_312_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_313_: *mut LeanObject = core::ptr::null_mut();
    v_res_313_ = l_Lean_Meta_Sym_DSimp_instAndThenDSimproc___lam__0(
        v_f_300_, v_g_301_, v___y_302_, v___y_303_, v___y_304_, v___y_305_, v___y_306_, v___y_307_,
        v___y_308_, v___y_309_, v___y_310_, v___y_311_,
    );
    lean_dec(v___y_311_);
    lean_dec_ref(v___y_310_);
    lean_dec(v___y_309_);
    lean_dec_ref(v___y_308_);
    lean_dec(v___y_307_);
    lean_dec_ref(v___y_306_);
    lean_dec(v___y_305_);
    lean_dec(v___y_304_);
    lean_dec(v___y_303_);
    return v_res_313_;
}
pub unsafe fn l_Lean_Meta_Sym_DSimp_DSimproc_orElse(
    mut v_f_316_: *mut LeanObject,
    mut v_g_317_: *mut LeanObject,
    mut v_e_u2081_318_: *mut LeanObject,
    mut v_a_319_: *mut LeanObject,
    mut v_a_320_: *mut LeanObject,
    mut v_a_321_: *mut LeanObject,
    mut v_a_322_: *mut LeanObject,
    mut v_a_323_: *mut LeanObject,
    mut v_a_324_: *mut LeanObject,
    mut v_a_325_: *mut LeanObject,
    mut v_a_326_: *mut LeanObject,
    mut v_a_327_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_329_: *mut LeanObject = core::ptr::null_mut();
    lean_inc(v_a_327_);
    lean_inc_ref(v_a_326_);
    lean_inc(v_a_325_);
    lean_inc_ref(v_a_324_);
    lean_inc(v_a_323_);
    lean_inc_ref(v_a_322_);
    lean_inc(v_a_321_);
    lean_inc(v_a_320_);
    lean_inc(v_a_319_);
    lean_inc_ref(v_e_u2081_318_);
    v___x_329_ = lean_apply_11(
        v_f_316_,
        v_e_u2081_318_,
        v_a_319_,
        v_a_320_,
        v_a_321_,
        v_a_322_,
        v_a_323_,
        v_a_324_,
        v_a_325_,
        v_a_326_,
        v_a_327_,
        lean_box(0),
    );
    if lean_obj_tag(v___x_329_) == 0 {
        let mut v_a_330_: *mut LeanObject = core::ptr::null_mut();
        v_a_330_ = lean_ctor_get(v___x_329_, 0);
        lean_inc(v_a_330_);
        if lean_obj_tag(v_a_330_) == 0 {
            let mut v_done_331_: u8 = 0;
            v_done_331_ = lean_ctor_get_uint8(v_a_330_, 0 as u32);
            lean_dec_ref_known(v_a_330_, 0);
            if v_done_331_ == 0 {
                let mut v___x_332_: *mut LeanObject = core::ptr::null_mut();
                lean_dec_ref_known(v___x_329_, 1);
                lean_inc(v_a_327_);
                lean_inc_ref(v_a_326_);
                lean_inc(v_a_325_);
                lean_inc_ref(v_a_324_);
                lean_inc(v_a_323_);
                lean_inc_ref(v_a_322_);
                lean_inc(v_a_321_);
                lean_inc(v_a_320_);
                lean_inc(v_a_319_);
                v___x_332_ = lean_apply_11(
                    v_g_317_,
                    v_e_u2081_318_,
                    v_a_319_,
                    v_a_320_,
                    v_a_321_,
                    v_a_322_,
                    v_a_323_,
                    v_a_324_,
                    v_a_325_,
                    v_a_326_,
                    v_a_327_,
                    lean_box(0),
                );
                return v___x_332_;
            } else {
                lean_dec_ref(v_e_u2081_318_);
                lean_dec_ref(v_g_317_);
                return v___x_329_;
            }
        } else {
            lean_dec_ref_known(v_a_330_, 1);
            lean_dec_ref(v_e_u2081_318_);
            lean_dec_ref(v_g_317_);
            return v___x_329_;
        }
    } else {
        lean_dec_ref(v_e_u2081_318_);
        lean_dec_ref(v_g_317_);
        return v___x_329_;
    }
}
pub unsafe fn l_Lean_Meta_Sym_DSimp_DSimproc_orElse___boxed(
    mut v_f_333_: *mut LeanObject,
    mut v_g_334_: *mut LeanObject,
    mut v_e_u2081_335_: *mut LeanObject,
    mut v_a_336_: *mut LeanObject,
    mut v_a_337_: *mut LeanObject,
    mut v_a_338_: *mut LeanObject,
    mut v_a_339_: *mut LeanObject,
    mut v_a_340_: *mut LeanObject,
    mut v_a_341_: *mut LeanObject,
    mut v_a_342_: *mut LeanObject,
    mut v_a_343_: *mut LeanObject,
    mut v_a_344_: *mut LeanObject,
    mut v_a_345_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_346_: *mut LeanObject = core::ptr::null_mut();
    v_res_346_ = l_Lean_Meta_Sym_DSimp_DSimproc_orElse(
        v_f_333_,
        v_g_334_,
        v_e_u2081_335_,
        v_a_336_,
        v_a_337_,
        v_a_338_,
        v_a_339_,
        v_a_340_,
        v_a_341_,
        v_a_342_,
        v_a_343_,
        v_a_344_,
    );
    lean_dec(v_a_344_);
    lean_dec_ref(v_a_343_);
    lean_dec(v_a_342_);
    lean_dec_ref(v_a_341_);
    lean_dec(v_a_340_);
    lean_dec_ref(v_a_339_);
    lean_dec(v_a_338_);
    lean_dec(v_a_337_);
    lean_dec(v_a_336_);
    return v_res_346_;
}
pub unsafe fn l_Lean_Meta_Sym_DSimp_instOrElseDSimproc___lam__0(
    mut v_f_347_: *mut LeanObject,
    mut v_g_348_: *mut LeanObject,
    mut v___y_349_: *mut LeanObject,
    mut v___y_350_: *mut LeanObject,
    mut v___y_351_: *mut LeanObject,
    mut v___y_352_: *mut LeanObject,
    mut v___y_353_: *mut LeanObject,
    mut v___y_354_: *mut LeanObject,
    mut v___y_355_: *mut LeanObject,
    mut v___y_356_: *mut LeanObject,
    mut v___y_357_: *mut LeanObject,
    mut v___y_358_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_360_: *mut LeanObject = core::ptr::null_mut();
    lean_inc(v___y_358_);
    lean_inc_ref(v___y_357_);
    lean_inc(v___y_356_);
    lean_inc_ref(v___y_355_);
    lean_inc(v___y_354_);
    lean_inc_ref(v___y_353_);
    lean_inc(v___y_352_);
    lean_inc(v___y_351_);
    lean_inc(v___y_350_);
    lean_inc_ref(v___y_349_);
    v___x_360_ = lean_apply_11(
        v_f_347_,
        v___y_349_,
        v___y_350_,
        v___y_351_,
        v___y_352_,
        v___y_353_,
        v___y_354_,
        v___y_355_,
        v___y_356_,
        v___y_357_,
        v___y_358_,
        lean_box(0),
    );
    if lean_obj_tag(v___x_360_) == 0 {
        let mut v_a_361_: *mut LeanObject = core::ptr::null_mut();
        v_a_361_ = lean_ctor_get(v___x_360_, 0);
        lean_inc(v_a_361_);
        if lean_obj_tag(v_a_361_) == 0 {
            let mut v_done_362_: u8 = 0;
            v_done_362_ = lean_ctor_get_uint8(v_a_361_, 0 as u32);
            lean_dec_ref_known(v_a_361_, 0);
            if v_done_362_ == 0 {
                let mut v___x_363_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_364_: *mut LeanObject = core::ptr::null_mut();
                lean_dec_ref_known(v___x_360_, 1);
                v___x_363_ = lean_box(0);
                lean_inc(v___y_358_);
                lean_inc_ref(v___y_357_);
                lean_inc(v___y_356_);
                lean_inc_ref(v___y_355_);
                lean_inc(v___y_354_);
                lean_inc_ref(v___y_353_);
                lean_inc(v___y_352_);
                lean_inc(v___y_351_);
                lean_inc(v___y_350_);
                v___x_364_ = lean_apply_12(
                    v_g_348_,
                    v___x_363_,
                    v___y_349_,
                    v___y_350_,
                    v___y_351_,
                    v___y_352_,
                    v___y_353_,
                    v___y_354_,
                    v___y_355_,
                    v___y_356_,
                    v___y_357_,
                    v___y_358_,
                    lean_box(0),
                );
                return v___x_364_;
            } else {
                lean_dec_ref(v___y_349_);
                lean_dec_ref(v_g_348_);
                return v___x_360_;
            }
        } else {
            lean_dec_ref_known(v_a_361_, 1);
            lean_dec_ref(v___y_349_);
            lean_dec_ref(v_g_348_);
            return v___x_360_;
        }
    } else {
        lean_dec_ref(v___y_349_);
        lean_dec_ref(v_g_348_);
        return v___x_360_;
    }
}
pub unsafe fn l_Lean_Meta_Sym_DSimp_instOrElseDSimproc___lam__0___boxed(
    mut v_f_365_: *mut LeanObject,
    mut v_g_366_: *mut LeanObject,
    mut v___y_367_: *mut LeanObject,
    mut v___y_368_: *mut LeanObject,
    mut v___y_369_: *mut LeanObject,
    mut v___y_370_: *mut LeanObject,
    mut v___y_371_: *mut LeanObject,
    mut v___y_372_: *mut LeanObject,
    mut v___y_373_: *mut LeanObject,
    mut v___y_374_: *mut LeanObject,
    mut v___y_375_: *mut LeanObject,
    mut v___y_376_: *mut LeanObject,
    mut v___y_377_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_378_: *mut LeanObject = core::ptr::null_mut();
    v_res_378_ = l_Lean_Meta_Sym_DSimp_instOrElseDSimproc___lam__0(
        v_f_365_, v_g_366_, v___y_367_, v___y_368_, v___y_369_, v___y_370_, v___y_371_, v___y_372_,
        v___y_373_, v___y_374_, v___y_375_, v___y_376_,
    );
    lean_dec(v___y_376_);
    lean_dec_ref(v___y_375_);
    lean_dec(v___y_374_);
    lean_dec_ref(v___y_373_);
    lean_dec(v___y_372_);
    lean_dec_ref(v___y_371_);
    lean_dec(v___y_370_);
    lean_dec(v___y_369_);
    lean_dec(v___y_368_);
    return v_res_378_;
}
pub unsafe fn l_Lean_Meta_Sym_DSimp_DSimproc_tryCatch(
    mut v_f_381_: *mut LeanObject,
    mut v_e_382_: *mut LeanObject,
    mut v_a_383_: *mut LeanObject,
    mut v_a_384_: *mut LeanObject,
    mut v_a_385_: *mut LeanObject,
    mut v_a_386_: *mut LeanObject,
    mut v_a_387_: *mut LeanObject,
    mut v_a_388_: *mut LeanObject,
    mut v_a_389_: *mut LeanObject,
    mut v_a_390_: *mut LeanObject,
    mut v_a_391_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_393_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_394_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_396_: u8 = 0;
    let mut v___x_398_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_399_: u8 = 0;
    let mut v___x_400_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_402_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_403_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_404_: u8 = 0;
    let mut v_unused_405_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_406_: u8 = 0;
    let mut v___x_407_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                lean_inc(v_a_391_);
                lean_inc_ref(v_a_390_);
                lean_inc(v_a_389_);
                lean_inc_ref(v_a_388_);
                lean_inc(v_a_387_);
                lean_inc_ref(v_a_386_);
                lean_inc(v_a_385_);
                lean_inc(v_a_384_);
                lean_inc(v_a_383_);
                v___x_393_ = lean_apply_11(
                    v_f_381_,
                    v_e_382_,
                    v_a_383_,
                    v_a_384_,
                    v_a_385_,
                    v_a_386_,
                    v_a_387_,
                    v_a_388_,
                    v_a_389_,
                    v_a_390_,
                    v_a_391_,
                    lean_box(0),
                );
                if lean_obj_tag(v___x_393_) == 0 {
                    return v___x_393_;
                } else {
                    v_a_394_ = lean_ctor_get(v___x_393_, 0);
                    lean_inc(v_a_394_);
                    v___x_406_ = l_Lean_Exception_isInterrupt(v_a_394_);
                    if v___x_406_ == 0 {
                        v___x_407_ = l_Lean_Exception_isRuntime(v_a_394_);
                        v___y_396_ = v___x_407_;
                        state = 1;
                        continue;
                    } else {
                        lean_dec(v_a_394_);
                        v___y_396_ = v___x_406_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v___y_396_ == 0 {
                    v_isSharedCheck_404_ = (!lean_is_exclusive(v___x_393_)) as u8;
                    if v_isSharedCheck_404_ == 0 {
                        v_unused_405_ = lean_ctor_get(v___x_393_, 0);
                        lean_dec(v_unused_405_);
                        v___x_398_ = v___x_393_;
                        v_isShared_399_ = v_isSharedCheck_404_;
                        state = 2;
                        continue;
                    } else {
                        lean_dec(v___x_393_);
                        v___x_398_ = lean_box(0);
                        v_isShared_399_ = v_isSharedCheck_404_;
                        state = 2;
                        continue;
                    }
                } else {
                    return v___x_393_;
                }
            }
            2 => {
                v___x_400_ = lean_alloc_ctor(0, 0, (1) as u32);
                lean_ctor_set_uint8(v___x_400_, 0 as u32, v___y_396_);
                if v_isShared_399_ == 0 {
                    lean_ctor_set_tag(v___x_398_, 0);
                    lean_ctor_set(v___x_398_, 0, v___x_400_);
                    v___x_402_ = v___x_398_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_403_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_403_, 0, v___x_400_);
                    v___x_402_ = v_reuseFailAlloc_403_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_402_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Sym_DSimp_DSimproc_tryCatch___boxed(
    mut v_f_408_: *mut LeanObject,
    mut v_e_409_: *mut LeanObject,
    mut v_a_410_: *mut LeanObject,
    mut v_a_411_: *mut LeanObject,
    mut v_a_412_: *mut LeanObject,
    mut v_a_413_: *mut LeanObject,
    mut v_a_414_: *mut LeanObject,
    mut v_a_415_: *mut LeanObject,
    mut v_a_416_: *mut LeanObject,
    mut v_a_417_: *mut LeanObject,
    mut v_a_418_: *mut LeanObject,
    mut v_a_419_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_420_: *mut LeanObject = core::ptr::null_mut();
    v_res_420_ = l_Lean_Meta_Sym_DSimp_DSimproc_tryCatch(
        v_f_408_, v_e_409_, v_a_410_, v_a_411_, v_a_412_, v_a_413_, v_a_414_, v_a_415_, v_a_416_,
        v_a_417_, v_a_418_,
    );
    lean_dec(v_a_418_);
    lean_dec_ref(v_a_417_);
    lean_dec(v_a_416_);
    lean_dec_ref(v_a_415_);
    lean_dec(v_a_414_);
    lean_dec_ref(v_a_413_);
    lean_dec(v_a_412_);
    lean_dec(v_a_411_);
    lean_dec(v_a_410_);
    return v_res_420_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Meta_Sym_DSimp_DSimproc(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Meta_Sym_DSimp_Result(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Meta_Sym_DSimp_DSimproc(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_meta_initialized = true;
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lean_Meta_Sym_DSimp_DSimproc(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Meta_Sym_DSimp_Result(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Sym_DSimp_DSimproc(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Lean_Meta_Sym_DSimp_DSimproc(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Lean_Meta_Sym_DSimp_DSimproc(builtin);
}
