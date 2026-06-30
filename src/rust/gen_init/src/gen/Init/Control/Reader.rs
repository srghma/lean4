// Lean compiler output
// Module: Init.Control.Reader
// Imports: Init.Control.Except
use crate::r#gen::Init::Control::Except::{
    initialize_Init_Control_Except, runtime_initialize_Init_Control_Except,
};
use crate::r#gen::Init::Prelude::{
    l_ReaderT_instApplicativeOfMonad___redArg___lam__1,
    l_ReaderT_instApplicativeOfMonad___redArg___lam__3,
    l_ReaderT_instApplicativeOfMonad___redArg___lam__4,
    l_ReaderT_instFunctorOfMonad___redArg___lam__0, l_ReaderT_instFunctorOfMonad___redArg___lam__1,
    l_ReaderT_pure___boxed,
};
pub static l_instMonadControlReaderT___closed__0_value: leanh::LeanClosureObject<0> =
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
        m_fun: l_instMonadControlReaderT___lam__1 as *const core::ffi::c_void,
        m_arity: 3,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_instMonadControlReaderT___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_instMonadControlReaderT___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_instMonadControlReaderT___closed__1_value: leanh::LeanClosureObject<0> =
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
        m_fun: l_instMonadControlReaderT___lam__2___boxed as *const core::ffi::c_void,
        m_arity: 3,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_instMonadControlReaderT___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_instMonadControlReaderT___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_instMonadControlReaderT___closed__2_value: leanh::LeanCtorObject<2> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 0,
        },
        m_objs: [
            core::ptr::addr_of!(l_instMonadControlReaderT___closed__0_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_instMonadControlReaderT___closed__1_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_instMonadControlReaderT___closed__2: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_instMonadControlReaderT___closed__2_value)
        as *mut leanh::LeanObject;
pub static l_instMonadAttachReaderTOfMonad___redArg___closed__0_value:
    leanh::LeanClosureObject<0> = leanh::LeanClosureObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_instMonadAttachReaderTOfMonad___redArg___lam__0___boxed as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_instMonadAttachReaderTOfMonad___redArg___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_instMonadAttachReaderTOfMonad___redArg___closed__0_value)
        as *mut leanh::LeanObject;
pub unsafe fn l_ReaderT_orElse___redArg___lam__0(
    mut v_x_u2082_189_: *mut leanh::LeanObject,
    mut v_s_190_: *mut leanh::LeanObject,
    mut v_x_191_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_192_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_193_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_192_ = leanh::lean_box(0);
    leanh::lean_inc(v_s_190_);
    v___x_193_ = leanh::lean_apply_2(v_x_u2082_189_, v___x_192_, v_s_190_);
    return v___x_193_;
}
pub unsafe fn l_ReaderT_orElse___redArg___lam__0___boxed(
    mut v_x_u2082_194_: *mut leanh::LeanObject,
    mut v_s_195_: *mut leanh::LeanObject,
    mut v_x_196_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_197_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_197_ = l_ReaderT_orElse___redArg___lam__0(v_x_u2082_194_, v_s_195_, v_x_196_);
    leanh::lean_dec(v_s_195_);
    return v_res_197_;
}
pub unsafe fn l_ReaderT_orElse___redArg(
    mut v_inst_198_: *mut leanh::LeanObject,
    mut v_x_u2081_199_: *mut leanh::LeanObject,
    mut v_x_u2082_200_: *mut leanh::LeanObject,
    mut v_s_201_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_orElse_202_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_203_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_204_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_205_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_orElse_202_ = leanh::lean_ctor_get(v_inst_198_, 2);
    leanh::lean_inc(v_orElse_202_);
    leanh::lean_dec_ref(v_inst_198_);
    leanh::lean_inc_n(v_s_201_, 2);
    v___f_203_ = leanh::lean_alloc_closure(
        l_ReaderT_orElse___redArg___lam__0___boxed as *mut core::ffi::c_void,
        3,
        2,
    );
    leanh::lean_closure_set(v___f_203_, 0, v_x_u2082_200_);
    leanh::lean_closure_set(v___f_203_, 1, v_s_201_);
    v___x_204_ = leanh::lean_apply_1(v_x_u2081_199_, v_s_201_);
    v___x_205_ = leanh::lean_apply_3(
        v_orElse_202_,
        leanh::lean_box(0),
        v___x_204_,
        v___f_203_,
    );
    return v___x_205_;
}
pub unsafe fn l_ReaderT_orElse___redArg___boxed(
    mut v_inst_206_: *mut leanh::LeanObject,
    mut v_x_u2081_207_: *mut leanh::LeanObject,
    mut v_x_u2082_208_: *mut leanh::LeanObject,
    mut v_s_209_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_210_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_210_ = l_ReaderT_orElse___redArg(v_inst_206_, v_x_u2081_207_, v_x_u2082_208_, v_s_209_);
    leanh::lean_dec(v_s_209_);
    return v_res_210_;
}
pub unsafe fn l_ReaderT_orElse(
    mut v_m_211_: *mut leanh::LeanObject,
    mut v_00_u03c1_212_: *mut leanh::LeanObject,
    mut v_00_u03b1_213_: *mut leanh::LeanObject,
    mut v_inst_214_: *mut leanh::LeanObject,
    mut v_x_u2081_215_: *mut leanh::LeanObject,
    mut v_x_u2082_216_: *mut leanh::LeanObject,
    mut v_s_217_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_orElse_218_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_219_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_220_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_221_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_orElse_218_ = leanh::lean_ctor_get(v_inst_214_, 2);
    leanh::lean_inc(v_orElse_218_);
    leanh::lean_dec_ref(v_inst_214_);
    leanh::lean_inc_n(v_s_217_, 2);
    v___f_219_ = leanh::lean_alloc_closure(
        l_ReaderT_orElse___redArg___lam__0___boxed as *mut core::ffi::c_void,
        3,
        2,
    );
    leanh::lean_closure_set(v___f_219_, 0, v_x_u2082_216_);
    leanh::lean_closure_set(v___f_219_, 1, v_s_217_);
    v___x_220_ = leanh::lean_apply_1(v_x_u2081_215_, v_s_217_);
    v___x_221_ = leanh::lean_apply_3(
        v_orElse_218_,
        leanh::lean_box(0),
        v___x_220_,
        v___f_219_,
    );
    return v___x_221_;
}
pub unsafe fn l_ReaderT_orElse___boxed(
    mut v_m_222_: *mut leanh::LeanObject,
    mut v_00_u03c1_223_: *mut leanh::LeanObject,
    mut v_00_u03b1_224_: *mut leanh::LeanObject,
    mut v_inst_225_: *mut leanh::LeanObject,
    mut v_x_u2081_226_: *mut leanh::LeanObject,
    mut v_x_u2082_227_: *mut leanh::LeanObject,
    mut v_s_228_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_229_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_229_ = l_ReaderT_orElse(
        v_m_222_,
        v_00_u03c1_223_,
        v_00_u03b1_224_,
        v_inst_225_,
        v_x_u2081_226_,
        v_x_u2082_227_,
        v_s_228_,
    );
    leanh::lean_dec(v_s_228_);
    return v_res_229_;
}
pub unsafe fn l_ReaderT_failure___redArg(
    mut v_inst_230_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_failure_231_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_232_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_failure_231_ = leanh::lean_ctor_get(v_inst_230_, 1);
    leanh::lean_inc(v_failure_231_);
    leanh::lean_dec_ref(v_inst_230_);
    v___x_232_ = leanh::lean_apply_1(v_failure_231_, leanh::lean_box(0));
    return v___x_232_;
}
pub unsafe fn l_ReaderT_failure(
    mut v_m_233_: *mut leanh::LeanObject,
    mut v_00_u03c1_234_: *mut leanh::LeanObject,
    mut v_00_u03b1_235_: *mut leanh::LeanObject,
    mut v_inst_236_: *mut leanh::LeanObject,
    mut v_x_237_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_failure_238_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_239_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_failure_238_ = leanh::lean_ctor_get(v_inst_236_, 1);
    leanh::lean_inc(v_failure_238_);
    leanh::lean_dec_ref(v_inst_236_);
    v___x_239_ = leanh::lean_apply_1(v_failure_238_, leanh::lean_box(0));
    return v___x_239_;
}
pub unsafe fn l_ReaderT_failure___boxed(
    mut v_m_240_: *mut leanh::LeanObject,
    mut v_00_u03c1_241_: *mut leanh::LeanObject,
    mut v_00_u03b1_242_: *mut leanh::LeanObject,
    mut v_inst_243_: *mut leanh::LeanObject,
    mut v_x_244_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_245_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_245_ = l_ReaderT_failure(
        v_m_240_,
        v_00_u03c1_241_,
        v_00_u03b1_242_,
        v_inst_243_,
        v_x_244_,
    );
    leanh::lean_dec(v_x_244_);
    return v_res_245_;
}
pub unsafe fn l_ReaderT_instAlternativeOfMonad___redArg___lam__0(
    mut v_inst_246_: *mut leanh::LeanObject,
    mut v_00_u03b1_247_: *mut leanh::LeanObject,
    mut v___y_248_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_failure_249_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_250_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_failure_249_ = leanh::lean_ctor_get(v_inst_246_, 1);
    leanh::lean_inc(v_failure_249_);
    leanh::lean_dec_ref(v_inst_246_);
    v___x_250_ = leanh::lean_apply_1(v_failure_249_, leanh::lean_box(0));
    return v___x_250_;
}
pub unsafe fn l_ReaderT_instAlternativeOfMonad___redArg___lam__0___boxed(
    mut v_inst_251_: *mut leanh::LeanObject,
    mut v_00_u03b1_252_: *mut leanh::LeanObject,
    mut v___y_253_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_254_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_254_ = l_ReaderT_instAlternativeOfMonad___redArg___lam__0(
        v_inst_251_,
        v_00_u03b1_252_,
        v___y_253_,
    );
    leanh::lean_dec(v___y_253_);
    return v_res_254_;
}
pub unsafe fn l_ReaderT_instAlternativeOfMonad___redArg___lam__1(
    mut v___y_255_: *mut leanh::LeanObject,
    mut v___y_256_: *mut leanh::LeanObject,
    mut v_x_257_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_258_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_259_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_258_ = leanh::lean_box(0);
    leanh::lean_inc(v___y_256_);
    v___x_259_ = leanh::lean_apply_2(v___y_255_, v___x_258_, v___y_256_);
    return v___x_259_;
}
pub unsafe fn l_ReaderT_instAlternativeOfMonad___redArg___lam__1___boxed(
    mut v___y_260_: *mut leanh::LeanObject,
    mut v___y_261_: *mut leanh::LeanObject,
    mut v_x_262_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_263_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_263_ =
        l_ReaderT_instAlternativeOfMonad___redArg___lam__1(v___y_260_, v___y_261_, v_x_262_);
    leanh::lean_dec(v___y_261_);
    return v_res_263_;
}
pub unsafe fn l_ReaderT_instAlternativeOfMonad___redArg___lam__2(
    mut v_inst_264_: *mut leanh::LeanObject,
    mut v_00_u03b1_265_: *mut leanh::LeanObject,
    mut v___y_266_: *mut leanh::LeanObject,
    mut v___y_267_: *mut leanh::LeanObject,
    mut v___y_268_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_orElse_269_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_270_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_271_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_272_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_orElse_269_ = leanh::lean_ctor_get(v_inst_264_, 2);
    leanh::lean_inc(v_orElse_269_);
    leanh::lean_dec_ref(v_inst_264_);
    leanh::lean_inc_n(v___y_268_, 2);
    v___f_270_ = leanh::lean_alloc_closure(
        l_ReaderT_instAlternativeOfMonad___redArg___lam__1___boxed as *mut core::ffi::c_void,
        3,
        2,
    );
    leanh::lean_closure_set(v___f_270_, 0, v___y_267_);
    leanh::lean_closure_set(v___f_270_, 1, v___y_268_);
    v___x_271_ = leanh::lean_apply_1(v___y_266_, v___y_268_);
    v___x_272_ = leanh::lean_apply_3(
        v_orElse_269_,
        leanh::lean_box(0),
        v___x_271_,
        v___f_270_,
    );
    return v___x_272_;
}
pub unsafe fn l_ReaderT_instAlternativeOfMonad___redArg___lam__2___boxed(
    mut v_inst_273_: *mut leanh::LeanObject,
    mut v_00_u03b1_274_: *mut leanh::LeanObject,
    mut v___y_275_: *mut leanh::LeanObject,
    mut v___y_276_: *mut leanh::LeanObject,
    mut v___y_277_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_278_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_278_ = l_ReaderT_instAlternativeOfMonad___redArg___lam__2(
        v_inst_273_,
        v_00_u03b1_274_,
        v___y_275_,
        v___y_276_,
        v___y_277_,
    );
    leanh::lean_dec(v___y_277_);
    return v_res_278_;
}
pub unsafe fn l_ReaderT_instAlternativeOfMonad___redArg(
    mut v_inst_279_: *mut leanh::LeanObject,
    mut v_inst_280_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_toApplicative_281_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toFunctor_282_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeq_283_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeqLeft_284_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeqRight_285_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_287_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_288_: u8 = 0;
    let mut v___f_289_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_290_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_291_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_292_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_293_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_294_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_295_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_296_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_297_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_299_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_300_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_301_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_302_: u8 = 0;
    let mut v_unused_303_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_toApplicative_281_ = leanh::lean_ctor_get(v_inst_280_, 0);
                leanh::lean_inc_ref(v_toApplicative_281_);
                v_toFunctor_282_ = leanh::lean_ctor_get(v_toApplicative_281_, 0);
                v_toSeq_283_ = leanh::lean_ctor_get(v_toApplicative_281_, 2);
                v_toSeqLeft_284_ = leanh::lean_ctor_get(v_toApplicative_281_, 3);
                v_toSeqRight_285_ = leanh::lean_ctor_get(v_toApplicative_281_, 4);
                v_isSharedCheck_302_ =
                    (!leanh::lean_is_exclusive(v_toApplicative_281_)) as u8;
                if v_isSharedCheck_302_ == 0 {
                    v_unused_303_ = leanh::lean_ctor_get(v_toApplicative_281_, 1);
                    leanh::lean_dec(v_unused_303_);
                    v___x_287_ = v_toApplicative_281_;
                    v_isShared_288_ = v_isSharedCheck_302_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_toSeqRight_285_);
                    leanh::lean_inc(v_toSeqLeft_284_);
                    leanh::lean_inc(v_toSeq_283_);
                    leanh::lean_inc(v_toFunctor_282_);
                    leanh::lean_dec(v_toApplicative_281_);
                    v___x_287_ = leanh::lean_box(0);
                    v_isShared_288_ = v_isSharedCheck_302_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                leanh::lean_inc_ref(v_inst_279_);
                v___f_289_ = leanh::lean_alloc_closure(
                    l_ReaderT_instAlternativeOfMonad___redArg___lam__0___boxed
                        as *mut core::ffi::c_void,
                    3,
                    1,
                );
                leanh::lean_closure_set(v___f_289_, 0, v_inst_279_);
                v___f_290_ = leanh::lean_alloc_closure(
                    l_ReaderT_instAlternativeOfMonad___redArg___lam__2___boxed
                        as *mut core::ffi::c_void,
                    5,
                    1,
                );
                leanh::lean_closure_set(v___f_290_, 0, v_inst_279_);
                v___f_291_ = leanh::lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__1 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                leanh::lean_closure_set(v___f_291_, 0, v_toSeqRight_285_);
                v___f_292_ = leanh::lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__3 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                leanh::lean_closure_set(v___f_292_, 0, v_toSeqLeft_284_);
                v___f_293_ = leanh::lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__4 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                leanh::lean_closure_set(v___f_293_, 0, v_toSeq_283_);
                leanh::lean_inc_ref(v_toFunctor_282_);
                v___f_294_ = leanh::lean_alloc_closure(
                    l_ReaderT_instFunctorOfMonad___redArg___lam__0 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                leanh::lean_closure_set(v___f_294_, 0, v_toFunctor_282_);
                v___f_295_ = leanh::lean_alloc_closure(
                    l_ReaderT_instFunctorOfMonad___redArg___lam__1 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                leanh::lean_closure_set(v___f_295_, 0, v_toFunctor_282_);
                v___x_296_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_296_, 0, v___f_294_);
                leanh::lean_ctor_set(v___x_296_, 1, v___f_295_);
                v___x_297_ = leanh::lean_alloc_closure(
                    l_ReaderT_pure___boxed as *mut core::ffi::c_void,
                    6,
                    3,
                );
                leanh::lean_closure_set(v___x_297_, 0, leanh::lean_box(0));
                leanh::lean_closure_set(v___x_297_, 1, leanh::lean_box(0));
                leanh::lean_closure_set(v___x_297_, 2, v_inst_280_);
                if v_isShared_288_ == 0 {
                    leanh::lean_ctor_set(v___x_287_, 4, v___f_291_);
                    leanh::lean_ctor_set(v___x_287_, 3, v___f_292_);
                    leanh::lean_ctor_set(v___x_287_, 2, v___f_293_);
                    leanh::lean_ctor_set(v___x_287_, 1, v___x_297_);
                    leanh::lean_ctor_set(v___x_287_, 0, v___x_296_);
                    v___x_299_ = v___x_287_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_301_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_301_, 0, v___x_296_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_301_, 1, v___x_297_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_301_, 2, v___f_293_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_301_, 3, v___f_292_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_301_, 4, v___f_291_);
                    v___x_299_ = v_reuseFailAlloc_301_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_300_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
                leanh::lean_ctor_set(v___x_300_, 0, v___x_299_);
                leanh::lean_ctor_set(v___x_300_, 1, v___f_289_);
                leanh::lean_ctor_set(v___x_300_, 2, v___f_290_);
                return v___x_300_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_ReaderT_instAlternativeOfMonad(
    mut v_m_304_: *mut leanh::LeanObject,
    mut v_00_u03c1_305_: *mut leanh::LeanObject,
    mut v_inst_306_: *mut leanh::LeanObject,
    mut v_inst_307_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_308_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_308_ = l_ReaderT_instAlternativeOfMonad___redArg(v_inst_306_, v_inst_307_);
    return v___x_308_;
}
pub unsafe fn l_instMonadControlReaderT___lam__0(
    mut v_ctx_309_: *mut leanh::LeanObject,
    mut v_00_u03b2_310_: *mut leanh::LeanObject,
    mut v_x_311_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_312_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_312_ = leanh::lean_apply_1(v_x_311_, v_ctx_309_);
    return v___x_312_;
}
pub unsafe fn l_instMonadControlReaderT___lam__1(
    mut v_00_u03b1_313_: *mut leanh::LeanObject,
    mut v_f_314_: *mut leanh::LeanObject,
    mut v_ctx_315_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_316_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_317_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_316_ = leanh::lean_alloc_closure(
        l_instMonadControlReaderT___lam__0 as *mut core::ffi::c_void,
        3,
        1,
    );
    leanh::lean_closure_set(v___f_316_, 0, v_ctx_315_);
    v___x_317_ = leanh::lean_apply_1(v_f_314_, v___f_316_);
    return v___x_317_;
}
pub unsafe fn l_instMonadControlReaderT___lam__2(
    mut v_00_u03b1_318_: *mut leanh::LeanObject,
    mut v_x_319_: *mut leanh::LeanObject,
    mut v_x_320_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    leanh::lean_inc(v_x_319_);
    return v_x_319_;
}
pub unsafe fn l_instMonadControlReaderT___lam__2___boxed(
    mut v_00_u03b1_321_: *mut leanh::LeanObject,
    mut v_x_322_: *mut leanh::LeanObject,
    mut v_x_323_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_324_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_324_ = l_instMonadControlReaderT___lam__2(v_00_u03b1_321_, v_x_322_, v_x_323_);
    leanh::lean_dec(v_x_323_);
    leanh::lean_dec(v_x_322_);
    return v_res_324_;
}
pub unsafe fn l_instMonadControlReaderT(
    mut v_m_330_: *mut leanh::LeanObject,
    mut v_00_u03c1_331_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_332_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_332_ = l_instMonadControlReaderT___closed__2;
    return v___x_332_;
}
pub unsafe fn l_ReaderT_tryFinally___redArg___lam__0(
    mut v_h_333_: *mut leanh::LeanObject,
    mut v_ctx_334_: *mut leanh::LeanObject,
    mut v_a_x3f_335_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_336_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_336_ = leanh::lean_apply_2(v_h_333_, v_a_x3f_335_, v_ctx_334_);
    return v___x_336_;
}
pub unsafe fn l_ReaderT_tryFinally___redArg___lam__1(
    mut v_inst_337_: *mut leanh::LeanObject,
    mut v_00_u03b1_338_: *mut leanh::LeanObject,
    mut v_00_u03b2_339_: *mut leanh::LeanObject,
    mut v_x_340_: *mut leanh::LeanObject,
    mut v_h_341_: *mut leanh::LeanObject,
    mut v_ctx_342_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_343_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_344_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_345_: *mut leanh::LeanObject = core::ptr::null_mut();
    leanh::lean_inc(v_ctx_342_);
    v___f_343_ = leanh::lean_alloc_closure(
        l_ReaderT_tryFinally___redArg___lam__0 as *mut core::ffi::c_void,
        3,
        2,
    );
    leanh::lean_closure_set(v___f_343_, 0, v_h_341_);
    leanh::lean_closure_set(v___f_343_, 1, v_ctx_342_);
    v___x_344_ = leanh::lean_apply_1(v_x_340_, v_ctx_342_);
    v___x_345_ = leanh::lean_apply_4(
        v_inst_337_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v___x_344_,
        v___f_343_,
    );
    return v___x_345_;
}
pub unsafe fn l_ReaderT_tryFinally___redArg(
    mut v_inst_346_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_347_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_347_ = leanh::lean_alloc_closure(
        l_ReaderT_tryFinally___redArg___lam__1 as *mut core::ffi::c_void,
        6,
        1,
    );
    leanh::lean_closure_set(v___f_347_, 0, v_inst_346_);
    return v___f_347_;
}
pub unsafe fn l_ReaderT_tryFinally(
    mut v_m_348_: *mut leanh::LeanObject,
    mut v_00_u03c1_349_: *mut leanh::LeanObject,
    mut v_inst_350_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_351_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_351_ = leanh::lean_alloc_closure(
        l_ReaderT_tryFinally___redArg___lam__1 as *mut core::ffi::c_void,
        6,
        1,
    );
    leanh::lean_closure_set(v___f_351_, 0, v_inst_350_);
    return v___f_351_;
}
pub unsafe fn l_instMonadAttachReaderTOfMonad___redArg___lam__0(
    mut v_x_352_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    leanh::lean_inc(v_x_352_);
    return v_x_352_;
}
pub unsafe fn l_instMonadAttachReaderTOfMonad___redArg___lam__0___boxed(
    mut v_x_353_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_354_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_354_ = l_instMonadAttachReaderTOfMonad___redArg___lam__0(v_x_353_);
    leanh::lean_dec(v_x_353_);
    return v_res_354_;
}
pub unsafe fn l_instMonadAttachReaderTOfMonad___redArg___lam__1(
    mut v_toFunctor_355_: *mut leanh::LeanObject,
    mut v_inst_356_: *mut leanh::LeanObject,
    mut v___f_357_: *mut leanh::LeanObject,
    mut v_00_u03b1_358_: *mut leanh::LeanObject,
    mut v_x_359_: *mut leanh::LeanObject,
    mut v_r_360_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_map_361_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_362_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_363_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_364_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_map_361_ = leanh::lean_ctor_get(v_toFunctor_355_, 0);
    leanh::lean_inc(v_map_361_);
    leanh::lean_dec_ref(v_toFunctor_355_);
    v___x_362_ = leanh::lean_apply_1(v_x_359_, v_r_360_);
    v___x_363_ = leanh::lean_apply_2(v_inst_356_, leanh::lean_box(0), v___x_362_);
    v___x_364_ = leanh::lean_apply_4(
        v_map_361_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v___f_357_,
        v___x_363_,
    );
    return v___x_364_;
}
pub unsafe fn l_instMonadAttachReaderTOfMonad___redArg(
    mut v_inst_366_: *mut leanh::LeanObject,
    mut v_inst_367_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_toApplicative_368_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toFunctor_369_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_370_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_371_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_368_ = leanh::lean_ctor_get(v_inst_366_, 0);
    leanh::lean_inc_ref(v_toApplicative_368_);
    leanh::lean_dec_ref(v_inst_366_);
    v_toFunctor_369_ = leanh::lean_ctor_get(v_toApplicative_368_, 0);
    leanh::lean_inc_ref(v_toFunctor_369_);
    leanh::lean_dec_ref(v_toApplicative_368_);
    v___f_370_ = l_instMonadAttachReaderTOfMonad___redArg___closed__0;
    v___f_371_ = leanh::lean_alloc_closure(
        l_instMonadAttachReaderTOfMonad___redArg___lam__1 as *mut core::ffi::c_void,
        6,
        3,
    );
    leanh::lean_closure_set(v___f_371_, 0, v_toFunctor_369_);
    leanh::lean_closure_set(v___f_371_, 1, v_inst_367_);
    leanh::lean_closure_set(v___f_371_, 2, v___f_370_);
    return v___f_371_;
}
pub unsafe fn l_instMonadAttachReaderTOfMonad(
    mut v_m_372_: *mut leanh::LeanObject,
    mut v_00_u03c1_373_: *mut leanh::LeanObject,
    mut v_inst_374_: *mut leanh::LeanObject,
    mut v_inst_375_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_376_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_376_ = l_instMonadAttachReaderTOfMonad___redArg(v_inst_374_, v_inst_375_);
    return v___x_376_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Init_Control_Reader(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Init_Control_Except(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Init_Control_Reader(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_meta_initialized = true;
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Init_Control_Reader(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Init_Control_Except(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Control_Reader(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = meta_initialize_Init_Control_Reader(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return initialize_Init_Control_Reader(builtin);
}