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
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_alloc_closure, lean_alloc_ctor, lean_apply_1,
    lean_apply_2, lean_apply_3, lean_apply_4, lean_box, lean_closure_set, lean_ctor_get,
    lean_ctor_set, lean_dec, lean_dec_ref, lean_inc, lean_inc_n, lean_inc_ref,
    lean_io_result_is_error, lean_io_result_mk_ok, lean_is_exclusive,
};
pub static l_instMonadControlReaderT___closed__0_value: LeanClosureObject<0> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_instMonadControlReaderT___lam__1 as *const core::ffi::c_void,
    m_arity: 3,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_instMonadControlReaderT___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_instMonadControlReaderT___closed__0_value) as *mut LeanObject;
pub static l_instMonadControlReaderT___closed__1_value: LeanClosureObject<0> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_instMonadControlReaderT___lam__2___boxed as *const core::ffi::c_void,
    m_arity: 3,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_instMonadControlReaderT___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_instMonadControlReaderT___closed__1_value) as *mut LeanObject;
pub static l_instMonadControlReaderT___closed__2_value: LeanCtorObject<2> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 0,
    },
    m_objs: [
        core::ptr::addr_of!(l_instMonadControlReaderT___closed__0_value) as *mut LeanObject,
        core::ptr::addr_of!(l_instMonadControlReaderT___closed__1_value) as *mut LeanObject,
    ],
};
static mut l_instMonadControlReaderT___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_instMonadControlReaderT___closed__2_value) as *mut LeanObject;
pub static l_instMonadAttachReaderTOfMonad___redArg___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_instMonadAttachReaderTOfMonad___redArg___lam__0___boxed
            as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_instMonadAttachReaderTOfMonad___redArg___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_instMonadAttachReaderTOfMonad___redArg___closed__0_value)
        as *mut LeanObject;
pub unsafe fn l_ReaderT_orElse___redArg___lam__0(
    mut v_x_u2082_189_: *mut LeanObject,
    mut v_s_190_: *mut LeanObject,
    mut v_x_191_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_192_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_193_: *mut LeanObject = core::ptr::null_mut();
    v___x_192_ = lean_box(0);
    lean_inc(v_s_190_);
    v___x_193_ = lean_apply_2(v_x_u2082_189_, v___x_192_, v_s_190_);
    return v___x_193_;
}
pub unsafe fn l_ReaderT_orElse___redArg___lam__0___boxed(
    mut v_x_u2082_194_: *mut LeanObject,
    mut v_s_195_: *mut LeanObject,
    mut v_x_196_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_197_: *mut LeanObject = core::ptr::null_mut();
    v_res_197_ = l_ReaderT_orElse___redArg___lam__0(v_x_u2082_194_, v_s_195_, v_x_196_);
    lean_dec(v_s_195_);
    return v_res_197_;
}
pub unsafe fn l_ReaderT_orElse___redArg(
    mut v_inst_198_: *mut LeanObject,
    mut v_x_u2081_199_: *mut LeanObject,
    mut v_x_u2082_200_: *mut LeanObject,
    mut v_s_201_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_orElse_202_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_203_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_204_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_205_: *mut LeanObject = core::ptr::null_mut();
    v_orElse_202_ = lean_ctor_get(v_inst_198_, 2);
    lean_inc(v_orElse_202_);
    lean_dec_ref(v_inst_198_);
    lean_inc_n(v_s_201_, 2);
    v___f_203_ = lean_alloc_closure(
        l_ReaderT_orElse___redArg___lam__0___boxed as *mut core::ffi::c_void,
        3,
        2,
    );
    lean_closure_set(v___f_203_, 0, v_x_u2082_200_);
    lean_closure_set(v___f_203_, 1, v_s_201_);
    v___x_204_ = lean_apply_1(v_x_u2081_199_, v_s_201_);
    v___x_205_ = lean_apply_3(v_orElse_202_, lean_box(0), v___x_204_, v___f_203_);
    return v___x_205_;
}
pub unsafe fn l_ReaderT_orElse___redArg___boxed(
    mut v_inst_206_: *mut LeanObject,
    mut v_x_u2081_207_: *mut LeanObject,
    mut v_x_u2082_208_: *mut LeanObject,
    mut v_s_209_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_210_: *mut LeanObject = core::ptr::null_mut();
    v_res_210_ = l_ReaderT_orElse___redArg(v_inst_206_, v_x_u2081_207_, v_x_u2082_208_, v_s_209_);
    lean_dec(v_s_209_);
    return v_res_210_;
}
pub unsafe fn l_ReaderT_orElse(
    mut v_m_211_: *mut LeanObject,
    mut v_00_u03c1_212_: *mut LeanObject,
    mut v_00_u03b1_213_: *mut LeanObject,
    mut v_inst_214_: *mut LeanObject,
    mut v_x_u2081_215_: *mut LeanObject,
    mut v_x_u2082_216_: *mut LeanObject,
    mut v_s_217_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_orElse_218_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_219_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_220_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_221_: *mut LeanObject = core::ptr::null_mut();
    v_orElse_218_ = lean_ctor_get(v_inst_214_, 2);
    lean_inc(v_orElse_218_);
    lean_dec_ref(v_inst_214_);
    lean_inc_n(v_s_217_, 2);
    v___f_219_ = lean_alloc_closure(
        l_ReaderT_orElse___redArg___lam__0___boxed as *mut core::ffi::c_void,
        3,
        2,
    );
    lean_closure_set(v___f_219_, 0, v_x_u2082_216_);
    lean_closure_set(v___f_219_, 1, v_s_217_);
    v___x_220_ = lean_apply_1(v_x_u2081_215_, v_s_217_);
    v___x_221_ = lean_apply_3(v_orElse_218_, lean_box(0), v___x_220_, v___f_219_);
    return v___x_221_;
}
pub unsafe fn l_ReaderT_orElse___boxed(
    mut v_m_222_: *mut LeanObject,
    mut v_00_u03c1_223_: *mut LeanObject,
    mut v_00_u03b1_224_: *mut LeanObject,
    mut v_inst_225_: *mut LeanObject,
    mut v_x_u2081_226_: *mut LeanObject,
    mut v_x_u2082_227_: *mut LeanObject,
    mut v_s_228_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_229_: *mut LeanObject = core::ptr::null_mut();
    v_res_229_ = l_ReaderT_orElse(
        v_m_222_,
        v_00_u03c1_223_,
        v_00_u03b1_224_,
        v_inst_225_,
        v_x_u2081_226_,
        v_x_u2082_227_,
        v_s_228_,
    );
    lean_dec(v_s_228_);
    return v_res_229_;
}
pub unsafe fn l_ReaderT_failure___redArg(mut v_inst_230_: *mut LeanObject) -> *mut LeanObject {
    let mut v_failure_231_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_232_: *mut LeanObject = core::ptr::null_mut();
    v_failure_231_ = lean_ctor_get(v_inst_230_, 1);
    lean_inc(v_failure_231_);
    lean_dec_ref(v_inst_230_);
    v___x_232_ = lean_apply_1(v_failure_231_, lean_box(0));
    return v___x_232_;
}
pub unsafe fn l_ReaderT_failure(
    mut v_m_233_: *mut LeanObject,
    mut v_00_u03c1_234_: *mut LeanObject,
    mut v_00_u03b1_235_: *mut LeanObject,
    mut v_inst_236_: *mut LeanObject,
    mut v_x_237_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_failure_238_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_239_: *mut LeanObject = core::ptr::null_mut();
    v_failure_238_ = lean_ctor_get(v_inst_236_, 1);
    lean_inc(v_failure_238_);
    lean_dec_ref(v_inst_236_);
    v___x_239_ = lean_apply_1(v_failure_238_, lean_box(0));
    return v___x_239_;
}
pub unsafe fn l_ReaderT_failure___boxed(
    mut v_m_240_: *mut LeanObject,
    mut v_00_u03c1_241_: *mut LeanObject,
    mut v_00_u03b1_242_: *mut LeanObject,
    mut v_inst_243_: *mut LeanObject,
    mut v_x_244_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_245_: *mut LeanObject = core::ptr::null_mut();
    v_res_245_ = l_ReaderT_failure(
        v_m_240_,
        v_00_u03c1_241_,
        v_00_u03b1_242_,
        v_inst_243_,
        v_x_244_,
    );
    lean_dec(v_x_244_);
    return v_res_245_;
}
pub unsafe fn l_ReaderT_instAlternativeOfMonad___redArg___lam__0(
    mut v_inst_246_: *mut LeanObject,
    mut v_00_u03b1_247_: *mut LeanObject,
    mut v___y_248_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_failure_249_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_250_: *mut LeanObject = core::ptr::null_mut();
    v_failure_249_ = lean_ctor_get(v_inst_246_, 1);
    lean_inc(v_failure_249_);
    lean_dec_ref(v_inst_246_);
    v___x_250_ = lean_apply_1(v_failure_249_, lean_box(0));
    return v___x_250_;
}
pub unsafe fn l_ReaderT_instAlternativeOfMonad___redArg___lam__0___boxed(
    mut v_inst_251_: *mut LeanObject,
    mut v_00_u03b1_252_: *mut LeanObject,
    mut v___y_253_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_254_: *mut LeanObject = core::ptr::null_mut();
    v_res_254_ = l_ReaderT_instAlternativeOfMonad___redArg___lam__0(
        v_inst_251_,
        v_00_u03b1_252_,
        v___y_253_,
    );
    lean_dec(v___y_253_);
    return v_res_254_;
}
pub unsafe fn l_ReaderT_instAlternativeOfMonad___redArg___lam__1(
    mut v___y_255_: *mut LeanObject,
    mut v___y_256_: *mut LeanObject,
    mut v_x_257_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_258_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_259_: *mut LeanObject = core::ptr::null_mut();
    v___x_258_ = lean_box(0);
    lean_inc(v___y_256_);
    v___x_259_ = lean_apply_2(v___y_255_, v___x_258_, v___y_256_);
    return v___x_259_;
}
pub unsafe fn l_ReaderT_instAlternativeOfMonad___redArg___lam__1___boxed(
    mut v___y_260_: *mut LeanObject,
    mut v___y_261_: *mut LeanObject,
    mut v_x_262_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_263_: *mut LeanObject = core::ptr::null_mut();
    v_res_263_ =
        l_ReaderT_instAlternativeOfMonad___redArg___lam__1(v___y_260_, v___y_261_, v_x_262_);
    lean_dec(v___y_261_);
    return v_res_263_;
}
pub unsafe fn l_ReaderT_instAlternativeOfMonad___redArg___lam__2(
    mut v_inst_264_: *mut LeanObject,
    mut v_00_u03b1_265_: *mut LeanObject,
    mut v___y_266_: *mut LeanObject,
    mut v___y_267_: *mut LeanObject,
    mut v___y_268_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_orElse_269_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_270_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_271_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_272_: *mut LeanObject = core::ptr::null_mut();
    v_orElse_269_ = lean_ctor_get(v_inst_264_, 2);
    lean_inc(v_orElse_269_);
    lean_dec_ref(v_inst_264_);
    lean_inc_n(v___y_268_, 2);
    v___f_270_ = lean_alloc_closure(
        l_ReaderT_instAlternativeOfMonad___redArg___lam__1___boxed as *mut core::ffi::c_void,
        3,
        2,
    );
    lean_closure_set(v___f_270_, 0, v___y_267_);
    lean_closure_set(v___f_270_, 1, v___y_268_);
    v___x_271_ = lean_apply_1(v___y_266_, v___y_268_);
    v___x_272_ = lean_apply_3(v_orElse_269_, lean_box(0), v___x_271_, v___f_270_);
    return v___x_272_;
}
pub unsafe fn l_ReaderT_instAlternativeOfMonad___redArg___lam__2___boxed(
    mut v_inst_273_: *mut LeanObject,
    mut v_00_u03b1_274_: *mut LeanObject,
    mut v___y_275_: *mut LeanObject,
    mut v___y_276_: *mut LeanObject,
    mut v___y_277_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_278_: *mut LeanObject = core::ptr::null_mut();
    v_res_278_ = l_ReaderT_instAlternativeOfMonad___redArg___lam__2(
        v_inst_273_,
        v_00_u03b1_274_,
        v___y_275_,
        v___y_276_,
        v___y_277_,
    );
    lean_dec(v___y_277_);
    return v_res_278_;
}
pub unsafe fn l_ReaderT_instAlternativeOfMonad___redArg(
    mut v_inst_279_: *mut LeanObject,
    mut v_inst_280_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toApplicative_281_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toFunctor_282_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toSeq_283_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toSeqLeft_284_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toSeqRight_285_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_287_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_288_: u8 = 0;
    let mut v___f_289_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_290_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_291_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_292_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_293_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_294_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_295_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_296_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_297_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_299_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_300_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_301_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_302_: u8 = 0;
    let mut v_unused_303_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_toApplicative_281_ = lean_ctor_get(v_inst_280_, 0);
                lean_inc_ref(v_toApplicative_281_);
                v_toFunctor_282_ = lean_ctor_get(v_toApplicative_281_, 0);
                v_toSeq_283_ = lean_ctor_get(v_toApplicative_281_, 2);
                v_toSeqLeft_284_ = lean_ctor_get(v_toApplicative_281_, 3);
                v_toSeqRight_285_ = lean_ctor_get(v_toApplicative_281_, 4);
                v_isSharedCheck_302_ = (!lean_is_exclusive(v_toApplicative_281_)) as u8;
                if v_isSharedCheck_302_ == 0 {
                    v_unused_303_ = lean_ctor_get(v_toApplicative_281_, 1);
                    lean_dec(v_unused_303_);
                    v___x_287_ = v_toApplicative_281_;
                    v_isShared_288_ = v_isSharedCheck_302_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_toSeqRight_285_);
                    lean_inc(v_toSeqLeft_284_);
                    lean_inc(v_toSeq_283_);
                    lean_inc(v_toFunctor_282_);
                    lean_dec(v_toApplicative_281_);
                    v___x_287_ = lean_box(0);
                    v_isShared_288_ = v_isSharedCheck_302_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                lean_inc_ref(v_inst_279_);
                v___f_289_ = lean_alloc_closure(
                    l_ReaderT_instAlternativeOfMonad___redArg___lam__0___boxed
                        as *mut core::ffi::c_void,
                    3,
                    1,
                );
                lean_closure_set(v___f_289_, 0, v_inst_279_);
                v___f_290_ = lean_alloc_closure(
                    l_ReaderT_instAlternativeOfMonad___redArg___lam__2___boxed
                        as *mut core::ffi::c_void,
                    5,
                    1,
                );
                lean_closure_set(v___f_290_, 0, v_inst_279_);
                v___f_291_ = lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__1 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                lean_closure_set(v___f_291_, 0, v_toSeqRight_285_);
                v___f_292_ = lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__3 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                lean_closure_set(v___f_292_, 0, v_toSeqLeft_284_);
                v___f_293_ = lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__4 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                lean_closure_set(v___f_293_, 0, v_toSeq_283_);
                lean_inc_ref(v_toFunctor_282_);
                v___f_294_ = lean_alloc_closure(
                    l_ReaderT_instFunctorOfMonad___redArg___lam__0 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                lean_closure_set(v___f_294_, 0, v_toFunctor_282_);
                v___f_295_ = lean_alloc_closure(
                    l_ReaderT_instFunctorOfMonad___redArg___lam__1 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                lean_closure_set(v___f_295_, 0, v_toFunctor_282_);
                v___x_296_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_296_, 0, v___f_294_);
                lean_ctor_set(v___x_296_, 1, v___f_295_);
                v___x_297_ =
                    lean_alloc_closure(l_ReaderT_pure___boxed as *mut core::ffi::c_void, 6, 3);
                lean_closure_set(v___x_297_, 0, lean_box(0));
                lean_closure_set(v___x_297_, 1, lean_box(0));
                lean_closure_set(v___x_297_, 2, v_inst_280_);
                if v_isShared_288_ == 0 {
                    lean_ctor_set(v___x_287_, 4, v___f_291_);
                    lean_ctor_set(v___x_287_, 3, v___f_292_);
                    lean_ctor_set(v___x_287_, 2, v___f_293_);
                    lean_ctor_set(v___x_287_, 1, v___x_297_);
                    lean_ctor_set(v___x_287_, 0, v___x_296_);
                    v___x_299_ = v___x_287_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_301_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_301_, 0, v___x_296_);
                    lean_ctor_set(v_reuseFailAlloc_301_, 1, v___x_297_);
                    lean_ctor_set(v_reuseFailAlloc_301_, 2, v___f_293_);
                    lean_ctor_set(v_reuseFailAlloc_301_, 3, v___f_292_);
                    lean_ctor_set(v_reuseFailAlloc_301_, 4, v___f_291_);
                    v___x_299_ = v_reuseFailAlloc_301_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_300_ = lean_alloc_ctor(0, 3, (0) as u32);
                lean_ctor_set(v___x_300_, 0, v___x_299_);
                lean_ctor_set(v___x_300_, 1, v___f_289_);
                lean_ctor_set(v___x_300_, 2, v___f_290_);
                return v___x_300_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_ReaderT_instAlternativeOfMonad(
    mut v_m_304_: *mut LeanObject,
    mut v_00_u03c1_305_: *mut LeanObject,
    mut v_inst_306_: *mut LeanObject,
    mut v_inst_307_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_308_: *mut LeanObject = core::ptr::null_mut();
    v___x_308_ = l_ReaderT_instAlternativeOfMonad___redArg(v_inst_306_, v_inst_307_);
    return v___x_308_;
}
pub unsafe fn l_instMonadControlReaderT___lam__0(
    mut v_ctx_309_: *mut LeanObject,
    mut v_00_u03b2_310_: *mut LeanObject,
    mut v_x_311_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_312_: *mut LeanObject = core::ptr::null_mut();
    v___x_312_ = lean_apply_1(v_x_311_, v_ctx_309_);
    return v___x_312_;
}
pub unsafe fn l_instMonadControlReaderT___lam__1(
    mut v_00_u03b1_313_: *mut LeanObject,
    mut v_f_314_: *mut LeanObject,
    mut v_ctx_315_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_316_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_317_: *mut LeanObject = core::ptr::null_mut();
    v___f_316_ = lean_alloc_closure(
        l_instMonadControlReaderT___lam__0 as *mut core::ffi::c_void,
        3,
        1,
    );
    lean_closure_set(v___f_316_, 0, v_ctx_315_);
    v___x_317_ = lean_apply_1(v_f_314_, v___f_316_);
    return v___x_317_;
}
pub unsafe fn l_instMonadControlReaderT___lam__2(
    mut v_00_u03b1_318_: *mut LeanObject,
    mut v_x_319_: *mut LeanObject,
    mut v_x_320_: *mut LeanObject,
) -> *mut LeanObject {
    lean_inc(v_x_319_);
    return v_x_319_;
}
pub unsafe fn l_instMonadControlReaderT___lam__2___boxed(
    mut v_00_u03b1_321_: *mut LeanObject,
    mut v_x_322_: *mut LeanObject,
    mut v_x_323_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_324_: *mut LeanObject = core::ptr::null_mut();
    v_res_324_ = l_instMonadControlReaderT___lam__2(v_00_u03b1_321_, v_x_322_, v_x_323_);
    lean_dec(v_x_323_);
    lean_dec(v_x_322_);
    return v_res_324_;
}
pub unsafe fn l_instMonadControlReaderT(
    mut v_m_330_: *mut LeanObject,
    mut v_00_u03c1_331_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_332_: *mut LeanObject = core::ptr::null_mut();
    v___x_332_ = l_instMonadControlReaderT___closed__2;
    return v___x_332_;
}
pub unsafe fn l_ReaderT_tryFinally___redArg___lam__0(
    mut v_h_333_: *mut LeanObject,
    mut v_ctx_334_: *mut LeanObject,
    mut v_a_x3f_335_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_336_: *mut LeanObject = core::ptr::null_mut();
    v___x_336_ = lean_apply_2(v_h_333_, v_a_x3f_335_, v_ctx_334_);
    return v___x_336_;
}
pub unsafe fn l_ReaderT_tryFinally___redArg___lam__1(
    mut v_inst_337_: *mut LeanObject,
    mut v_00_u03b1_338_: *mut LeanObject,
    mut v_00_u03b2_339_: *mut LeanObject,
    mut v_x_340_: *mut LeanObject,
    mut v_h_341_: *mut LeanObject,
    mut v_ctx_342_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_343_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_344_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_345_: *mut LeanObject = core::ptr::null_mut();
    lean_inc(v_ctx_342_);
    v___f_343_ = lean_alloc_closure(
        l_ReaderT_tryFinally___redArg___lam__0 as *mut core::ffi::c_void,
        3,
        2,
    );
    lean_closure_set(v___f_343_, 0, v_h_341_);
    lean_closure_set(v___f_343_, 1, v_ctx_342_);
    v___x_344_ = lean_apply_1(v_x_340_, v_ctx_342_);
    v___x_345_ = lean_apply_4(
        v_inst_337_,
        lean_box(0),
        lean_box(0),
        v___x_344_,
        v___f_343_,
    );
    return v___x_345_;
}
pub unsafe fn l_ReaderT_tryFinally___redArg(mut v_inst_346_: *mut LeanObject) -> *mut LeanObject {
    let mut v___f_347_: *mut LeanObject = core::ptr::null_mut();
    v___f_347_ = lean_alloc_closure(
        l_ReaderT_tryFinally___redArg___lam__1 as *mut core::ffi::c_void,
        6,
        1,
    );
    lean_closure_set(v___f_347_, 0, v_inst_346_);
    return v___f_347_;
}
pub unsafe fn l_ReaderT_tryFinally(
    mut v_m_348_: *mut LeanObject,
    mut v_00_u03c1_349_: *mut LeanObject,
    mut v_inst_350_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_351_: *mut LeanObject = core::ptr::null_mut();
    v___f_351_ = lean_alloc_closure(
        l_ReaderT_tryFinally___redArg___lam__1 as *mut core::ffi::c_void,
        6,
        1,
    );
    lean_closure_set(v___f_351_, 0, v_inst_350_);
    return v___f_351_;
}
pub unsafe fn l_instMonadAttachReaderTOfMonad___redArg___lam__0(
    mut v_x_352_: *mut LeanObject,
) -> *mut LeanObject {
    lean_inc(v_x_352_);
    return v_x_352_;
}
pub unsafe fn l_instMonadAttachReaderTOfMonad___redArg___lam__0___boxed(
    mut v_x_353_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_354_: *mut LeanObject = core::ptr::null_mut();
    v_res_354_ = l_instMonadAttachReaderTOfMonad___redArg___lam__0(v_x_353_);
    lean_dec(v_x_353_);
    return v_res_354_;
}
pub unsafe fn l_instMonadAttachReaderTOfMonad___redArg___lam__1(
    mut v_toFunctor_355_: *mut LeanObject,
    mut v_inst_356_: *mut LeanObject,
    mut v___f_357_: *mut LeanObject,
    mut v_00_u03b1_358_: *mut LeanObject,
    mut v_x_359_: *mut LeanObject,
    mut v_r_360_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_map_361_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_362_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_363_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_364_: *mut LeanObject = core::ptr::null_mut();
    v_map_361_ = lean_ctor_get(v_toFunctor_355_, 0);
    lean_inc(v_map_361_);
    lean_dec_ref(v_toFunctor_355_);
    v___x_362_ = lean_apply_1(v_x_359_, v_r_360_);
    v___x_363_ = lean_apply_2(v_inst_356_, lean_box(0), v___x_362_);
    v___x_364_ = lean_apply_4(v_map_361_, lean_box(0), lean_box(0), v___f_357_, v___x_363_);
    return v___x_364_;
}
pub unsafe fn l_instMonadAttachReaderTOfMonad___redArg(
    mut v_inst_366_: *mut LeanObject,
    mut v_inst_367_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toApplicative_368_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toFunctor_369_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_370_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_371_: *mut LeanObject = core::ptr::null_mut();
    v_toApplicative_368_ = lean_ctor_get(v_inst_366_, 0);
    lean_inc_ref(v_toApplicative_368_);
    lean_dec_ref(v_inst_366_);
    v_toFunctor_369_ = lean_ctor_get(v_toApplicative_368_, 0);
    lean_inc_ref(v_toFunctor_369_);
    lean_dec_ref(v_toApplicative_368_);
    v___f_370_ = l_instMonadAttachReaderTOfMonad___redArg___closed__0;
    v___f_371_ = lean_alloc_closure(
        l_instMonadAttachReaderTOfMonad___redArg___lam__1 as *mut core::ffi::c_void,
        6,
        3,
    );
    lean_closure_set(v___f_371_, 0, v_toFunctor_369_);
    lean_closure_set(v___f_371_, 1, v_inst_367_);
    lean_closure_set(v___f_371_, 2, v___f_370_);
    return v___f_371_;
}
pub unsafe fn l_instMonadAttachReaderTOfMonad(
    mut v_m_372_: *mut LeanObject,
    mut v_00_u03c1_373_: *mut LeanObject,
    mut v_inst_374_: *mut LeanObject,
    mut v_inst_375_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_376_: *mut LeanObject = core::ptr::null_mut();
    v___x_376_ = l_instMonadAttachReaderTOfMonad___redArg(v_inst_374_, v_inst_375_);
    return v___x_376_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Init_Control_Reader(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Init_Control_Except(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Init_Control_Reader(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_meta_initialized = true;
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Init_Control_Reader(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Init_Control_Except(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Control_Reader(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Init_Control_Reader(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Init_Control_Reader(builtin);
}
