// Lean compiler output
// Module: Lean.Elab.Deriving.SizeOf
// Imports: Lean.Meta.SizeOf Lean.Elab.Deriving.Basic Lean.Elab.Deriving.Util
use crate::ffi::{
    lean_array_get_size, lean_array_size, lean_array_uget_borrowed, lean_nat_dec_lt,
    lean_st_ref_get, lean_usize_add, lean_usize_dec_eq, lean_usize_dec_lt, lean_usize_of_nat,
};
use crate::r#gen::Lean::Elab::Command::l_Lean_Elab_Command_liftTermElabM___boxed;
use crate::r#gen::Lean::Elab::Deriving::Basic::{
    initialize_Lean_Elab_Deriving_Basic, l_Lean_Elab_registerDerivingHandler,
    runtime_initialize_Lean_Elab_Deriving_Basic,
};
use crate::r#gen::Lean::Elab::Deriving::Util::{
    initialize_Lean_Elab_Deriving_Util, l_Lean_Elab_Deriving_withoutExposeFromCtors___redArg,
    runtime_initialize_Lean_Elab_Deriving_Util,
};
use crate::r#gen::Lean::Meta::SizeOf::{
    initialize_Lean_Meta_SizeOf, l_Lean_Meta_mkSizeOfInstances, runtime_initialize_Lean_Meta_SizeOf,
};
use crate::r#gen::Lean::MonadEnv::l_Lean_isInductiveCore;
pub static l___private_Lean_Elab_Deriving_SizeOf_0__Lean_Elab_Deriving_SizeOf_initFn___closed__0_00___x40_Lean_Elab_Deriving_SizeOf_388027031____hygCtx___hyg_2__value: crate::leanh::LeanStringObject<7> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [83, 105, 122, 101, 79, 102, 0]};
static mut l___private_Lean_Elab_Deriving_SizeOf_0__Lean_Elab_Deriving_SizeOf_initFn___closed__0_00___x40_Lean_Elab_Deriving_SizeOf_388027031____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Deriving_SizeOf_0__Lean_Elab_Deriving_SizeOf_initFn___closed__0_00___x40_Lean_Elab_Deriving_SizeOf_388027031____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Deriving_SizeOf_0__Lean_Elab_Deriving_SizeOf_initFn___closed__1_00___x40_Lean_Elab_Deriving_SizeOf_388027031____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Deriving_SizeOf_0__Lean_Elab_Deriving_SizeOf_initFn___closed__0_00___x40_Lean_Elab_Deriving_SizeOf_388027031____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,14284789806808743489 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_Deriving_SizeOf_0__Lean_Elab_Deriving_SizeOf_initFn___closed__1_00___x40_Lean_Elab_Deriving_SizeOf_388027031____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Deriving_SizeOf_0__Lean_Elab_Deriving_SizeOf_initFn___closed__1_00___x40_Lean_Elab_Deriving_SizeOf_388027031____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Deriving_SizeOf_0__Lean_Elab_Deriving_SizeOf_initFn___closed__2_00___x40_Lean_Elab_Deriving_SizeOf_388027031____hygCtx___hyg_2__value: crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_Elab_Deriving_SizeOf_mkSizeOfHandler___boxed as *const core::ffi::c_void, m_arity: 4, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_Elab_Deriving_SizeOf_0__Lean_Elab_Deriving_SizeOf_initFn___closed__2_00___x40_Lean_Elab_Deriving_SizeOf_388027031____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Deriving_SizeOf_0__Lean_Elab_Deriving_SizeOf_initFn___closed__2_00___x40_Lean_Elab_Deriving_SizeOf_388027031____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub unsafe fn l_Lean_isInductive___at___00Lean_Elab_Deriving_SizeOf_mkSizeOfHandler_spec__1___redArg(
    mut v_declName_181_: *mut crate::leanh::LeanObject,
    mut v___y_182_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_184_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_185_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_186_: u8 = 0;
    let mut v___x_187_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_188_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_184_ = lean_st_ref_get(v___y_182_);
    v_env_185_ = crate::leanh::lean_ctor_get(v___x_184_, 0);
    crate::leanh::lean_inc_ref(v_env_185_);
    crate::leanh::lean_dec(v___x_184_);
    v___x_186_ = l_Lean_isInductiveCore(v_env_185_, v_declName_181_);
    v___x_187_ = crate::leanh::lean_box((v___x_186_) as usize);
    v___x_188_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_188_, 0, v___x_187_);
    return v___x_188_;
}
pub unsafe fn l_Lean_isInductive___at___00Lean_Elab_Deriving_SizeOf_mkSizeOfHandler_spec__1___redArg___boxed(
    mut v_declName_189_: *mut crate::leanh::LeanObject,
    mut v___y_190_: *mut crate::leanh::LeanObject,
    mut v___y_191_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_192_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_192_ =
        l_Lean_isInductive___at___00Lean_Elab_Deriving_SizeOf_mkSizeOfHandler_spec__1___redArg(
            v_declName_189_,
            v___y_190_,
        );
    crate::leanh::lean_dec(v___y_190_);
    return v_res_192_;
}
pub unsafe fn l_Lean_isInductive___at___00Lean_Elab_Deriving_SizeOf_mkSizeOfHandler_spec__1(
    mut v_declName_193_: *mut crate::leanh::LeanObject,
    mut v___y_194_: *mut crate::leanh::LeanObject,
    mut v___y_195_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_197_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_197_ =
        l_Lean_isInductive___at___00Lean_Elab_Deriving_SizeOf_mkSizeOfHandler_spec__1___redArg(
            v_declName_193_,
            v___y_195_,
        );
    return v___x_197_;
}
pub unsafe fn l_Lean_isInductive___at___00Lean_Elab_Deriving_SizeOf_mkSizeOfHandler_spec__1___boxed(
    mut v_declName_198_: *mut crate::leanh::LeanObject,
    mut v___y_199_: *mut crate::leanh::LeanObject,
    mut v___y_200_: *mut crate::leanh::LeanObject,
    mut v___y_201_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_202_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_202_ = l_Lean_isInductive___at___00Lean_Elab_Deriving_SizeOf_mkSizeOfHandler_spec__1(
        v_declName_198_,
        v___y_199_,
        v___y_200_,
    );
    crate::leanh::lean_dec(v___y_200_);
    crate::leanh::lean_dec_ref(v___y_199_);
    return v_res_202_;
}
pub unsafe fn l_Lean_Elab_Deriving_SizeOf_mkSizeOfHandler___lam__0(
    mut v_____do__lift_203_: u8,
    mut v___y_204_: *mut crate::leanh::LeanObject,
    mut v___y_205_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if v_____do__lift_203_ == 0 {
        let mut v___x_207_: u8 = 0;
        let mut v___x_208_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_209_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_207_ = 1;
        v___x_208_ = crate::leanh::lean_box((v___x_207_) as usize);
        v___x_209_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_209_, 0, v___x_208_);
        return v___x_209_;
    } else {
        let mut v___x_210_: u8 = 0;
        let mut v___x_211_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_212_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_210_ = 0;
        v___x_211_ = crate::leanh::lean_box((v___x_210_) as usize);
        v___x_212_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_212_, 0, v___x_211_);
        return v___x_212_;
    }
}
pub unsafe fn l_Lean_Elab_Deriving_SizeOf_mkSizeOfHandler___lam__0___boxed(
    mut v_____do__lift_213_: *mut crate::leanh::LeanObject,
    mut v___y_214_: *mut crate::leanh::LeanObject,
    mut v___y_215_: *mut crate::leanh::LeanObject,
    mut v___y_216_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_____do__lift_1887__boxed_217_: u8 = 0;
    let mut v_res_218_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_____do__lift_1887__boxed_217_ = (crate::leanh::lean_unbox(v_____do__lift_213_) as u8);
    v_res_218_ = l_Lean_Elab_Deriving_SizeOf_mkSizeOfHandler___lam__0(
        v_____do__lift_1887__boxed_217_,
        v___y_214_,
        v___y_215_,
    );
    crate::leanh::lean_dec(v___y_215_);
    crate::leanh::lean_dec_ref(v___y_214_);
    return v_res_218_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_Deriving_SizeOf_mkSizeOfHandler_spec__2(
    mut v_as_219_: *mut crate::leanh::LeanObject,
    mut v_i_220_: usize,
    mut v_stop_221_: usize,
    mut v___y_222_: *mut crate::leanh::LeanObject,
    mut v___y_223_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_225_: u8 = 0;
    let mut v___x_226_: u8 = 0;
    let mut v_a_228_: u8 = 0;
    let mut v___x_229_: usize = 0;
    let mut v___x_230_: usize = 0;
    let mut v___x_232_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_233_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_234_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_235_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_236_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_238_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_239_: u8 = 0;
    let mut v___x_240_: u8 = 0;
    let mut v___x_241_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_243_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_244_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_245_: u8 = 0;
    let mut v_a_246_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_247_: u8 = 0;
    let mut v___x_248_: u8 = 0;
    let mut v___x_249_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_250_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_225_ = lean_usize_dec_eq(v_i_220_, v_stop_221_);
                if v___x_225_ == 0 {
                    v___x_226_ = 1;
                    v___x_234_ = lean_array_uget_borrowed(v_as_219_, v_i_220_);
                    crate::leanh::lean_inc(v___x_234_);
                    v___x_235_ = l_Lean_isInductive___at___00Lean_Elab_Deriving_SizeOf_mkSizeOfHandler_spec__1___redArg(v___x_234_, v___y_223_);
                    if crate::leanh::lean_obj_tag(v___x_235_) == 0 {
                        v_a_236_ = crate::leanh::lean_ctor_get(v___x_235_, 0);
                        v_isSharedCheck_245_ = (!crate::leanh::lean_is_exclusive(v___x_235_)) as u8;
                        if v_isSharedCheck_245_ == 0 {
                            v___x_238_ = v___x_235_;
                            v_isShared_239_ = v_isSharedCheck_245_;
                            state = 2;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_236_);
                            crate::leanh::lean_dec(v___x_235_);
                            v___x_238_ = crate::leanh::lean_box(0);
                            v_isShared_239_ = v_isSharedCheck_245_;
                            state = 2;
                            continue;
                        }
                    } else {
                        if crate::leanh::lean_obj_tag(v___x_235_) == 0 {
                            v_a_246_ = crate::leanh::lean_ctor_get(v___x_235_, 0);
                            crate::leanh::lean_inc(v_a_246_);
                            crate::leanh::lean_dec_ref_known(v___x_235_, 1);
                            v___x_247_ = (crate::leanh::lean_unbox(v_a_246_) as u8);
                            crate::leanh::lean_dec(v_a_246_);
                            v_a_228_ = v___x_247_;
                            state = 1;
                            continue;
                        } else {
                            return v___x_235_;
                        }
                    }
                } else {
                    v___x_248_ = 0;
                    v___x_249_ = crate::leanh::lean_box((v___x_248_) as usize);
                    v___x_250_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_250_, 0, v___x_249_);
                    return v___x_250_;
                }
            }
            1 => {
                if v_a_228_ == 0 {
                    v___x_229_ = 1usize;
                    v___x_230_ = lean_usize_add(v_i_220_, v___x_229_);
                    v_i_220_ = v___x_230_;
                    state = 0;
                    continue;
                } else {
                    v___x_232_ = crate::leanh::lean_box((v___x_226_) as usize);
                    v___x_233_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_233_, 0, v___x_232_);
                    return v___x_233_;
                }
            }
            2 => {
                v___x_240_ = (crate::leanh::lean_unbox(v_a_236_) as u8);
                crate::leanh::lean_dec(v_a_236_);
                if v___x_240_ == 0 {
                    v___x_241_ = crate::leanh::lean_box((v___x_226_) as usize);
                    if v_isShared_239_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_238_, 0, v___x_241_);
                        v___x_243_ = v___x_238_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_244_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_244_, 0, v___x_241_);
                        v___x_243_ = v_reuseFailAlloc_244_;
                        state = 3;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_238_);
                    v_a_228_ = v___x_225_;
                    state = 1;
                    continue;
                }
            }
            3 => {
                return v___x_243_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_Deriving_SizeOf_mkSizeOfHandler_spec__2___boxed(
    mut v_as_251_: *mut crate::leanh::LeanObject,
    mut v_i_252_: *mut crate::leanh::LeanObject,
    mut v_stop_253_: *mut crate::leanh::LeanObject,
    mut v___y_254_: *mut crate::leanh::LeanObject,
    mut v___y_255_: *mut crate::leanh::LeanObject,
    mut v___y_256_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_i_boxed_257_: usize = 0;
    let mut v_stop_boxed_258_: usize = 0;
    let mut v_res_259_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_257_ = crate::leanh::lean_unbox_usize(v_i_252_);
    crate::leanh::lean_dec(v_i_252_);
    v_stop_boxed_258_ = crate::leanh::lean_unbox_usize(v_stop_253_);
    crate::leanh::lean_dec(v_stop_253_);
    v_res_259_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_Deriving_SizeOf_mkSizeOfHandler_spec__2(v_as_251_, v_i_boxed_257_, v_stop_boxed_258_, v___y_254_, v___y_255_);
    crate::leanh::lean_dec(v___y_255_);
    crate::leanh::lean_dec_ref(v___y_254_);
    crate::leanh::lean_dec_ref(v_as_251_);
    return v_res_259_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Deriving_SizeOf_mkSizeOfHandler_spec__0___lam__0(
    mut v_a_260_: *mut crate::leanh::LeanObject,
    mut v___y_261_: *mut crate::leanh::LeanObject,
    mut v___y_262_: *mut crate::leanh::LeanObject,
    mut v___y_263_: *mut crate::leanh::LeanObject,
    mut v___y_264_: *mut crate::leanh::LeanObject,
    mut v___y_265_: *mut crate::leanh::LeanObject,
    mut v___y_266_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_268_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_268_ =
        l_Lean_Meta_mkSizeOfInstances(v_a_260_, v___y_263_, v___y_264_, v___y_265_, v___y_266_);
    return v___x_268_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Deriving_SizeOf_mkSizeOfHandler_spec__0___lam__0___boxed(
    mut v_a_269_: *mut crate::leanh::LeanObject,
    mut v___y_270_: *mut crate::leanh::LeanObject,
    mut v___y_271_: *mut crate::leanh::LeanObject,
    mut v___y_272_: *mut crate::leanh::LeanObject,
    mut v___y_273_: *mut crate::leanh::LeanObject,
    mut v___y_274_: *mut crate::leanh::LeanObject,
    mut v___y_275_: *mut crate::leanh::LeanObject,
    mut v___y_276_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_277_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_277_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Deriving_SizeOf_mkSizeOfHandler_spec__0___lam__0(v_a_269_, v___y_270_, v___y_271_, v___y_272_, v___y_273_, v___y_274_, v___y_275_);
    crate::leanh::lean_dec(v___y_275_);
    crate::leanh::lean_dec_ref(v___y_274_);
    crate::leanh::lean_dec(v___y_273_);
    crate::leanh::lean_dec_ref(v___y_272_);
    crate::leanh::lean_dec(v___y_271_);
    crate::leanh::lean_dec_ref(v___y_270_);
    return v_res_277_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Deriving_SizeOf_mkSizeOfHandler_spec__0(
    mut v_as_278_: *mut crate::leanh::LeanObject,
    mut v_sz_279_: usize,
    mut v_i_280_: usize,
    mut v_b_281_: *mut crate::leanh::LeanObject,
    mut v___y_282_: *mut crate::leanh::LeanObject,
    mut v___y_283_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_285_: u8 = 0;
    let mut v___x_286_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_287_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_288_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_289_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_290_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_291_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_292_: usize = 0;
    let mut v___x_293_: usize = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_285_ = lean_usize_dec_lt(v_i_280_, v_sz_279_);
                if v___x_285_ == 0 {
                    v___x_286_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_286_, 0, v_b_281_);
                    return v___x_286_;
                } else {
                    v_a_287_ = lean_array_uget_borrowed(v_as_278_, v_i_280_);
                    crate::leanh::lean_inc_n(v_a_287_, 2);
                    v___f_288_ = crate::leanh::lean_alloc_closure(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Deriving_SizeOf_mkSizeOfHandler_spec__0___lam__0___boxed as *mut core::ffi::c_void, 8, 1);
                    crate::leanh::lean_closure_set(v___f_288_, 0, v_a_287_);
                    v___x_289_ = crate::leanh::lean_alloc_closure(
                        l_Lean_Elab_Command_liftTermElabM___boxed as *mut core::ffi::c_void,
                        5,
                        2,
                    );
                    crate::leanh::lean_closure_set(v___x_289_, 0, crate::leanh::lean_box(0));
                    crate::leanh::lean_closure_set(v___x_289_, 1, v___f_288_);
                    v___x_290_ = l_Lean_Elab_Deriving_withoutExposeFromCtors___redArg(
                        v_a_287_, v___x_289_, v___y_282_, v___y_283_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_290_) == 0 {
                        crate::leanh::lean_dec_ref_known(v___x_290_, 1);
                        v___x_291_ = crate::leanh::lean_box(0);
                        v___x_292_ = 1usize;
                        v___x_293_ = lean_usize_add(v_i_280_, v___x_292_);
                        v_i_280_ = v___x_293_;
                        v_b_281_ = v___x_291_;
                        state = 0;
                        continue;
                    } else {
                        return v___x_290_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Deriving_SizeOf_mkSizeOfHandler_spec__0___boxed(
    mut v_as_295_: *mut crate::leanh::LeanObject,
    mut v_sz_296_: *mut crate::leanh::LeanObject,
    mut v_i_297_: *mut crate::leanh::LeanObject,
    mut v_b_298_: *mut crate::leanh::LeanObject,
    mut v___y_299_: *mut crate::leanh::LeanObject,
    mut v___y_300_: *mut crate::leanh::LeanObject,
    mut v___y_301_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_sz_boxed_302_: usize = 0;
    let mut v_i_boxed_303_: usize = 0;
    let mut v_res_304_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_302_ = crate::leanh::lean_unbox_usize(v_sz_296_);
    crate::leanh::lean_dec(v_sz_296_);
    v_i_boxed_303_ = crate::leanh::lean_unbox_usize(v_i_297_);
    crate::leanh::lean_dec(v_i_297_);
    v_res_304_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Deriving_SizeOf_mkSizeOfHandler_spec__0(v_as_295_, v_sz_boxed_302_, v_i_boxed_303_, v_b_298_, v___y_299_, v___y_300_);
    crate::leanh::lean_dec(v___y_300_);
    crate::leanh::lean_dec_ref(v___y_299_);
    crate::leanh::lean_dec_ref(v_as_295_);
    return v_res_304_;
}
pub unsafe fn l_Lean_Elab_Deriving_SizeOf_mkSizeOfHandler(
    mut v_declNames_305_: *mut crate::leanh::LeanObject,
    mut v_a_306_: *mut crate::leanh::LeanObject,
    mut v_a_307_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_310_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_311_: usize = 0;
    let mut v___x_312_: usize = 0;
    let mut v___x_313_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_315_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_316_: u8 = 0;
    let mut v___x_317_: u8 = 0;
    let mut v___x_318_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_320_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_321_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_322_: u8 = 0;
    let mut v_unused_323_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_324_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_326_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_327_: u8 = 0;
    let mut v___x_329_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_330_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_331_: u8 = 0;
    let mut v___y_333_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_334_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_335_: u8 = 0;
    let mut v___x_336_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_337_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_338_: u8 = 0;
    let mut v___x_339_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_340_: usize = 0;
    let mut v___x_341_: usize = 0;
    let mut v___x_342_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_343_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_344_: u8 = 0;
    let mut v___x_345_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_336_ = crate::leanh::lean_unsigned_to_nat(0);
                v___x_337_ = lean_array_get_size(v_declNames_305_);
                v___x_338_ = lean_nat_dec_lt(v___x_336_, v___x_337_);
                if v___x_338_ == 0 {
                    v___x_339_ = l_Lean_Elab_Deriving_SizeOf_mkSizeOfHandler___lam__0(
                        v___x_338_, v_a_306_, v_a_307_,
                    );
                    v___y_333_ = v___x_339_;
                    state = 6;
                    continue;
                } else {
                    if v___x_338_ == 0 {
                        state = 1;
                        continue;
                    } else {
                        v___x_340_ = 0usize;
                        v___x_341_ = lean_usize_of_nat(v___x_337_);
                        v___x_342_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_Deriving_SizeOf_mkSizeOfHandler_spec__2(v_declNames_305_, v___x_340_, v___x_341_, v_a_306_, v_a_307_);
                        if crate::leanh::lean_obj_tag(v___x_342_) == 0 {
                            v_a_343_ = crate::leanh::lean_ctor_get(v___x_342_, 0);
                            crate::leanh::lean_inc(v_a_343_);
                            crate::leanh::lean_dec_ref_known(v___x_342_, 1);
                            v___x_344_ = (crate::leanh::lean_unbox(v_a_343_) as u8);
                            crate::leanh::lean_dec(v_a_343_);
                            v___x_345_ = l_Lean_Elab_Deriving_SizeOf_mkSizeOfHandler___lam__0(
                                v___x_344_, v_a_306_, v_a_307_,
                            );
                            v___y_333_ = v___x_345_;
                            state = 6;
                            continue;
                        } else {
                            v___y_333_ = v___x_342_;
                            state = 6;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v___x_310_ = crate::leanh::lean_box(0);
                v_sz_311_ = lean_array_size(v_declNames_305_);
                v___x_312_ = 0usize;
                v___x_313_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Deriving_SizeOf_mkSizeOfHandler_spec__0(v_declNames_305_, v_sz_311_, v___x_312_, v___x_310_, v_a_306_, v_a_307_);
                if crate::leanh::lean_obj_tag(v___x_313_) == 0 {
                    v_isSharedCheck_322_ = (!crate::leanh::lean_is_exclusive(v___x_313_)) as u8;
                    if v_isSharedCheck_322_ == 0 {
                        v_unused_323_ = crate::leanh::lean_ctor_get(v___x_313_, 0);
                        crate::leanh::lean_dec(v_unused_323_);
                        v___x_315_ = v___x_313_;
                        v_isShared_316_ = v_isSharedCheck_322_;
                        state = 2;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v___x_313_);
                        v___x_315_ = crate::leanh::lean_box(0);
                        v_isShared_316_ = v_isSharedCheck_322_;
                        state = 2;
                        continue;
                    }
                } else {
                    v_a_324_ = crate::leanh::lean_ctor_get(v___x_313_, 0);
                    v_isSharedCheck_331_ = (!crate::leanh::lean_is_exclusive(v___x_313_)) as u8;
                    if v_isSharedCheck_331_ == 0 {
                        v___x_326_ = v___x_313_;
                        v_isShared_327_ = v_isSharedCheck_331_;
                        state = 4;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_324_);
                        crate::leanh::lean_dec(v___x_313_);
                        v___x_326_ = crate::leanh::lean_box(0);
                        v_isShared_327_ = v_isSharedCheck_331_;
                        state = 4;
                        continue;
                    }
                }
            }
            2 => {
                v___x_317_ = 1;
                v___x_318_ = crate::leanh::lean_box((v___x_317_) as usize);
                if v_isShared_316_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_315_, 0, v___x_318_);
                    v___x_320_ = v___x_315_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_321_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_321_, 0, v___x_318_);
                    v___x_320_ = v_reuseFailAlloc_321_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_320_;
            }
            4 => {
                if v_isShared_327_ == 0 {
                    v___x_329_ = v___x_326_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_330_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_330_, 0, v_a_324_);
                    v___x_329_ = v_reuseFailAlloc_330_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_329_;
            }
            6 => {
                if crate::leanh::lean_obj_tag(v___y_333_) == 0 {
                    v_a_334_ = crate::leanh::lean_ctor_get(v___y_333_, 0);
                    v___x_335_ = (crate::leanh::lean_unbox(v_a_334_) as u8);
                    if v___x_335_ == 0 {
                        return v___y_333_;
                    } else {
                        crate::leanh::lean_dec_ref_known(v___y_333_, 1);
                        state = 1;
                        continue;
                    }
                } else {
                    return v___y_333_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_Deriving_SizeOf_mkSizeOfHandler___boxed(
    mut v_declNames_346_: *mut crate::leanh::LeanObject,
    mut v_a_347_: *mut crate::leanh::LeanObject,
    mut v_a_348_: *mut crate::leanh::LeanObject,
    mut v_a_349_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_350_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_350_ = l_Lean_Elab_Deriving_SizeOf_mkSizeOfHandler(v_declNames_346_, v_a_347_, v_a_348_);
    crate::leanh::lean_dec(v_a_348_);
    crate::leanh::lean_dec_ref(v_a_347_);
    crate::leanh::lean_dec_ref(v_declNames_346_);
    return v_res_350_;
}
pub unsafe fn l___private_Lean_Elab_Deriving_SizeOf_0__Lean_Elab_Deriving_SizeOf_initFn_00___x40_Lean_Elab_Deriving_SizeOf_388027031____hygCtx___hyg_2_()
-> *mut crate::leanh::LeanObject {
    let mut v___x_356_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_357_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_358_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_356_ = l___private_Lean_Elab_Deriving_SizeOf_0__Lean_Elab_Deriving_SizeOf_initFn___closed__1_00___x40_Lean_Elab_Deriving_SizeOf_388027031____hygCtx___hyg_2_;
    v___x_357_ = l___private_Lean_Elab_Deriving_SizeOf_0__Lean_Elab_Deriving_SizeOf_initFn___closed__2_00___x40_Lean_Elab_Deriving_SizeOf_388027031____hygCtx___hyg_2_;
    v___x_358_ = l_Lean_Elab_registerDerivingHandler(v___x_356_, v___x_357_);
    return v___x_358_;
}
pub unsafe fn l___private_Lean_Elab_Deriving_SizeOf_0__Lean_Elab_Deriving_SizeOf_initFn_00___x40_Lean_Elab_Deriving_SizeOf_388027031____hygCtx___hyg_2____boxed(
    mut v_a_359_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_360_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_360_ = l___private_Lean_Elab_Deriving_SizeOf_0__Lean_Elab_Deriving_SizeOf_initFn_00___x40_Lean_Elab_Deriving_SizeOf_388027031____hygCtx___hyg_2_();
    return v_res_360_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Elab_Deriving_SizeOf(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Meta_SizeOf(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Elab_Deriving_Basic(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Elab_Deriving_Util(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = l___private_Lean_Elab_Deriving_SizeOf_0__Lean_Elab_Deriving_SizeOf_initFn_00___x40_Lean_Elab_Deriving_SizeOf_388027031____hygCtx___hyg_2_();
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Elab_Deriving_SizeOf(
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
pub unsafe fn initialize_Lean_Elab_Deriving_SizeOf(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Meta_SizeOf(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lean_Elab_Deriving_Basic(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lean_Elab_Deriving_Util(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Elab_Deriving_SizeOf(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_Elab_Deriving_SizeOf(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Lean_Elab_Deriving_SizeOf(builtin);
}
