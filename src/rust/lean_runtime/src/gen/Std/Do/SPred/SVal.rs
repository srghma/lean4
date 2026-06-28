// Lean compiler output
// Module: Std.Do.SPred.SVal
// Imports: Init.Data.List.Notation Init.SimpLemmas Init.Core Init.Grind.Attr
use crate::r#gen::Init::Core::{initialize_Init_Core, runtime_initialize_Init_Core};
use crate::r#gen::Init::Data::List::Notation::{
    initialize_Init_Data_List_Notation, runtime_initialize_Init_Data_List_Notation,
};
use crate::r#gen::Init::Grind::Attr::{
    initialize_Init_Grind_Attr, runtime_initialize_Init_Grind_Attr,
};
use crate::r#gen::Init::SimpLemmas::{
    initialize_Init_SimpLemmas, runtime_initialize_Init_SimpLemmas,
};
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_alloc_closure, lean_alloc_ctor, lean_apply_1,
    lean_apply_2, lean_apply_3, lean_box, lean_closure_set, lean_ctor_get, lean_ctor_set, lean_dec,
    lean_dec_ref, lean_dec_ref_known, lean_inc, lean_io_result_is_error, lean_io_result_mk_ok,
    lean_mark_persistent, lean_obj_tag,
};
pub static mut l_Std_Do_SVal_instInhabitedStateTupleNil: *mut LeanObject = core::ptr::null_mut();
pub unsafe fn _init_l_Std_Do_SVal_instInhabitedStateTupleNil() -> *mut LeanObject {
    let mut v___x_157_: *mut LeanObject = core::ptr::null_mut();
    v___x_157_ = lean_box(0);
    return v___x_157_;
}
pub unsafe fn l_Std_Do_SVal_instInhabitedStateTupleCons___redArg(
    mut v_inst_158_: *mut LeanObject,
    mut v_inst_159_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_160_: *mut LeanObject = core::ptr::null_mut();
    v___x_160_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_160_, 0, v_inst_158_);
    lean_ctor_set(v___x_160_, 1, v_inst_159_);
    return v___x_160_;
}
pub unsafe fn l_Std_Do_SVal_instInhabitedStateTupleCons(
    mut v_00_u03c3_161_: *mut LeanObject,
    mut v_00_u03c3s_162_: *mut LeanObject,
    mut v_inst_163_: *mut LeanObject,
    mut v_inst_164_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_165_: *mut LeanObject = core::ptr::null_mut();
    v___x_165_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_165_, 0, v_inst_163_);
    lean_ctor_set(v___x_165_, 1, v_inst_164_);
    return v___x_165_;
}
pub unsafe fn l_Std_Do_SVal_instInhabitedStateTupleCons___boxed(
    mut v_00_u03c3_166_: *mut LeanObject,
    mut v_00_u03c3s_167_: *mut LeanObject,
    mut v_inst_168_: *mut LeanObject,
    mut v_inst_169_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_170_: *mut LeanObject = core::ptr::null_mut();
    v_res_170_ = l_Std_Do_SVal_instInhabitedStateTupleCons(
        v_00_u03c3_166_,
        v_00_u03c3s_167_,
        v_inst_168_,
        v_inst_169_,
    );
    lean_dec(v_00_u03c3s_167_);
    return v_res_170_;
}
pub unsafe fn l_Std_Do_SVal_curry___redArg___lam__0(
    mut v___y_171_: *mut LeanObject,
    mut v_f_172_: *mut LeanObject,
    mut v_s_x27_173_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_174_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_175_: *mut LeanObject = core::ptr::null_mut();
    v___x_174_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_174_, 0, v___y_171_);
    lean_ctor_set(v___x_174_, 1, v_s_x27_173_);
    v___x_175_ = lean_apply_1(v_f_172_, v___x_174_);
    return v___x_175_;
}
pub unsafe fn l_Std_Do_SVal_curry___redArg(
    mut v_00_u03c3s_176_: *mut LeanObject,
    mut v_f_177_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_00_u03c3s_176_) == 0 {
        let mut v___x_178_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_179_: *mut LeanObject = core::ptr::null_mut();
        v___x_178_ = lean_box(0);
        v___x_179_ = lean_apply_1(v_f_177_, v___x_178_);
        return v___x_179_;
    } else {
        let mut v_tail_180_: *mut LeanObject = core::ptr::null_mut();
        let mut v___f_181_: *mut LeanObject = core::ptr::null_mut();
        v_tail_180_ = lean_ctor_get(v_00_u03c3s_176_, 1);
        lean_inc(v_tail_180_);
        lean_dec_ref_known(v_00_u03c3s_176_, 2);
        v___f_181_ = lean_alloc_closure(
            l_Std_Do_SVal_curry___redArg___lam__1 as *mut core::ffi::c_void,
            3,
            2,
        );
        lean_closure_set(v___f_181_, 0, v_f_177_);
        lean_closure_set(v___f_181_, 1, v_tail_180_);
        return v___f_181_;
    }
}
pub unsafe fn l_Std_Do_SVal_curry___redArg___lam__1(
    mut v_f_182_: *mut LeanObject,
    mut v_tail_183_: *mut LeanObject,
    mut v___y_184_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_185_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_186_: *mut LeanObject = core::ptr::null_mut();
    v___f_185_ = lean_alloc_closure(
        l_Std_Do_SVal_curry___redArg___lam__0 as *mut core::ffi::c_void,
        3,
        2,
    );
    lean_closure_set(v___f_185_, 0, v___y_184_);
    lean_closure_set(v___f_185_, 1, v_f_182_);
    v___x_186_ = l_Std_Do_SVal_curry___redArg(v_tail_183_, v___f_185_);
    return v___x_186_;
}
pub unsafe fn l_Std_Do_SVal_curry(
    mut v_00_u03b1_187_: *mut LeanObject,
    mut v_00_u03c3s_188_: *mut LeanObject,
    mut v_f_189_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_190_: *mut LeanObject = core::ptr::null_mut();
    v___x_190_ = l_Std_Do_SVal_curry___redArg(v_00_u03c3s_188_, v_f_189_);
    return v___x_190_;
}
pub unsafe fn l_Std_Do_SVal_uncurry___redArg(
    mut v_00_u03c3s_191_: *mut LeanObject,
    mut v_f_192_: *mut LeanObject,
    mut v_a_193_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_tail_194_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_195_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_196_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_197_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_00_u03c3s_191_) == 0 {
                    lean_dec(v_a_193_);
                    return v_f_192_;
                } else {
                    v_tail_194_ = lean_ctor_get(v_00_u03c3s_191_, 1);
                    v_fst_195_ = lean_ctor_get(v_a_193_, 0);
                    lean_inc(v_fst_195_);
                    v_snd_196_ = lean_ctor_get(v_a_193_, 1);
                    lean_inc(v_snd_196_);
                    lean_dec(v_a_193_);
                    v___x_197_ = lean_apply_1(v_f_192_, v_fst_195_);
                    v_00_u03c3s_191_ = v_tail_194_;
                    v_f_192_ = v___x_197_;
                    v_a_193_ = v_snd_196_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Do_SVal_uncurry___redArg___boxed(
    mut v_00_u03c3s_199_: *mut LeanObject,
    mut v_f_200_: *mut LeanObject,
    mut v_a_201_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_202_: *mut LeanObject = core::ptr::null_mut();
    v_res_202_ = l_Std_Do_SVal_uncurry___redArg(v_00_u03c3s_199_, v_f_200_, v_a_201_);
    lean_dec(v_00_u03c3s_199_);
    return v_res_202_;
}
pub unsafe fn l_Std_Do_SVal_uncurry(
    mut v_00_u03b1_203_: *mut LeanObject,
    mut v_00_u03c3s_204_: *mut LeanObject,
    mut v_f_205_: *mut LeanObject,
    mut v_a_206_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_207_: *mut LeanObject = core::ptr::null_mut();
    v___x_207_ = l_Std_Do_SVal_uncurry___redArg(v_00_u03c3s_204_, v_f_205_, v_a_206_);
    return v___x_207_;
}
pub unsafe fn l_Std_Do_SVal_uncurry___boxed(
    mut v_00_u03b1_208_: *mut LeanObject,
    mut v_00_u03c3s_209_: *mut LeanObject,
    mut v_f_210_: *mut LeanObject,
    mut v_a_211_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_212_: *mut LeanObject = core::ptr::null_mut();
    v_res_212_ = l_Std_Do_SVal_uncurry(v_00_u03b1_208_, v_00_u03c3s_209_, v_f_210_, v_a_211_);
    lean_dec(v_00_u03c3s_209_);
    return v_res_212_;
}
pub unsafe fn l___private_Std_Do_SPred_SVal_0__Std_Do_SVal_uncurry_match__3_splitter___redArg(
    mut v_00_u03c3s_213_: *mut LeanObject,
    mut v_f_214_: *mut LeanObject,
    mut v_h__1_215_: *mut LeanObject,
    mut v_h__2_216_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_00_u03c3s_213_) == 0 {
        let mut v___x_217_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_216_);
        v___x_217_ = lean_apply_1(v_h__1_215_, v_f_214_);
        return v___x_217_;
    } else {
        let mut v_tail_218_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_219_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_215_);
        v_tail_218_ = lean_ctor_get(v_00_u03c3s_213_, 1);
        lean_inc(v_tail_218_);
        lean_dec_ref_known(v_00_u03c3s_213_, 2);
        v___x_219_ = lean_apply_3(v_h__2_216_, lean_box(0), v_tail_218_, v_f_214_);
        return v___x_219_;
    }
}
pub unsafe fn l___private_Std_Do_SPred_SVal_0__Std_Do_SVal_uncurry_match__3_splitter(
    mut v_00_u03b1_220_: *mut LeanObject,
    mut v_motive_221_: *mut LeanObject,
    mut v_00_u03c3s_222_: *mut LeanObject,
    mut v_f_223_: *mut LeanObject,
    mut v_h__1_224_: *mut LeanObject,
    mut v_h__2_225_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_00_u03c3s_222_) == 0 {
        let mut v___x_226_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_225_);
        v___x_226_ = lean_apply_1(v_h__1_224_, v_f_223_);
        return v___x_226_;
    } else {
        let mut v_tail_227_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_228_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_224_);
        v_tail_227_ = lean_ctor_get(v_00_u03c3s_222_, 1);
        lean_inc(v_tail_227_);
        lean_dec_ref_known(v_00_u03c3s_222_, 2);
        v___x_228_ = lean_apply_3(v_h__2_225_, lean_box(0), v_tail_227_, v_f_223_);
        return v___x_228_;
    }
}
pub unsafe fn l___private_Std_Do_SPred_SVal_0__Std_Do_SVal_uncurry_match__1_splitter___redArg(
    mut v_x_229_: *mut LeanObject,
    mut v_h__1_230_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_fst_231_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_232_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_233_: *mut LeanObject = core::ptr::null_mut();
    v_fst_231_ = lean_ctor_get(v_x_229_, 0);
    lean_inc(v_fst_231_);
    v_snd_232_ = lean_ctor_get(v_x_229_, 1);
    lean_inc(v_snd_232_);
    lean_dec_ref(v_x_229_);
    v___x_233_ = lean_apply_2(v_h__1_230_, v_fst_231_, v_snd_232_);
    return v___x_233_;
}
pub unsafe fn l___private_Std_Do_SPred_SVal_0__Std_Do_SVal_uncurry_match__1_splitter(
    mut v_head_234_: *mut LeanObject,
    mut v_tail_235_: *mut LeanObject,
    mut v_motive_236_: *mut LeanObject,
    mut v_x_237_: *mut LeanObject,
    mut v_h__1_238_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_fst_239_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_240_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_241_: *mut LeanObject = core::ptr::null_mut();
    v_fst_239_ = lean_ctor_get(v_x_237_, 0);
    lean_inc(v_fst_239_);
    v_snd_240_ = lean_ctor_get(v_x_237_, 1);
    lean_inc(v_snd_240_);
    lean_dec_ref(v_x_237_);
    v___x_241_ = lean_apply_2(v_h__1_238_, v_fst_239_, v_snd_240_);
    return v___x_241_;
}
pub unsafe fn l___private_Std_Do_SPred_SVal_0__Std_Do_SVal_uncurry_match__1_splitter___boxed(
    mut v_head_242_: *mut LeanObject,
    mut v_tail_243_: *mut LeanObject,
    mut v_motive_244_: *mut LeanObject,
    mut v_x_245_: *mut LeanObject,
    mut v_h__1_246_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_247_: *mut LeanObject = core::ptr::null_mut();
    v_res_247_ = l___private_Std_Do_SPred_SVal_0__Std_Do_SVal_uncurry_match__1_splitter(
        v_head_242_,
        v_tail_243_,
        v_motive_244_,
        v_x_245_,
        v_h__1_246_,
    );
    lean_dec(v_tail_243_);
    return v_res_247_;
}
pub unsafe fn l___private_Std_Do_SPred_SVal_0__Std_Do_SVal_curry_match__1_splitter___redArg(
    mut v_00_u03c3s_248_: *mut LeanObject,
    mut v_f_249_: *mut LeanObject,
    mut v_h__1_250_: *mut LeanObject,
    mut v_h__2_251_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_00_u03c3s_248_) == 0 {
        let mut v___x_252_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_251_);
        v___x_252_ = lean_apply_1(v_h__1_250_, v_f_249_);
        return v___x_252_;
    } else {
        let mut v_tail_253_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_254_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_250_);
        v_tail_253_ = lean_ctor_get(v_00_u03c3s_248_, 1);
        lean_inc(v_tail_253_);
        lean_dec_ref_known(v_00_u03c3s_248_, 2);
        v___x_254_ = lean_apply_3(v_h__2_251_, lean_box(0), v_tail_253_, v_f_249_);
        return v___x_254_;
    }
}
pub unsafe fn l___private_Std_Do_SPred_SVal_0__Std_Do_SVal_curry_match__1_splitter(
    mut v_00_u03b1_255_: *mut LeanObject,
    mut v_motive_256_: *mut LeanObject,
    mut v_00_u03c3s_257_: *mut LeanObject,
    mut v_f_258_: *mut LeanObject,
    mut v_h__1_259_: *mut LeanObject,
    mut v_h__2_260_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_00_u03c3s_257_) == 0 {
        let mut v___x_261_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_260_);
        v___x_261_ = lean_apply_1(v_h__1_259_, v_f_258_);
        return v___x_261_;
    } else {
        let mut v_tail_262_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_263_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_259_);
        v_tail_262_ = lean_ctor_get(v_00_u03c3s_257_, 1);
        lean_inc(v_tail_262_);
        lean_dec_ref_known(v_00_u03c3s_257_, 2);
        v___x_263_ = lean_apply_3(v_h__2_260_, lean_box(0), v_tail_262_, v_f_258_);
        return v___x_263_;
    }
}
pub unsafe fn l_Std_Do_SVal_instInhabited___redArg___lam__0(
    mut v_inst_264_: *mut LeanObject,
    mut v_x_265_: *mut LeanObject,
) -> *mut LeanObject {
    lean_inc(v_inst_264_);
    return v_inst_264_;
}
pub unsafe fn l_Std_Do_SVal_instInhabited___redArg___lam__0___boxed(
    mut v_inst_266_: *mut LeanObject,
    mut v_x_267_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_268_: *mut LeanObject = core::ptr::null_mut();
    v_res_268_ = l_Std_Do_SVal_instInhabited___redArg___lam__0(v_inst_266_, v_x_267_);
    lean_dec(v_x_267_);
    lean_dec(v_inst_266_);
    return v_res_268_;
}
pub unsafe fn l_Std_Do_SVal_instInhabited___redArg(
    mut v_00_u03c3s_269_: *mut LeanObject,
    mut v_inst_270_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_271_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_272_: *mut LeanObject = core::ptr::null_mut();
    v___f_271_ = lean_alloc_closure(
        l_Std_Do_SVal_instInhabited___redArg___lam__0___boxed as *mut core::ffi::c_void,
        2,
        1,
    );
    lean_closure_set(v___f_271_, 0, v_inst_270_);
    v___x_272_ = l_Std_Do_SVal_curry___redArg(v_00_u03c3s_269_, v___f_271_);
    return v___x_272_;
}
pub unsafe fn l_Std_Do_SVal_instInhabited(
    mut v_00_u03b1_273_: *mut LeanObject,
    mut v_00_u03c3s_274_: *mut LeanObject,
    mut v_inst_275_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_276_: *mut LeanObject = core::ptr::null_mut();
    v___x_276_ = l_Std_Do_SVal_instInhabited___redArg(v_00_u03c3s_274_, v_inst_275_);
    return v___x_276_;
}
pub unsafe fn l_Std_Do_SVal_instGetTyCons___redArg___lam__0(
    mut v_s_277_: *mut LeanObject,
    mut v_x_278_: *mut LeanObject,
) -> *mut LeanObject {
    lean_inc(v_s_277_);
    return v_s_277_;
}
pub unsafe fn l_Std_Do_SVal_instGetTyCons___redArg___lam__0___boxed(
    mut v_s_279_: *mut LeanObject,
    mut v_x_280_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_281_: *mut LeanObject = core::ptr::null_mut();
    v_res_281_ = l_Std_Do_SVal_instGetTyCons___redArg___lam__0(v_s_279_, v_x_280_);
    lean_dec(v_x_280_);
    lean_dec(v_s_279_);
    return v_res_281_;
}
pub unsafe fn l_Std_Do_SVal_instGetTyCons___redArg___lam__1(
    mut v_00_u03c3s_282_: *mut LeanObject,
    mut v_s_283_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_284_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_285_: *mut LeanObject = core::ptr::null_mut();
    v___f_284_ = lean_alloc_closure(
        l_Std_Do_SVal_instGetTyCons___redArg___lam__0___boxed as *mut core::ffi::c_void,
        2,
        1,
    );
    lean_closure_set(v___f_284_, 0, v_s_283_);
    v___x_285_ = l_Std_Do_SVal_curry___redArg(v_00_u03c3s_282_, v___f_284_);
    return v___x_285_;
}
pub unsafe fn l_Std_Do_SVal_instGetTyCons___redArg(
    mut v_00_u03c3s_286_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_287_: *mut LeanObject = core::ptr::null_mut();
    v___f_287_ = lean_alloc_closure(
        l_Std_Do_SVal_instGetTyCons___redArg___lam__1 as *mut core::ffi::c_void,
        2,
        1,
    );
    lean_closure_set(v___f_287_, 0, v_00_u03c3s_286_);
    return v___f_287_;
}
pub unsafe fn l_Std_Do_SVal_instGetTyCons(
    mut v_00_u03c3_288_: *mut LeanObject,
    mut v_00_u03c3s_289_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_290_: *mut LeanObject = core::ptr::null_mut();
    v___f_290_ = lean_alloc_closure(
        l_Std_Do_SVal_instGetTyCons___redArg___lam__1 as *mut core::ffi::c_void,
        2,
        1,
    );
    lean_closure_set(v___f_290_, 0, v_00_u03c3s_289_);
    return v___f_290_;
}
pub unsafe fn l_Std_Do_SVal_instGetTyCons__1___redArg(
    mut v_inst_291_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_292_: *mut LeanObject = core::ptr::null_mut();
    v___f_292_ = lean_alloc_closure(
        l_Std_Do_SVal_instInhabited___redArg___lam__0___boxed as *mut core::ffi::c_void,
        2,
        1,
    );
    lean_closure_set(v___f_292_, 0, v_inst_291_);
    return v___f_292_;
}
pub unsafe fn l_Std_Do_SVal_instGetTyCons__1(
    mut v_00_u03c3_u2081_293_: *mut LeanObject,
    mut v_00_u03c3s_294_: *mut LeanObject,
    mut v_00_u03c3_u2082_295_: *mut LeanObject,
    mut v_inst_296_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_297_: *mut LeanObject = core::ptr::null_mut();
    v___f_297_ = lean_alloc_closure(
        l_Std_Do_SVal_instInhabited___redArg___lam__0___boxed as *mut core::ffi::c_void,
        2,
        1,
    );
    lean_closure_set(v___f_297_, 0, v_inst_296_);
    return v___f_297_;
}
pub unsafe fn l_Std_Do_SVal_instGetTyCons__1___boxed(
    mut v_00_u03c3_u2081_298_: *mut LeanObject,
    mut v_00_u03c3s_299_: *mut LeanObject,
    mut v_00_u03c3_u2082_300_: *mut LeanObject,
    mut v_inst_301_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_302_: *mut LeanObject = core::ptr::null_mut();
    v_res_302_ = l_Std_Do_SVal_instGetTyCons__1(
        v_00_u03c3_u2081_298_,
        v_00_u03c3s_299_,
        v_00_u03c3_u2082_300_,
        v_inst_301_,
    );
    lean_dec(v_00_u03c3s_299_);
    return v_res_302_;
}
pub unsafe fn l_Std_Do_SVal_getThe___redArg(mut v_inst_303_: *mut LeanObject) -> *mut LeanObject {
    lean_inc(v_inst_303_);
    return v_inst_303_;
}
pub unsafe fn l_Std_Do_SVal_getThe___redArg___boxed(
    mut v_inst_304_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_305_: *mut LeanObject = core::ptr::null_mut();
    v_res_305_ = l_Std_Do_SVal_getThe___redArg(v_inst_304_);
    lean_dec(v_inst_304_);
    return v_res_305_;
}
pub unsafe fn l_Std_Do_SVal_getThe(
    mut v_00_u03c3s_306_: *mut LeanObject,
    mut v_00_u03c3_307_: *mut LeanObject,
    mut v_inst_308_: *mut LeanObject,
) -> *mut LeanObject {
    lean_inc(v_inst_308_);
    return v_inst_308_;
}
pub unsafe fn l_Std_Do_SVal_getThe___boxed(
    mut v_00_u03c3s_309_: *mut LeanObject,
    mut v_00_u03c3_310_: *mut LeanObject,
    mut v_inst_311_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_312_: *mut LeanObject = core::ptr::null_mut();
    v_res_312_ = l_Std_Do_SVal_getThe(v_00_u03c3s_309_, v_00_u03c3_310_, v_inst_311_);
    lean_dec(v_inst_311_);
    lean_dec(v_00_u03c3s_309_);
    return v_res_312_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Std_Do_SPred_SVal(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Init_Data_List_Notation(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_SimpLemmas(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Core(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Grind_Attr(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    l_Std_Do_SVal_instInhabitedStateTupleNil = _init_l_Std_Do_SVal_instInhabitedStateTupleNil();
    lean_mark_persistent(l_Std_Do_SVal_instInhabitedStateTupleNil);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Std_Do_SPred_SVal(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_meta_initialized = true;
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Std_Do_SPred_SVal(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Init_Data_List_Notation(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_SimpLemmas(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Core(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Grind_Attr(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Std_Do_SPred_SVal(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Std_Do_SPred_SVal(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Std_Do_SPred_SVal(builtin);
}
