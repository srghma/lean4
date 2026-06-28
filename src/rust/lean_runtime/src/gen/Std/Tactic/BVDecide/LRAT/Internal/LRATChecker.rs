// Lean compiler output
// Module: Std.Tactic.BVDecide.LRAT.Internal.LRATChecker
// Imports: Std.Tactic.BVDecide.LRAT.Actions Std.Tactic.BVDecide.LRAT.Internal.Formula.Class
use crate::r#gen::Std::Tactic::BVDecide::LRAT::Actions::{
    initialize_Std_Tactic_BVDecide_LRAT_Actions,
    runtime_initialize_Std_Tactic_BVDecide_LRAT_Actions,
};
use crate::r#gen::Std::Tactic::BVDecide::LRAT::Internal::Formula::Class::{
    initialize_Std_Tactic_BVDecide_LRAT_Internal_Formula_Class,
    runtime_initialize_Std_Tactic_BVDecide_LRAT_Internal_Formula_Class,
};
use crate::lean_imports_rs::Init::Prelude::{lean_nat_dec_eq, lean_nat_dec_le};
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_apply_2, lean_apply_3, lean_apply_5, lean_box,
    lean_ctor_get, lean_dec, lean_dec_ref, lean_dec_ref_known, lean_inc, lean_inc_ref,
    lean_io_result_is_error, lean_io_result_mk_ok, lean_obj_tag, lean_unbox, lean_unsigned_to_nat,
};
pub static mut l_Std_Tactic_BVDecide_LRAT_Internal_instInhabitedResult_default: u8 = 0;
pub static mut l_Std_Tactic_BVDecide_LRAT_Internal_instInhabitedResult: u8 = 0;
pub static l_Std_Tactic_BVDecide_LRAT_Internal_instToStringResult___lam__0___closed__0_value:
    LeanStringObject<8> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 8,
    m_capacity: 8,
    m_length: 7,
    m_data: [115, 117, 99, 99, 101, 115, 115, 0],
};
static mut l_Std_Tactic_BVDecide_LRAT_Internal_instToStringResult___lam__0___closed__0:
    *mut LeanObject = core::ptr::addr_of!(
    l_Std_Tactic_BVDecide_LRAT_Internal_instToStringResult___lam__0___closed__0_value
) as *mut LeanObject;
pub static l_Std_Tactic_BVDecide_LRAT_Internal_instToStringResult___lam__0___closed__1_value:
    LeanStringObject<13> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 13,
    m_capacity: 13,
    m_length: 12,
    m_data: [111, 117, 116, 32, 111, 102, 32, 112, 114, 111, 111, 102, 0],
};
static mut l_Std_Tactic_BVDecide_LRAT_Internal_instToStringResult___lam__0___closed__1:
    *mut LeanObject = core::ptr::addr_of!(
    l_Std_Tactic_BVDecide_LRAT_Internal_instToStringResult___lam__0___closed__1_value
) as *mut LeanObject;
pub static l_Std_Tactic_BVDecide_LRAT_Internal_instToStringResult___lam__0___closed__2_value:
    LeanStringObject<12> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 12,
    m_capacity: 12,
    m_length: 11,
    m_data: [114, 117, 112, 32, 102, 97, 105, 108, 117, 114, 101, 0],
};
static mut l_Std_Tactic_BVDecide_LRAT_Internal_instToStringResult___lam__0___closed__2:
    *mut LeanObject = core::ptr::addr_of!(
    l_Std_Tactic_BVDecide_LRAT_Internal_instToStringResult___lam__0___closed__2_value
) as *mut LeanObject;
pub static l_Std_Tactic_BVDecide_LRAT_Internal_instToStringResult___closed__0_value:
    LeanClosureObject<0> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Std_Tactic_BVDecide_LRAT_Internal_instToStringResult___lam__0___boxed
        as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_Tactic_BVDecide_LRAT_Internal_instToStringResult___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Tactic_BVDecide_LRAT_Internal_instToStringResult___closed__0_value)
        as *mut LeanObject;
pub static mut l_Std_Tactic_BVDecide_LRAT_Internal_instToStringResult: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Tactic_BVDecide_LRAT_Internal_instToStringResult___closed__0_value)
        as *mut LeanObject;
pub unsafe fn l_Std_Tactic_BVDecide_LRAT_Internal_Result_ctorIdx(
    mut v_x_171_: u8,
) -> *mut LeanObject {
    match v_x_171_ {
        0 => {
            let mut v___x_172_: *mut LeanObject = core::ptr::null_mut();
            v___x_172_ = lean_unsigned_to_nat(0);
            return v___x_172_;
        }
        1 => {
            let mut v___x_173_: *mut LeanObject = core::ptr::null_mut();
            v___x_173_ = lean_unsigned_to_nat(1);
            return v___x_173_;
        }
        _ => {
            let mut v___x_174_: *mut LeanObject = core::ptr::null_mut();
            v___x_174_ = lean_unsigned_to_nat(2);
            return v___x_174_;
        }
    }
}
pub unsafe fn l_Std_Tactic_BVDecide_LRAT_Internal_Result_ctorIdx___boxed(
    mut v_x_175_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_x_boxed_176_: u8 = 0;
    let mut v_res_177_: *mut LeanObject = core::ptr::null_mut();
    v_x_boxed_176_ = (lean_unbox(v_x_175_) as u8);
    v_res_177_ = l_Std_Tactic_BVDecide_LRAT_Internal_Result_ctorIdx(v_x_boxed_176_);
    return v_res_177_;
}
pub unsafe fn l_Std_Tactic_BVDecide_LRAT_Internal_Result_toCtorIdx(
    mut v_x_178_: u8,
) -> *mut LeanObject {
    let mut v___x_179_: *mut LeanObject = core::ptr::null_mut();
    v___x_179_ = l_Std_Tactic_BVDecide_LRAT_Internal_Result_ctorIdx(v_x_178_);
    return v___x_179_;
}
pub unsafe fn l_Std_Tactic_BVDecide_LRAT_Internal_Result_toCtorIdx___boxed(
    mut v_x_180_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_x_4__boxed_181_: u8 = 0;
    let mut v_res_182_: *mut LeanObject = core::ptr::null_mut();
    v_x_4__boxed_181_ = (lean_unbox(v_x_180_) as u8);
    v_res_182_ = l_Std_Tactic_BVDecide_LRAT_Internal_Result_toCtorIdx(v_x_4__boxed_181_);
    return v_res_182_;
}
pub unsafe fn l_Std_Tactic_BVDecide_LRAT_Internal_Result_ctorElim___redArg(
    mut v_k_183_: *mut LeanObject,
) -> *mut LeanObject {
    lean_inc(v_k_183_);
    return v_k_183_;
}
pub unsafe fn l_Std_Tactic_BVDecide_LRAT_Internal_Result_ctorElim___redArg___boxed(
    mut v_k_184_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_185_: *mut LeanObject = core::ptr::null_mut();
    v_res_185_ = l_Std_Tactic_BVDecide_LRAT_Internal_Result_ctorElim___redArg(v_k_184_);
    lean_dec(v_k_184_);
    return v_res_185_;
}
pub unsafe fn l_Std_Tactic_BVDecide_LRAT_Internal_Result_ctorElim(
    mut v_motive_186_: *mut LeanObject,
    mut v_ctorIdx_187_: *mut LeanObject,
    mut v_t_188_: u8,
    mut v_h_189_: *mut LeanObject,
    mut v_k_190_: *mut LeanObject,
) -> *mut LeanObject {
    lean_inc(v_k_190_);
    return v_k_190_;
}
pub unsafe fn l_Std_Tactic_BVDecide_LRAT_Internal_Result_ctorElim___boxed(
    mut v_motive_191_: *mut LeanObject,
    mut v_ctorIdx_192_: *mut LeanObject,
    mut v_t_193_: *mut LeanObject,
    mut v_h_194_: *mut LeanObject,
    mut v_k_195_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_t_boxed_196_: u8 = 0;
    let mut v_res_197_: *mut LeanObject = core::ptr::null_mut();
    v_t_boxed_196_ = (lean_unbox(v_t_193_) as u8);
    v_res_197_ = l_Std_Tactic_BVDecide_LRAT_Internal_Result_ctorElim(
        v_motive_191_,
        v_ctorIdx_192_,
        v_t_boxed_196_,
        v_h_194_,
        v_k_195_,
    );
    lean_dec(v_k_195_);
    lean_dec(v_ctorIdx_192_);
    return v_res_197_;
}
pub unsafe fn l_Std_Tactic_BVDecide_LRAT_Internal_Result_success_elim___redArg(
    mut v_success_198_: *mut LeanObject,
) -> *mut LeanObject {
    lean_inc(v_success_198_);
    return v_success_198_;
}
pub unsafe fn l_Std_Tactic_BVDecide_LRAT_Internal_Result_success_elim___redArg___boxed(
    mut v_success_199_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_200_: *mut LeanObject = core::ptr::null_mut();
    v_res_200_ = l_Std_Tactic_BVDecide_LRAT_Internal_Result_success_elim___redArg(v_success_199_);
    lean_dec(v_success_199_);
    return v_res_200_;
}
pub unsafe fn l_Std_Tactic_BVDecide_LRAT_Internal_Result_success_elim(
    mut v_motive_201_: *mut LeanObject,
    mut v_t_202_: u8,
    mut v_h_203_: *mut LeanObject,
    mut v_success_204_: *mut LeanObject,
) -> *mut LeanObject {
    lean_inc(v_success_204_);
    return v_success_204_;
}
pub unsafe fn l_Std_Tactic_BVDecide_LRAT_Internal_Result_success_elim___boxed(
    mut v_motive_205_: *mut LeanObject,
    mut v_t_206_: *mut LeanObject,
    mut v_h_207_: *mut LeanObject,
    mut v_success_208_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_t_boxed_209_: u8 = 0;
    let mut v_res_210_: *mut LeanObject = core::ptr::null_mut();
    v_t_boxed_209_ = (lean_unbox(v_t_206_) as u8);
    v_res_210_ = l_Std_Tactic_BVDecide_LRAT_Internal_Result_success_elim(
        v_motive_205_,
        v_t_boxed_209_,
        v_h_207_,
        v_success_208_,
    );
    lean_dec(v_success_208_);
    return v_res_210_;
}
pub unsafe fn l_Std_Tactic_BVDecide_LRAT_Internal_Result_outOfProof_elim___redArg(
    mut v_outOfProof_211_: *mut LeanObject,
) -> *mut LeanObject {
    lean_inc(v_outOfProof_211_);
    return v_outOfProof_211_;
}
pub unsafe fn l_Std_Tactic_BVDecide_LRAT_Internal_Result_outOfProof_elim___redArg___boxed(
    mut v_outOfProof_212_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_213_: *mut LeanObject = core::ptr::null_mut();
    v_res_213_ =
        l_Std_Tactic_BVDecide_LRAT_Internal_Result_outOfProof_elim___redArg(v_outOfProof_212_);
    lean_dec(v_outOfProof_212_);
    return v_res_213_;
}
pub unsafe fn l_Std_Tactic_BVDecide_LRAT_Internal_Result_outOfProof_elim(
    mut v_motive_214_: *mut LeanObject,
    mut v_t_215_: u8,
    mut v_h_216_: *mut LeanObject,
    mut v_outOfProof_217_: *mut LeanObject,
) -> *mut LeanObject {
    lean_inc(v_outOfProof_217_);
    return v_outOfProof_217_;
}
pub unsafe fn l_Std_Tactic_BVDecide_LRAT_Internal_Result_outOfProof_elim___boxed(
    mut v_motive_218_: *mut LeanObject,
    mut v_t_219_: *mut LeanObject,
    mut v_h_220_: *mut LeanObject,
    mut v_outOfProof_221_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_t_boxed_222_: u8 = 0;
    let mut v_res_223_: *mut LeanObject = core::ptr::null_mut();
    v_t_boxed_222_ = (lean_unbox(v_t_219_) as u8);
    v_res_223_ = l_Std_Tactic_BVDecide_LRAT_Internal_Result_outOfProof_elim(
        v_motive_218_,
        v_t_boxed_222_,
        v_h_220_,
        v_outOfProof_221_,
    );
    lean_dec(v_outOfProof_221_);
    return v_res_223_;
}
pub unsafe fn l_Std_Tactic_BVDecide_LRAT_Internal_Result_rupFailure_elim___redArg(
    mut v_rupFailure_224_: *mut LeanObject,
) -> *mut LeanObject {
    lean_inc(v_rupFailure_224_);
    return v_rupFailure_224_;
}
pub unsafe fn l_Std_Tactic_BVDecide_LRAT_Internal_Result_rupFailure_elim___redArg___boxed(
    mut v_rupFailure_225_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_226_: *mut LeanObject = core::ptr::null_mut();
    v_res_226_ =
        l_Std_Tactic_BVDecide_LRAT_Internal_Result_rupFailure_elim___redArg(v_rupFailure_225_);
    lean_dec(v_rupFailure_225_);
    return v_res_226_;
}
pub unsafe fn l_Std_Tactic_BVDecide_LRAT_Internal_Result_rupFailure_elim(
    mut v_motive_227_: *mut LeanObject,
    mut v_t_228_: u8,
    mut v_h_229_: *mut LeanObject,
    mut v_rupFailure_230_: *mut LeanObject,
) -> *mut LeanObject {
    lean_inc(v_rupFailure_230_);
    return v_rupFailure_230_;
}
pub unsafe fn l_Std_Tactic_BVDecide_LRAT_Internal_Result_rupFailure_elim___boxed(
    mut v_motive_231_: *mut LeanObject,
    mut v_t_232_: *mut LeanObject,
    mut v_h_233_: *mut LeanObject,
    mut v_rupFailure_234_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_t_boxed_235_: u8 = 0;
    let mut v_res_236_: *mut LeanObject = core::ptr::null_mut();
    v_t_boxed_235_ = (lean_unbox(v_t_232_) as u8);
    v_res_236_ = l_Std_Tactic_BVDecide_LRAT_Internal_Result_rupFailure_elim(
        v_motive_231_,
        v_t_boxed_235_,
        v_h_233_,
        v_rupFailure_234_,
    );
    lean_dec(v_rupFailure_234_);
    return v_res_236_;
}
pub unsafe fn _init_l_Std_Tactic_BVDecide_LRAT_Internal_instInhabitedResult_default() -> u8 {
    let mut v___x_237_: u8 = 0;
    v___x_237_ = 0;
    return v___x_237_;
}
pub unsafe fn _init_l_Std_Tactic_BVDecide_LRAT_Internal_instInhabitedResult() -> u8 {
    let mut v___x_238_: u8 = 0;
    v___x_238_ = 0;
    return v___x_238_;
}
pub unsafe fn l_Std_Tactic_BVDecide_LRAT_Internal_Result_ofNat(
    mut v_n_239_: *mut LeanObject,
) -> u8 {
    let mut v___x_240_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_241_: u8 = 0;
    v___x_240_ = lean_unsigned_to_nat(0);
    v___x_241_ = lean_nat_dec_le(v_n_239_, v___x_240_);
    if v___x_241_ == 0 {
        let mut v___x_242_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_243_: u8 = 0;
        v___x_242_ = lean_unsigned_to_nat(1);
        v___x_243_ = lean_nat_dec_le(v_n_239_, v___x_242_);
        if v___x_243_ == 0 {
            let mut v___x_244_: u8 = 0;
            v___x_244_ = 2;
            return v___x_244_;
        } else {
            let mut v___x_245_: u8 = 0;
            v___x_245_ = 1;
            return v___x_245_;
        }
    } else {
        let mut v___x_246_: u8 = 0;
        v___x_246_ = 0;
        return v___x_246_;
    }
}
pub unsafe fn l_Std_Tactic_BVDecide_LRAT_Internal_Result_ofNat___boxed(
    mut v_n_247_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_248_: u8 = 0;
    let mut v_r_249_: *mut LeanObject = core::ptr::null_mut();
    v_res_248_ = l_Std_Tactic_BVDecide_LRAT_Internal_Result_ofNat(v_n_247_);
    lean_dec(v_n_247_);
    v_r_249_ = lean_box((v_res_248_) as usize);
    return v_r_249_;
}
pub unsafe fn l_Std_Tactic_BVDecide_LRAT_Internal_instDecidableEqResult(
    mut v_x_250_: u8,
    mut v_y_251_: u8,
) -> u8 {
    let mut v___x_252_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_253_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_254_: u8 = 0;
    v___x_252_ = l_Std_Tactic_BVDecide_LRAT_Internal_Result_ctorIdx(v_x_250_);
    v___x_253_ = l_Std_Tactic_BVDecide_LRAT_Internal_Result_ctorIdx(v_y_251_);
    v___x_254_ = lean_nat_dec_eq(v___x_252_, v___x_253_);
    lean_dec(v___x_253_);
    lean_dec(v___x_252_);
    return v___x_254_;
}
pub unsafe fn l_Std_Tactic_BVDecide_LRAT_Internal_instDecidableEqResult___boxed(
    mut v_x_255_: *mut LeanObject,
    mut v_y_256_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_x_13__boxed_257_: u8 = 0;
    let mut v_y_14__boxed_258_: u8 = 0;
    let mut v_res_259_: u8 = 0;
    let mut v_r_260_: *mut LeanObject = core::ptr::null_mut();
    v_x_13__boxed_257_ = (lean_unbox(v_x_255_) as u8);
    v_y_14__boxed_258_ = (lean_unbox(v_y_256_) as u8);
    v_res_259_ = l_Std_Tactic_BVDecide_LRAT_Internal_instDecidableEqResult(
        v_x_13__boxed_257_,
        v_y_14__boxed_258_,
    );
    v_r_260_ = lean_box((v_res_259_) as usize);
    return v_r_260_;
}
pub unsafe fn l_Std_Tactic_BVDecide_LRAT_Internal_instToStringResult___lam__0(
    mut v_x_264_: u8,
) -> *mut LeanObject {
    match v_x_264_ {
        0 => {
            let mut v___x_265_: *mut LeanObject = core::ptr::null_mut();
            v___x_265_ =
                l_Std_Tactic_BVDecide_LRAT_Internal_instToStringResult___lam__0___closed__0;
            return v___x_265_;
        }
        1 => {
            let mut v___x_266_: *mut LeanObject = core::ptr::null_mut();
            v___x_266_ =
                l_Std_Tactic_BVDecide_LRAT_Internal_instToStringResult___lam__0___closed__1;
            return v___x_266_;
        }
        _ => {
            let mut v___x_267_: *mut LeanObject = core::ptr::null_mut();
            v___x_267_ =
                l_Std_Tactic_BVDecide_LRAT_Internal_instToStringResult___lam__0___closed__2;
            return v___x_267_;
        }
    }
}
pub unsafe fn l_Std_Tactic_BVDecide_LRAT_Internal_instToStringResult___lam__0___boxed(
    mut v_x_268_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_x_36__boxed_269_: u8 = 0;
    let mut v_res_270_: *mut LeanObject = core::ptr::null_mut();
    v_x_36__boxed_269_ = (lean_unbox(v_x_268_) as u8);
    v_res_270_ =
        l_Std_Tactic_BVDecide_LRAT_Internal_instToStringResult___lam__0(v_x_36__boxed_269_);
    return v_res_270_;
}
pub unsafe fn l_Std_Tactic_BVDecide_LRAT_Internal_lratChecker___redArg(
    mut v_inst_273_: *mut LeanObject,
    mut v_inst_274_: *mut LeanObject,
    mut v_f_275_: *mut LeanObject,
    mut v_prf_276_: *mut LeanObject,
) -> u8 {
    let mut v___x_277_: u8 = 0;
    let mut v_head_278_: *mut LeanObject = core::ptr::null_mut();
    let mut v_rupHints_279_: *mut LeanObject = core::ptr::null_mut();
    let mut v_performRupAdd_280_: *mut LeanObject = core::ptr::null_mut();
    let mut v_empty_281_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_282_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_283_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_284_: u8 = 0;
    let mut v___x_285_: u8 = 0;
    let mut v___x_286_: u8 = 0;
    let mut v_tail_287_: *mut LeanObject = core::ptr::null_mut();
    let mut v_c_288_: *mut LeanObject = core::ptr::null_mut();
    let mut v_rupHints_289_: *mut LeanObject = core::ptr::null_mut();
    let mut v_performRupAdd_290_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_291_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_292_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_293_: u8 = 0;
    let mut v___x_294_: u8 = 0;
    let mut v_fst_295_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_297_: *mut LeanObject = core::ptr::null_mut();
    let mut v_c_298_: *mut LeanObject = core::ptr::null_mut();
    let mut v_pivot_299_: *mut LeanObject = core::ptr::null_mut();
    let mut v_rupHints_300_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ratHints_301_: *mut LeanObject = core::ptr::null_mut();
    let mut v_performRatAdd_302_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_303_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_304_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_305_: u8 = 0;
    let mut v___x_306_: u8 = 0;
    let mut v_fst_307_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_309_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ids_310_: *mut LeanObject = core::ptr::null_mut();
    let mut v_delete_311_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_312_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_prf_276_) == 0 {
                    lean_dec(v_f_275_);
                    lean_dec_ref(v_inst_274_);
                    lean_dec_ref(v_inst_273_);
                    v___x_277_ = 1;
                    return v___x_277_;
                } else {
                    v_head_278_ = lean_ctor_get(v_prf_276_, 0);
                    lean_inc(v_head_278_);
                    match lean_obj_tag(v_head_278_) {
                        0 => {
                            lean_dec_ref_known(v_prf_276_, 2);
                            v_rupHints_279_ = lean_ctor_get(v_head_278_, 1);
                            lean_inc_ref(v_rupHints_279_);
                            lean_dec_ref_known(v_head_278_, 2);
                            v_performRupAdd_280_ = lean_ctor_get(v_inst_274_, 4);
                            lean_inc_ref(v_performRupAdd_280_);
                            lean_dec_ref(v_inst_274_);
                            v_empty_281_ = lean_ctor_get(v_inst_273_, 2);
                            lean_inc(v_empty_281_);
                            lean_dec_ref(v_inst_273_);
                            v___x_282_ = lean_apply_3(
                                v_performRupAdd_280_,
                                v_f_275_,
                                v_empty_281_,
                                v_rupHints_279_,
                            );
                            v_snd_283_ = lean_ctor_get(v___x_282_, 1);
                            lean_inc(v_snd_283_);
                            lean_dec_ref(v___x_282_);
                            v___x_284_ = (lean_unbox(v_snd_283_) as u8);
                            lean_dec(v_snd_283_);
                            if v___x_284_ == 0 {
                                v___x_285_ = 2;
                                return v___x_285_;
                            } else {
                                v___x_286_ = 0;
                                return v___x_286_;
                            }
                        }
                        1 => {
                            v_tail_287_ = lean_ctor_get(v_prf_276_, 1);
                            lean_inc(v_tail_287_);
                            lean_dec_ref_known(v_prf_276_, 2);
                            v_c_288_ = lean_ctor_get(v_head_278_, 1);
                            lean_inc(v_c_288_);
                            v_rupHints_289_ = lean_ctor_get(v_head_278_, 2);
                            lean_inc_ref(v_rupHints_289_);
                            lean_dec_ref_known(v_head_278_, 3);
                            v_performRupAdd_290_ = lean_ctor_get(v_inst_274_, 4);
                            lean_inc_ref(v_performRupAdd_290_);
                            v___x_291_ = lean_apply_3(
                                v_performRupAdd_290_,
                                v_f_275_,
                                v_c_288_,
                                v_rupHints_289_,
                            );
                            v_snd_292_ = lean_ctor_get(v___x_291_, 1);
                            lean_inc(v_snd_292_);
                            v___x_293_ = (lean_unbox(v_snd_292_) as u8);
                            lean_dec(v_snd_292_);
                            if v___x_293_ == 0 {
                                lean_dec_ref(v___x_291_);
                                lean_dec(v_tail_287_);
                                lean_dec_ref(v_inst_274_);
                                lean_dec_ref(v_inst_273_);
                                v___x_294_ = 2;
                                return v___x_294_;
                            } else {
                                v_fst_295_ = lean_ctor_get(v___x_291_, 0);
                                lean_inc(v_fst_295_);
                                lean_dec_ref(v___x_291_);
                                v_f_275_ = v_fst_295_;
                                v_prf_276_ = v_tail_287_;
                                state = 0;
                                continue;
                            }
                        }
                        2 => {
                            v_tail_297_ = lean_ctor_get(v_prf_276_, 1);
                            lean_inc(v_tail_297_);
                            lean_dec_ref_known(v_prf_276_, 2);
                            v_c_298_ = lean_ctor_get(v_head_278_, 1);
                            lean_inc(v_c_298_);
                            v_pivot_299_ = lean_ctor_get(v_head_278_, 2);
                            lean_inc_ref(v_pivot_299_);
                            v_rupHints_300_ = lean_ctor_get(v_head_278_, 3);
                            lean_inc_ref(v_rupHints_300_);
                            v_ratHints_301_ = lean_ctor_get(v_head_278_, 4);
                            lean_inc_ref(v_ratHints_301_);
                            lean_dec_ref_known(v_head_278_, 5);
                            v_performRatAdd_302_ = lean_ctor_get(v_inst_274_, 5);
                            lean_inc_ref(v_performRatAdd_302_);
                            v___x_303_ = lean_apply_5(
                                v_performRatAdd_302_,
                                v_f_275_,
                                v_c_298_,
                                v_pivot_299_,
                                v_rupHints_300_,
                                v_ratHints_301_,
                            );
                            v_snd_304_ = lean_ctor_get(v___x_303_, 1);
                            lean_inc(v_snd_304_);
                            v___x_305_ = (lean_unbox(v_snd_304_) as u8);
                            lean_dec(v_snd_304_);
                            if v___x_305_ == 0 {
                                lean_dec_ref(v___x_303_);
                                lean_dec(v_tail_297_);
                                lean_dec_ref(v_inst_274_);
                                lean_dec_ref(v_inst_273_);
                                v___x_306_ = 2;
                                return v___x_306_;
                            } else {
                                v_fst_307_ = lean_ctor_get(v___x_303_, 0);
                                lean_inc(v_fst_307_);
                                lean_dec_ref(v___x_303_);
                                v_f_275_ = v_fst_307_;
                                v_prf_276_ = v_tail_297_;
                                state = 0;
                                continue;
                            }
                        }
                        _ => {
                            v_tail_309_ = lean_ctor_get(v_prf_276_, 1);
                            lean_inc(v_tail_309_);
                            lean_dec_ref_known(v_prf_276_, 2);
                            v_ids_310_ = lean_ctor_get(v_head_278_, 0);
                            lean_inc_ref(v_ids_310_);
                            lean_dec_ref_known(v_head_278_, 1);
                            v_delete_311_ = lean_ctor_get(v_inst_274_, 3);
                            lean_inc(v_delete_311_);
                            v___x_312_ = lean_apply_2(v_delete_311_, v_f_275_, v_ids_310_);
                            v_f_275_ = v___x_312_;
                            v_prf_276_ = v_tail_309_;
                            state = 0;
                            continue;
                        }
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Tactic_BVDecide_LRAT_Internal_lratChecker___redArg___boxed(
    mut v_inst_314_: *mut LeanObject,
    mut v_inst_315_: *mut LeanObject,
    mut v_f_316_: *mut LeanObject,
    mut v_prf_317_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_318_: u8 = 0;
    let mut v_r_319_: *mut LeanObject = core::ptr::null_mut();
    v_res_318_ = l_Std_Tactic_BVDecide_LRAT_Internal_lratChecker___redArg(
        v_inst_314_,
        v_inst_315_,
        v_f_316_,
        v_prf_317_,
    );
    v_r_319_ = lean_box((v_res_318_) as usize);
    return v_r_319_;
}
pub unsafe fn l_Std_Tactic_BVDecide_LRAT_Internal_lratChecker(
    mut v_00_u03b1_320_: *mut LeanObject,
    mut v_00_u03b2_321_: *mut LeanObject,
    mut v_00_u03c3_322_: *mut LeanObject,
    mut v_inst_323_: *mut LeanObject,
    mut v_inst_324_: *mut LeanObject,
    mut v_inst_325_: *mut LeanObject,
    mut v_inst_326_: *mut LeanObject,
    mut v_f_327_: *mut LeanObject,
    mut v_prf_328_: *mut LeanObject,
) -> u8 {
    let mut v___x_329_: u8 = 0;
    v___x_329_ = l_Std_Tactic_BVDecide_LRAT_Internal_lratChecker___redArg(
        v_inst_324_,
        v_inst_326_,
        v_f_327_,
        v_prf_328_,
    );
    return v___x_329_;
}
pub unsafe fn l_Std_Tactic_BVDecide_LRAT_Internal_lratChecker___boxed(
    mut v_00_u03b1_330_: *mut LeanObject,
    mut v_00_u03b2_331_: *mut LeanObject,
    mut v_00_u03c3_332_: *mut LeanObject,
    mut v_inst_333_: *mut LeanObject,
    mut v_inst_334_: *mut LeanObject,
    mut v_inst_335_: *mut LeanObject,
    mut v_inst_336_: *mut LeanObject,
    mut v_f_337_: *mut LeanObject,
    mut v_prf_338_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_339_: u8 = 0;
    let mut v_r_340_: *mut LeanObject = core::ptr::null_mut();
    v_res_339_ = l_Std_Tactic_BVDecide_LRAT_Internal_lratChecker(
        v_00_u03b1_330_,
        v_00_u03b2_331_,
        v_00_u03c3_332_,
        v_inst_333_,
        v_inst_334_,
        v_inst_335_,
        v_inst_336_,
        v_f_337_,
        v_prf_338_,
    );
    lean_dec_ref(v_inst_333_);
    v_r_340_ = lean_box((v_res_339_) as usize);
    return v_r_340_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Std_Tactic_BVDecide_LRAT_Internal_LRATChecker(
    builtin: u8,
) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Std_Tactic_BVDecide_LRAT_Actions(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Std_Tactic_BVDecide_LRAT_Internal_Formula_Class(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    l_Std_Tactic_BVDecide_LRAT_Internal_instInhabitedResult_default =
        _init_l_Std_Tactic_BVDecide_LRAT_Internal_instInhabitedResult_default();
    l_Std_Tactic_BVDecide_LRAT_Internal_instInhabitedResult =
        _init_l_Std_Tactic_BVDecide_LRAT_Internal_instInhabitedResult();
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Std_Tactic_BVDecide_LRAT_Internal_LRATChecker(
    builtin: u8,
) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_meta_initialized = true;
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Std_Tactic_BVDecide_LRAT_Internal_LRATChecker(
    builtin: u8,
) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Std_Tactic_BVDecide_LRAT_Actions(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Std_Tactic_BVDecide_LRAT_Internal_Formula_Class(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Std_Tactic_BVDecide_LRAT_Internal_LRATChecker(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Std_Tactic_BVDecide_LRAT_Internal_LRATChecker(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Std_Tactic_BVDecide_LRAT_Internal_LRATChecker(builtin);
}
