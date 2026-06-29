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
use crate::ffi::{lean_nat_dec_eq, lean_nat_dec_le};
pub static mut l_Std_Tactic_BVDecide_LRAT_Internal_instInhabitedResult_default: u8 = 0;
pub static mut l_Std_Tactic_BVDecide_LRAT_Internal_instInhabitedResult: u8 = 0;
pub static l_Std_Tactic_BVDecide_LRAT_Internal_instToStringResult___lam__0___closed__0_value:
    crate::leanh::LeanStringObject<8> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Std_Tactic_BVDecide_LRAT_Internal_instToStringResult___lam__0___closed__0_value
) as *mut crate::leanh::LeanObject;
pub static l_Std_Tactic_BVDecide_LRAT_Internal_instToStringResult___lam__0___closed__1_value:
    crate::leanh::LeanStringObject<13> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Std_Tactic_BVDecide_LRAT_Internal_instToStringResult___lam__0___closed__1_value
) as *mut crate::leanh::LeanObject;
pub static l_Std_Tactic_BVDecide_LRAT_Internal_instToStringResult___lam__0___closed__2_value:
    crate::leanh::LeanStringObject<12> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Std_Tactic_BVDecide_LRAT_Internal_instToStringResult___lam__0___closed__2_value
) as *mut crate::leanh::LeanObject;
pub static l_Std_Tactic_BVDecide_LRAT_Internal_instToStringResult___closed__0_value:
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
    m_fun: l_Std_Tactic_BVDecide_LRAT_Internal_instToStringResult___lam__0___boxed
        as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_Tactic_BVDecide_LRAT_Internal_instToStringResult___closed__0:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Tactic_BVDecide_LRAT_Internal_instToStringResult___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Std_Tactic_BVDecide_LRAT_Internal_instToStringResult:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Tactic_BVDecide_LRAT_Internal_instToStringResult___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub unsafe fn l_Std_Tactic_BVDecide_LRAT_Internal_Result_ctorIdx(
    mut v_x_171_: u8,
) -> *mut crate::leanh::LeanObject {
    match v_x_171_ {
        0 => {
            let mut v___x_172_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_172_ = crate::leanh::lean_unsigned_to_nat(0);
            return v___x_172_;
        }
        1 => {
            let mut v___x_173_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_173_ = crate::leanh::lean_unsigned_to_nat(1);
            return v___x_173_;
        }
        _ => {
            let mut v___x_174_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_174_ = crate::leanh::lean_unsigned_to_nat(2);
            return v___x_174_;
        }
    }
}
pub unsafe fn l_Std_Tactic_BVDecide_LRAT_Internal_Result_ctorIdx___boxed(
    mut v_x_175_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x_boxed_176_: u8 = 0;
    let mut v_res_177_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_x_boxed_176_ = (crate::leanh::lean_unbox(v_x_175_) as u8);
    v_res_177_ = l_Std_Tactic_BVDecide_LRAT_Internal_Result_ctorIdx(v_x_boxed_176_);
    return v_res_177_;
}
pub unsafe fn l_Std_Tactic_BVDecide_LRAT_Internal_Result_toCtorIdx(
    mut v_x_178_: u8,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_179_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_179_ = l_Std_Tactic_BVDecide_LRAT_Internal_Result_ctorIdx(v_x_178_);
    return v___x_179_;
}
pub unsafe fn l_Std_Tactic_BVDecide_LRAT_Internal_Result_toCtorIdx___boxed(
    mut v_x_180_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x_4__boxed_181_: u8 = 0;
    let mut v_res_182_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_x_4__boxed_181_ = (crate::leanh::lean_unbox(v_x_180_) as u8);
    v_res_182_ = l_Std_Tactic_BVDecide_LRAT_Internal_Result_toCtorIdx(v_x_4__boxed_181_);
    return v_res_182_;
}
pub unsafe fn l_Std_Tactic_BVDecide_LRAT_Internal_Result_ctorElim___redArg(
    mut v_k_183_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_k_183_);
    return v_k_183_;
}
pub unsafe fn l_Std_Tactic_BVDecide_LRAT_Internal_Result_ctorElim___redArg___boxed(
    mut v_k_184_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_185_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_185_ = l_Std_Tactic_BVDecide_LRAT_Internal_Result_ctorElim___redArg(v_k_184_);
    crate::leanh::lean_dec(v_k_184_);
    return v_res_185_;
}
pub unsafe fn l_Std_Tactic_BVDecide_LRAT_Internal_Result_ctorElim(
    mut v_motive_186_: *mut crate::leanh::LeanObject,
    mut v_ctorIdx_187_: *mut crate::leanh::LeanObject,
    mut v_t_188_: u8,
    mut v_h_189_: *mut crate::leanh::LeanObject,
    mut v_k_190_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_k_190_);
    return v_k_190_;
}
pub unsafe fn l_Std_Tactic_BVDecide_LRAT_Internal_Result_ctorElim___boxed(
    mut v_motive_191_: *mut crate::leanh::LeanObject,
    mut v_ctorIdx_192_: *mut crate::leanh::LeanObject,
    mut v_t_193_: *mut crate::leanh::LeanObject,
    mut v_h_194_: *mut crate::leanh::LeanObject,
    mut v_k_195_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_t_boxed_196_: u8 = 0;
    let mut v_res_197_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_t_boxed_196_ = (crate::leanh::lean_unbox(v_t_193_) as u8);
    v_res_197_ = l_Std_Tactic_BVDecide_LRAT_Internal_Result_ctorElim(
        v_motive_191_,
        v_ctorIdx_192_,
        v_t_boxed_196_,
        v_h_194_,
        v_k_195_,
    );
    crate::leanh::lean_dec(v_k_195_);
    crate::leanh::lean_dec(v_ctorIdx_192_);
    return v_res_197_;
}
pub unsafe fn l_Std_Tactic_BVDecide_LRAT_Internal_Result_success_elim___redArg(
    mut v_success_198_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_success_198_);
    return v_success_198_;
}
pub unsafe fn l_Std_Tactic_BVDecide_LRAT_Internal_Result_success_elim___redArg___boxed(
    mut v_success_199_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_200_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_200_ = l_Std_Tactic_BVDecide_LRAT_Internal_Result_success_elim___redArg(v_success_199_);
    crate::leanh::lean_dec(v_success_199_);
    return v_res_200_;
}
pub unsafe fn l_Std_Tactic_BVDecide_LRAT_Internal_Result_success_elim(
    mut v_motive_201_: *mut crate::leanh::LeanObject,
    mut v_t_202_: u8,
    mut v_h_203_: *mut crate::leanh::LeanObject,
    mut v_success_204_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_success_204_);
    return v_success_204_;
}
pub unsafe fn l_Std_Tactic_BVDecide_LRAT_Internal_Result_success_elim___boxed(
    mut v_motive_205_: *mut crate::leanh::LeanObject,
    mut v_t_206_: *mut crate::leanh::LeanObject,
    mut v_h_207_: *mut crate::leanh::LeanObject,
    mut v_success_208_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_t_boxed_209_: u8 = 0;
    let mut v_res_210_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_t_boxed_209_ = (crate::leanh::lean_unbox(v_t_206_) as u8);
    v_res_210_ = l_Std_Tactic_BVDecide_LRAT_Internal_Result_success_elim(
        v_motive_205_,
        v_t_boxed_209_,
        v_h_207_,
        v_success_208_,
    );
    crate::leanh::lean_dec(v_success_208_);
    return v_res_210_;
}
pub unsafe fn l_Std_Tactic_BVDecide_LRAT_Internal_Result_outOfProof_elim___redArg(
    mut v_outOfProof_211_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_outOfProof_211_);
    return v_outOfProof_211_;
}
pub unsafe fn l_Std_Tactic_BVDecide_LRAT_Internal_Result_outOfProof_elim___redArg___boxed(
    mut v_outOfProof_212_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_213_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_213_ =
        l_Std_Tactic_BVDecide_LRAT_Internal_Result_outOfProof_elim___redArg(v_outOfProof_212_);
    crate::leanh::lean_dec(v_outOfProof_212_);
    return v_res_213_;
}
pub unsafe fn l_Std_Tactic_BVDecide_LRAT_Internal_Result_outOfProof_elim(
    mut v_motive_214_: *mut crate::leanh::LeanObject,
    mut v_t_215_: u8,
    mut v_h_216_: *mut crate::leanh::LeanObject,
    mut v_outOfProof_217_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_outOfProof_217_);
    return v_outOfProof_217_;
}
pub unsafe fn l_Std_Tactic_BVDecide_LRAT_Internal_Result_outOfProof_elim___boxed(
    mut v_motive_218_: *mut crate::leanh::LeanObject,
    mut v_t_219_: *mut crate::leanh::LeanObject,
    mut v_h_220_: *mut crate::leanh::LeanObject,
    mut v_outOfProof_221_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_t_boxed_222_: u8 = 0;
    let mut v_res_223_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_t_boxed_222_ = (crate::leanh::lean_unbox(v_t_219_) as u8);
    v_res_223_ = l_Std_Tactic_BVDecide_LRAT_Internal_Result_outOfProof_elim(
        v_motive_218_,
        v_t_boxed_222_,
        v_h_220_,
        v_outOfProof_221_,
    );
    crate::leanh::lean_dec(v_outOfProof_221_);
    return v_res_223_;
}
pub unsafe fn l_Std_Tactic_BVDecide_LRAT_Internal_Result_rupFailure_elim___redArg(
    mut v_rupFailure_224_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_rupFailure_224_);
    return v_rupFailure_224_;
}
pub unsafe fn l_Std_Tactic_BVDecide_LRAT_Internal_Result_rupFailure_elim___redArg___boxed(
    mut v_rupFailure_225_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_226_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_226_ =
        l_Std_Tactic_BVDecide_LRAT_Internal_Result_rupFailure_elim___redArg(v_rupFailure_225_);
    crate::leanh::lean_dec(v_rupFailure_225_);
    return v_res_226_;
}
pub unsafe fn l_Std_Tactic_BVDecide_LRAT_Internal_Result_rupFailure_elim(
    mut v_motive_227_: *mut crate::leanh::LeanObject,
    mut v_t_228_: u8,
    mut v_h_229_: *mut crate::leanh::LeanObject,
    mut v_rupFailure_230_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_rupFailure_230_);
    return v_rupFailure_230_;
}
pub unsafe fn l_Std_Tactic_BVDecide_LRAT_Internal_Result_rupFailure_elim___boxed(
    mut v_motive_231_: *mut crate::leanh::LeanObject,
    mut v_t_232_: *mut crate::leanh::LeanObject,
    mut v_h_233_: *mut crate::leanh::LeanObject,
    mut v_rupFailure_234_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_t_boxed_235_: u8 = 0;
    let mut v_res_236_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_t_boxed_235_ = (crate::leanh::lean_unbox(v_t_232_) as u8);
    v_res_236_ = l_Std_Tactic_BVDecide_LRAT_Internal_Result_rupFailure_elim(
        v_motive_231_,
        v_t_boxed_235_,
        v_h_233_,
        v_rupFailure_234_,
    );
    crate::leanh::lean_dec(v_rupFailure_234_);
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
    mut v_n_239_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_240_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_241_: u8 = 0;
    v___x_240_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_241_ = lean_nat_dec_le(v_n_239_, v___x_240_);
    if v___x_241_ == 0 {
        let mut v___x_242_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_243_: u8 = 0;
        v___x_242_ = crate::leanh::lean_unsigned_to_nat(1);
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
    mut v_n_247_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_248_: u8 = 0;
    let mut v_r_249_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_248_ = l_Std_Tactic_BVDecide_LRAT_Internal_Result_ofNat(v_n_247_);
    crate::leanh::lean_dec(v_n_247_);
    v_r_249_ = crate::leanh::lean_box((v_res_248_) as usize);
    return v_r_249_;
}
pub unsafe fn l_Std_Tactic_BVDecide_LRAT_Internal_instDecidableEqResult(
    mut v_x_250_: u8,
    mut v_y_251_: u8,
) -> u8 {
    let mut v___x_252_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_253_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_254_: u8 = 0;
    v___x_252_ = l_Std_Tactic_BVDecide_LRAT_Internal_Result_ctorIdx(v_x_250_);
    v___x_253_ = l_Std_Tactic_BVDecide_LRAT_Internal_Result_ctorIdx(v_y_251_);
    v___x_254_ = lean_nat_dec_eq(v___x_252_, v___x_253_);
    crate::leanh::lean_dec(v___x_253_);
    crate::leanh::lean_dec(v___x_252_);
    return v___x_254_;
}
pub unsafe fn l_Std_Tactic_BVDecide_LRAT_Internal_instDecidableEqResult___boxed(
    mut v_x_255_: *mut crate::leanh::LeanObject,
    mut v_y_256_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x_13__boxed_257_: u8 = 0;
    let mut v_y_14__boxed_258_: u8 = 0;
    let mut v_res_259_: u8 = 0;
    let mut v_r_260_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_x_13__boxed_257_ = (crate::leanh::lean_unbox(v_x_255_) as u8);
    v_y_14__boxed_258_ = (crate::leanh::lean_unbox(v_y_256_) as u8);
    v_res_259_ = l_Std_Tactic_BVDecide_LRAT_Internal_instDecidableEqResult(
        v_x_13__boxed_257_,
        v_y_14__boxed_258_,
    );
    v_r_260_ = crate::leanh::lean_box((v_res_259_) as usize);
    return v_r_260_;
}
pub unsafe fn l_Std_Tactic_BVDecide_LRAT_Internal_instToStringResult___lam__0(
    mut v_x_264_: u8,
) -> *mut crate::leanh::LeanObject {
    match v_x_264_ {
        0 => {
            let mut v___x_265_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_265_ =
                l_Std_Tactic_BVDecide_LRAT_Internal_instToStringResult___lam__0___closed__0;
            return v___x_265_;
        }
        1 => {
            let mut v___x_266_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_266_ =
                l_Std_Tactic_BVDecide_LRAT_Internal_instToStringResult___lam__0___closed__1;
            return v___x_266_;
        }
        _ => {
            let mut v___x_267_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_267_ =
                l_Std_Tactic_BVDecide_LRAT_Internal_instToStringResult___lam__0___closed__2;
            return v___x_267_;
        }
    }
}
pub unsafe fn l_Std_Tactic_BVDecide_LRAT_Internal_instToStringResult___lam__0___boxed(
    mut v_x_268_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x_36__boxed_269_: u8 = 0;
    let mut v_res_270_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_x_36__boxed_269_ = (crate::leanh::lean_unbox(v_x_268_) as u8);
    v_res_270_ =
        l_Std_Tactic_BVDecide_LRAT_Internal_instToStringResult___lam__0(v_x_36__boxed_269_);
    return v_res_270_;
}
pub unsafe fn l_Std_Tactic_BVDecide_LRAT_Internal_lratChecker___redArg(
    mut v_inst_273_: *mut crate::leanh::LeanObject,
    mut v_inst_274_: *mut crate::leanh::LeanObject,
    mut v_f_275_: *mut crate::leanh::LeanObject,
    mut v_prf_276_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_277_: u8 = 0;
    let mut v_head_278_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_rupHints_279_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_performRupAdd_280_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_empty_281_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_282_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_283_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_284_: u8 = 0;
    let mut v___x_285_: u8 = 0;
    let mut v___x_286_: u8 = 0;
    let mut v_tail_287_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_c_288_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_rupHints_289_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_performRupAdd_290_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_291_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_292_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_293_: u8 = 0;
    let mut v___x_294_: u8 = 0;
    let mut v_fst_295_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_297_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_c_298_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_pivot_299_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_rupHints_300_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ratHints_301_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_performRatAdd_302_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_303_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_304_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_305_: u8 = 0;
    let mut v___x_306_: u8 = 0;
    let mut v_fst_307_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_309_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ids_310_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_delete_311_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_312_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_prf_276_) == 0 {
                    crate::leanh::lean_dec(v_f_275_);
                    crate::leanh::lean_dec_ref(v_inst_274_);
                    crate::leanh::lean_dec_ref(v_inst_273_);
                    v___x_277_ = 1;
                    return v___x_277_;
                } else {
                    v_head_278_ = crate::leanh::lean_ctor_get(v_prf_276_, 0);
                    crate::leanh::lean_inc(v_head_278_);
                    match crate::leanh::lean_obj_tag(v_head_278_) {
                        0 => {
                            crate::leanh::lean_dec_ref_known(v_prf_276_, 2);
                            v_rupHints_279_ = crate::leanh::lean_ctor_get(v_head_278_, 1);
                            crate::leanh::lean_inc_ref(v_rupHints_279_);
                            crate::leanh::lean_dec_ref_known(v_head_278_, 2);
                            v_performRupAdd_280_ = crate::leanh::lean_ctor_get(v_inst_274_, 4);
                            crate::leanh::lean_inc_ref(v_performRupAdd_280_);
                            crate::leanh::lean_dec_ref(v_inst_274_);
                            v_empty_281_ = crate::leanh::lean_ctor_get(v_inst_273_, 2);
                            crate::leanh::lean_inc(v_empty_281_);
                            crate::leanh::lean_dec_ref(v_inst_273_);
                            v___x_282_ = crate::leanh::lean_apply_3(
                                v_performRupAdd_280_,
                                v_f_275_,
                                v_empty_281_,
                                v_rupHints_279_,
                            );
                            v_snd_283_ = crate::leanh::lean_ctor_get(v___x_282_, 1);
                            crate::leanh::lean_inc(v_snd_283_);
                            crate::leanh::lean_dec_ref(v___x_282_);
                            v___x_284_ = (crate::leanh::lean_unbox(v_snd_283_) as u8);
                            crate::leanh::lean_dec(v_snd_283_);
                            if v___x_284_ == 0 {
                                v___x_285_ = 2;
                                return v___x_285_;
                            } else {
                                v___x_286_ = 0;
                                return v___x_286_;
                            }
                        }
                        1 => {
                            v_tail_287_ = crate::leanh::lean_ctor_get(v_prf_276_, 1);
                            crate::leanh::lean_inc(v_tail_287_);
                            crate::leanh::lean_dec_ref_known(v_prf_276_, 2);
                            v_c_288_ = crate::leanh::lean_ctor_get(v_head_278_, 1);
                            crate::leanh::lean_inc(v_c_288_);
                            v_rupHints_289_ = crate::leanh::lean_ctor_get(v_head_278_, 2);
                            crate::leanh::lean_inc_ref(v_rupHints_289_);
                            crate::leanh::lean_dec_ref_known(v_head_278_, 3);
                            v_performRupAdd_290_ = crate::leanh::lean_ctor_get(v_inst_274_, 4);
                            crate::leanh::lean_inc_ref(v_performRupAdd_290_);
                            v___x_291_ = crate::leanh::lean_apply_3(
                                v_performRupAdd_290_,
                                v_f_275_,
                                v_c_288_,
                                v_rupHints_289_,
                            );
                            v_snd_292_ = crate::leanh::lean_ctor_get(v___x_291_, 1);
                            crate::leanh::lean_inc(v_snd_292_);
                            v___x_293_ = (crate::leanh::lean_unbox(v_snd_292_) as u8);
                            crate::leanh::lean_dec(v_snd_292_);
                            if v___x_293_ == 0 {
                                crate::leanh::lean_dec_ref(v___x_291_);
                                crate::leanh::lean_dec(v_tail_287_);
                                crate::leanh::lean_dec_ref(v_inst_274_);
                                crate::leanh::lean_dec_ref(v_inst_273_);
                                v___x_294_ = 2;
                                return v___x_294_;
                            } else {
                                v_fst_295_ = crate::leanh::lean_ctor_get(v___x_291_, 0);
                                crate::leanh::lean_inc(v_fst_295_);
                                crate::leanh::lean_dec_ref(v___x_291_);
                                v_f_275_ = v_fst_295_;
                                v_prf_276_ = v_tail_287_;
                                state = 0;
                                continue;
                            }
                        }
                        2 => {
                            v_tail_297_ = crate::leanh::lean_ctor_get(v_prf_276_, 1);
                            crate::leanh::lean_inc(v_tail_297_);
                            crate::leanh::lean_dec_ref_known(v_prf_276_, 2);
                            v_c_298_ = crate::leanh::lean_ctor_get(v_head_278_, 1);
                            crate::leanh::lean_inc(v_c_298_);
                            v_pivot_299_ = crate::leanh::lean_ctor_get(v_head_278_, 2);
                            crate::leanh::lean_inc_ref(v_pivot_299_);
                            v_rupHints_300_ = crate::leanh::lean_ctor_get(v_head_278_, 3);
                            crate::leanh::lean_inc_ref(v_rupHints_300_);
                            v_ratHints_301_ = crate::leanh::lean_ctor_get(v_head_278_, 4);
                            crate::leanh::lean_inc_ref(v_ratHints_301_);
                            crate::leanh::lean_dec_ref_known(v_head_278_, 5);
                            v_performRatAdd_302_ = crate::leanh::lean_ctor_get(v_inst_274_, 5);
                            crate::leanh::lean_inc_ref(v_performRatAdd_302_);
                            v___x_303_ = crate::leanh::lean_apply_5(
                                v_performRatAdd_302_,
                                v_f_275_,
                                v_c_298_,
                                v_pivot_299_,
                                v_rupHints_300_,
                                v_ratHints_301_,
                            );
                            v_snd_304_ = crate::leanh::lean_ctor_get(v___x_303_, 1);
                            crate::leanh::lean_inc(v_snd_304_);
                            v___x_305_ = (crate::leanh::lean_unbox(v_snd_304_) as u8);
                            crate::leanh::lean_dec(v_snd_304_);
                            if v___x_305_ == 0 {
                                crate::leanh::lean_dec_ref(v___x_303_);
                                crate::leanh::lean_dec(v_tail_297_);
                                crate::leanh::lean_dec_ref(v_inst_274_);
                                crate::leanh::lean_dec_ref(v_inst_273_);
                                v___x_306_ = 2;
                                return v___x_306_;
                            } else {
                                v_fst_307_ = crate::leanh::lean_ctor_get(v___x_303_, 0);
                                crate::leanh::lean_inc(v_fst_307_);
                                crate::leanh::lean_dec_ref(v___x_303_);
                                v_f_275_ = v_fst_307_;
                                v_prf_276_ = v_tail_297_;
                                state = 0;
                                continue;
                            }
                        }
                        _ => {
                            v_tail_309_ = crate::leanh::lean_ctor_get(v_prf_276_, 1);
                            crate::leanh::lean_inc(v_tail_309_);
                            crate::leanh::lean_dec_ref_known(v_prf_276_, 2);
                            v_ids_310_ = crate::leanh::lean_ctor_get(v_head_278_, 0);
                            crate::leanh::lean_inc_ref(v_ids_310_);
                            crate::leanh::lean_dec_ref_known(v_head_278_, 1);
                            v_delete_311_ = crate::leanh::lean_ctor_get(v_inst_274_, 3);
                            crate::leanh::lean_inc(v_delete_311_);
                            v___x_312_ =
                                crate::leanh::lean_apply_2(v_delete_311_, v_f_275_, v_ids_310_);
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
    mut v_inst_314_: *mut crate::leanh::LeanObject,
    mut v_inst_315_: *mut crate::leanh::LeanObject,
    mut v_f_316_: *mut crate::leanh::LeanObject,
    mut v_prf_317_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_318_: u8 = 0;
    let mut v_r_319_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_318_ = l_Std_Tactic_BVDecide_LRAT_Internal_lratChecker___redArg(
        v_inst_314_,
        v_inst_315_,
        v_f_316_,
        v_prf_317_,
    );
    v_r_319_ = crate::leanh::lean_box((v_res_318_) as usize);
    return v_r_319_;
}
pub unsafe fn l_Std_Tactic_BVDecide_LRAT_Internal_lratChecker(
    mut v_00_u03b1_320_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_321_: *mut crate::leanh::LeanObject,
    mut v_00_u03c3_322_: *mut crate::leanh::LeanObject,
    mut v_inst_323_: *mut crate::leanh::LeanObject,
    mut v_inst_324_: *mut crate::leanh::LeanObject,
    mut v_inst_325_: *mut crate::leanh::LeanObject,
    mut v_inst_326_: *mut crate::leanh::LeanObject,
    mut v_f_327_: *mut crate::leanh::LeanObject,
    mut v_prf_328_: *mut crate::leanh::LeanObject,
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
    mut v_00_u03b1_330_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_331_: *mut crate::leanh::LeanObject,
    mut v_00_u03c3_332_: *mut crate::leanh::LeanObject,
    mut v_inst_333_: *mut crate::leanh::LeanObject,
    mut v_inst_334_: *mut crate::leanh::LeanObject,
    mut v_inst_335_: *mut crate::leanh::LeanObject,
    mut v_inst_336_: *mut crate::leanh::LeanObject,
    mut v_f_337_: *mut crate::leanh::LeanObject,
    mut v_prf_338_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_339_: u8 = 0;
    let mut v_r_340_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
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
    crate::leanh::lean_dec_ref(v_inst_333_);
    v_r_340_ = crate::leanh::lean_box((v_res_339_) as usize);
    return v_r_340_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Std_Tactic_BVDecide_LRAT_Internal_LRATChecker(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Std_Tactic_BVDecide_LRAT_Actions(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Std_Tactic_BVDecide_LRAT_Internal_Formula_Class(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    l_Std_Tactic_BVDecide_LRAT_Internal_instInhabitedResult_default =
        _init_l_Std_Tactic_BVDecide_LRAT_Internal_instInhabitedResult_default();
    l_Std_Tactic_BVDecide_LRAT_Internal_instInhabitedResult =
        _init_l_Std_Tactic_BVDecide_LRAT_Internal_instInhabitedResult();
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Std_Tactic_BVDecide_LRAT_Internal_LRATChecker(
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
pub unsafe fn initialize_Std_Tactic_BVDecide_LRAT_Internal_LRATChecker(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Std_Tactic_BVDecide_LRAT_Actions(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Std_Tactic_BVDecide_LRAT_Internal_Formula_Class(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Std_Tactic_BVDecide_LRAT_Internal_LRATChecker(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Std_Tactic_BVDecide_LRAT_Internal_LRATChecker(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Std_Tactic_BVDecide_LRAT_Internal_LRATChecker(builtin);
}
