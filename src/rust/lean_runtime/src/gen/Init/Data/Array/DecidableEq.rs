// Lean compiler output
// Module: Init.Data.Array.DecidableEq
// Imports: Init.Data.Array.Basic Init.Data.Array.Basic Init.Data.Nat.Lemmas Init.ByCases Init.Classical Init.Data.BEq Init.Data.Bool Init.Data.List.Nat.BEq Init.RCases
use crate::r#gen::Init::ByCases::{initialize_Init_ByCases, runtime_initialize_Init_ByCases};
use crate::r#gen::Init::Classical::{initialize_Init_Classical, runtime_initialize_Init_Classical};
use crate::r#gen::Init::Data::Array::Basic::{
    initialize_Init_Data_Array_Basic, l_Array_isEqvAux___redArg,
    runtime_initialize_Init_Data_Array_Basic,
};
use crate::r#gen::Init::Data::BEq::{initialize_Init_Data_BEq, runtime_initialize_Init_Data_BEq};
use crate::r#gen::Init::Data::Bool::{
    initialize_Init_Data_Bool, runtime_initialize_Init_Data_Bool,
};
use crate::r#gen::Init::Data::List::Nat::BEq::{
    initialize_Init_Data_List_Nat_BEq, runtime_initialize_Init_Data_List_Nat_BEq,
};
use crate::r#gen::Init::Data::Nat::Lemmas::{
    initialize_Init_Data_Nat_Lemmas, runtime_initialize_Init_Data_Nat_Lemmas,
};
use crate::r#gen::Init::RCases::{initialize_Init_RCases, runtime_initialize_Init_RCases};
use crate::lean_imports_rs::Init::Prelude::{
    lean_array_get_size, lean_array_to_list, lean_nat_dec_eq, lean_nat_sub,
};
pub unsafe fn l___private_Init_Data_Array_DecidableEq_0__Array_isEqvAux_match__1_splitter___redArg(
    mut v_x_155_: *mut crate::leanh::LeanObject,
    mut v_h__1_156_: *mut crate::leanh::LeanObject,
    mut v_h__2_157_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_zero_158_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isZero_159_: u8 = 0;
    v_zero_158_ = crate::leanh::lean_unsigned_to_nat(0);
    v_isZero_159_ = lean_nat_dec_eq(v_x_155_, v_zero_158_);
    if v_isZero_159_ == 1 {
        let mut v___x_160_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_157_);
        v___x_160_ = crate::leanh::lean_apply_1(v_h__1_156_, crate::leanh::lean_box(0));
        return v___x_160_;
    } else {
        let mut v_one_161_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_n_162_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_163_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_156_);
        v_one_161_ = crate::leanh::lean_unsigned_to_nat(1);
        v_n_162_ = lean_nat_sub(v_x_155_, v_one_161_);
        v___x_163_ = crate::leanh::lean_apply_2(v_h__2_157_, v_n_162_, crate::leanh::lean_box(0));
        return v___x_163_;
    }
}
pub unsafe fn l___private_Init_Data_Array_DecidableEq_0__Array_isEqvAux_match__1_splitter___redArg___boxed(
    mut v_x_164_: *mut crate::leanh::LeanObject,
    mut v_h__1_165_: *mut crate::leanh::LeanObject,
    mut v_h__2_166_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_167_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_167_ =
        l___private_Init_Data_Array_DecidableEq_0__Array_isEqvAux_match__1_splitter___redArg(
            v_x_164_,
            v_h__1_165_,
            v_h__2_166_,
        );
    crate::leanh::lean_dec(v_x_164_);
    return v_res_167_;
}
pub unsafe fn l___private_Init_Data_Array_DecidableEq_0__Array_isEqvAux_match__1_splitter(
    mut v_00_u03b1_168_: *mut crate::leanh::LeanObject,
    mut v_xs_169_: *mut crate::leanh::LeanObject,
    mut v_motive_170_: *mut crate::leanh::LeanObject,
    mut v_x_171_: *mut crate::leanh::LeanObject,
    mut v_x_172_: *mut crate::leanh::LeanObject,
    mut v_h__1_173_: *mut crate::leanh::LeanObject,
    mut v_h__2_174_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_zero_175_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isZero_176_: u8 = 0;
    v_zero_175_ = crate::leanh::lean_unsigned_to_nat(0);
    v_isZero_176_ = lean_nat_dec_eq(v_x_171_, v_zero_175_);
    if v_isZero_176_ == 1 {
        let mut v___x_177_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_174_);
        v___x_177_ = crate::leanh::lean_apply_1(v_h__1_173_, crate::leanh::lean_box(0));
        return v___x_177_;
    } else {
        let mut v_one_178_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_n_179_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_180_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_173_);
        v_one_178_ = crate::leanh::lean_unsigned_to_nat(1);
        v_n_179_ = lean_nat_sub(v_x_171_, v_one_178_);
        v___x_180_ = crate::leanh::lean_apply_2(v_h__2_174_, v_n_179_, crate::leanh::lean_box(0));
        return v___x_180_;
    }
}
pub unsafe fn l___private_Init_Data_Array_DecidableEq_0__Array_isEqvAux_match__1_splitter___boxed(
    mut v_00_u03b1_181_: *mut crate::leanh::LeanObject,
    mut v_xs_182_: *mut crate::leanh::LeanObject,
    mut v_motive_183_: *mut crate::leanh::LeanObject,
    mut v_x_184_: *mut crate::leanh::LeanObject,
    mut v_x_185_: *mut crate::leanh::LeanObject,
    mut v_h__1_186_: *mut crate::leanh::LeanObject,
    mut v_h__2_187_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_188_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_188_ = l___private_Init_Data_Array_DecidableEq_0__Array_isEqvAux_match__1_splitter(
        v_00_u03b1_181_,
        v_xs_182_,
        v_motive_183_,
        v_x_184_,
        v_x_185_,
        v_h__1_186_,
        v_h__2_187_,
    );
    crate::leanh::lean_dec(v_x_184_);
    crate::leanh::lean_dec_ref(v_xs_182_);
    return v_res_188_;
}
pub unsafe fn l_Array_instDecidableEqImpl___redArg___lam__0(
    mut v_inst_189_: *mut crate::leanh::LeanObject,
    mut v_a_190_: *mut crate::leanh::LeanObject,
    mut v_b_191_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_192_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_193_: u8 = 0;
    v___x_192_ = crate::leanh::lean_apply_2(v_inst_189_, v_a_190_, v_b_191_);
    v___x_193_ = (crate::leanh::lean_unbox(v___x_192_) as u8);
    return v___x_193_;
}
pub unsafe fn l_Array_instDecidableEqImpl___redArg___lam__0___boxed(
    mut v_inst_194_: *mut crate::leanh::LeanObject,
    mut v_a_195_: *mut crate::leanh::LeanObject,
    mut v_b_196_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_197_: u8 = 0;
    let mut v_r_198_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_197_ = l_Array_instDecidableEqImpl___redArg___lam__0(v_inst_194_, v_a_195_, v_b_196_);
    v_r_198_ = crate::leanh::lean_box((v_res_197_) as usize);
    return v_r_198_;
}
pub unsafe fn l_Array_instDecidableEqImpl___redArg(
    mut v_inst_199_: *mut crate::leanh::LeanObject,
    mut v_xs_200_: *mut crate::leanh::LeanObject,
    mut v_ys_201_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_202_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_203_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_204_: u8 = 0;
    v___x_202_ = lean_array_get_size(v_xs_200_);
    v___x_203_ = lean_array_get_size(v_ys_201_);
    v___x_204_ = lean_nat_dec_eq(v___x_202_, v___x_203_);
    if v___x_204_ == 0 {
        crate::leanh::lean_dec_ref(v_inst_199_);
        return v___x_204_;
    } else {
        let mut v___f_205_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_206_: u8 = 0;
        v___f_205_ = crate::leanh::lean_alloc_closure(
            l_Array_instDecidableEqImpl___redArg___lam__0___boxed as *mut core::ffi::c_void,
            3,
            1,
        );
        crate::leanh::lean_closure_set(v___f_205_, 0, v_inst_199_);
        v___x_206_ = l_Array_isEqvAux___redArg(v_xs_200_, v_ys_201_, v___f_205_, v___x_202_);
        return v___x_206_;
    }
}
pub unsafe fn l_Array_instDecidableEqImpl___redArg___boxed(
    mut v_inst_207_: *mut crate::leanh::LeanObject,
    mut v_xs_208_: *mut crate::leanh::LeanObject,
    mut v_ys_209_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_210_: u8 = 0;
    let mut v_r_211_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_210_ = l_Array_instDecidableEqImpl___redArg(v_inst_207_, v_xs_208_, v_ys_209_);
    crate::leanh::lean_dec_ref(v_ys_209_);
    crate::leanh::lean_dec_ref(v_xs_208_);
    v_r_211_ = crate::leanh::lean_box((v_res_210_) as usize);
    return v_r_211_;
}
pub unsafe fn l_Array_instDecidableEqImpl(
    mut v_00_u03b1_212_: *mut crate::leanh::LeanObject,
    mut v_inst_213_: *mut crate::leanh::LeanObject,
    mut v_xs_214_: *mut crate::leanh::LeanObject,
    mut v_ys_215_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_216_: u8 = 0;
    v___x_216_ = l_Array_instDecidableEqImpl___redArg(v_inst_213_, v_xs_214_, v_ys_215_);
    return v___x_216_;
}
pub unsafe fn l_Array_instDecidableEqImpl___boxed(
    mut v_00_u03b1_217_: *mut crate::leanh::LeanObject,
    mut v_inst_218_: *mut crate::leanh::LeanObject,
    mut v_xs_219_: *mut crate::leanh::LeanObject,
    mut v_ys_220_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_221_: u8 = 0;
    let mut v_r_222_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_221_ = l_Array_instDecidableEqImpl(v_00_u03b1_217_, v_inst_218_, v_xs_219_, v_ys_220_);
    crate::leanh::lean_dec_ref(v_ys_220_);
    crate::leanh::lean_dec_ref(v_xs_219_);
    v_r_222_ = crate::leanh::lean_box((v_res_221_) as usize);
    return v_r_222_;
}
pub unsafe fn l_Array_instDecidableEq___redArg(
    mut v_inst_223_: *mut crate::leanh::LeanObject,
    mut v_xs_224_: *mut crate::leanh::LeanObject,
    mut v_ys_225_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v_toList_226_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    crate::leanh::lean_inc_ref(v_xs_224_);
    v_toList_226_ = lean_array_to_list(v_xs_224_);
    if crate::leanh::lean_obj_tag(v_toList_226_) == 0 {
        let mut v_toList_227_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec_ref(v_xs_224_);
        crate::leanh::lean_dec_ref(v_inst_223_);
        v_toList_227_ = lean_array_to_list(v_ys_225_);
        if crate::leanh::lean_obj_tag(v_toList_227_) == 0 {
            let mut v___x_228_: u8 = 0;
            v___x_228_ = 1;
            return v___x_228_;
        } else {
            let mut v___x_229_: u8 = 0;
            crate::leanh::lean_dec_ref_known(v_toList_227_, 2);
            v___x_229_ = 0;
            return v___x_229_;
        }
    } else {
        let mut v_toList_230_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec_ref_known(v_toList_226_, 2);
        crate::leanh::lean_inc_ref(v_ys_225_);
        v_toList_230_ = lean_array_to_list(v_ys_225_);
        if crate::leanh::lean_obj_tag(v_toList_230_) == 0 {
            let mut v___x_231_: u8 = 0;
            crate::leanh::lean_dec_ref(v_ys_225_);
            crate::leanh::lean_dec_ref(v_xs_224_);
            crate::leanh::lean_dec_ref(v_inst_223_);
            v___x_231_ = 0;
            return v___x_231_;
        } else {
            let mut v___x_232_: u8 = 0;
            crate::leanh::lean_dec_ref_known(v_toList_230_, 2);
            v___x_232_ = l_Array_instDecidableEqImpl___redArg(v_inst_223_, v_xs_224_, v_ys_225_);
            crate::leanh::lean_dec_ref(v_ys_225_);
            crate::leanh::lean_dec_ref(v_xs_224_);
            return v___x_232_;
        }
    }
}
pub unsafe fn l_Array_instDecidableEq___redArg___boxed(
    mut v_inst_233_: *mut crate::leanh::LeanObject,
    mut v_xs_234_: *mut crate::leanh::LeanObject,
    mut v_ys_235_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_236_: u8 = 0;
    let mut v_r_237_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_236_ = l_Array_instDecidableEq___redArg(v_inst_233_, v_xs_234_, v_ys_235_);
    v_r_237_ = crate::leanh::lean_box((v_res_236_) as usize);
    return v_r_237_;
}
pub unsafe fn l_Array_instDecidableEq(
    mut v_00_u03b1_238_: *mut crate::leanh::LeanObject,
    mut v_inst_239_: *mut crate::leanh::LeanObject,
    mut v_xs_240_: *mut crate::leanh::LeanObject,
    mut v_ys_241_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_242_: u8 = 0;
    v___x_242_ = l_Array_instDecidableEq___redArg(v_inst_239_, v_xs_240_, v_ys_241_);
    return v___x_242_;
}
pub unsafe fn l_Array_instDecidableEq___boxed(
    mut v_00_u03b1_243_: *mut crate::leanh::LeanObject,
    mut v_inst_244_: *mut crate::leanh::LeanObject,
    mut v_xs_245_: *mut crate::leanh::LeanObject,
    mut v_ys_246_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_247_: u8 = 0;
    let mut v_r_248_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_247_ = l_Array_instDecidableEq(v_00_u03b1_243_, v_inst_244_, v_xs_245_, v_ys_246_);
    v_r_248_ = crate::leanh::lean_box((v_res_247_) as usize);
    return v_r_248_;
}
pub unsafe fn l_Array_instDecidableEqEmp___redArg(
    mut v_xs_249_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v_toList_250_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_toList_250_ = lean_array_to_list(v_xs_249_);
    if crate::leanh::lean_obj_tag(v_toList_250_) == 0 {
        let mut v___x_251_: u8 = 0;
        v___x_251_ = 1;
        return v___x_251_;
    } else {
        let mut v___x_252_: u8 = 0;
        crate::leanh::lean_dec_ref_known(v_toList_250_, 2);
        v___x_252_ = 0;
        return v___x_252_;
    }
}
pub unsafe fn l_Array_instDecidableEqEmp___redArg___boxed(
    mut v_xs_253_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_254_: u8 = 0;
    let mut v_r_255_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_254_ = l_Array_instDecidableEqEmp___redArg(v_xs_253_);
    v_r_255_ = crate::leanh::lean_box((v_res_254_) as usize);
    return v_r_255_;
}
pub unsafe fn l_Array_instDecidableEqEmp(
    mut v_00_u03b1_256_: *mut crate::leanh::LeanObject,
    mut v_xs_257_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_258_: u8 = 0;
    v___x_258_ = l_Array_instDecidableEqEmp___redArg(v_xs_257_);
    return v___x_258_;
}
pub unsafe fn l_Array_instDecidableEqEmp___boxed(
    mut v_00_u03b1_259_: *mut crate::leanh::LeanObject,
    mut v_xs_260_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_261_: u8 = 0;
    let mut v_r_262_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_261_ = l_Array_instDecidableEqEmp(v_00_u03b1_259_, v_xs_260_);
    v_r_262_ = crate::leanh::lean_box((v_res_261_) as usize);
    return v_r_262_;
}
pub unsafe fn l_Array_instDecidableEmpEq___redArg(
    mut v_ys_263_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v_toList_264_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_toList_264_ = lean_array_to_list(v_ys_263_);
    if crate::leanh::lean_obj_tag(v_toList_264_) == 0 {
        let mut v___x_265_: u8 = 0;
        v___x_265_ = 1;
        return v___x_265_;
    } else {
        let mut v___x_266_: u8 = 0;
        crate::leanh::lean_dec_ref_known(v_toList_264_, 2);
        v___x_266_ = 0;
        return v___x_266_;
    }
}
pub unsafe fn l_Array_instDecidableEmpEq___redArg___boxed(
    mut v_ys_267_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_268_: u8 = 0;
    let mut v_r_269_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_268_ = l_Array_instDecidableEmpEq___redArg(v_ys_267_);
    v_r_269_ = crate::leanh::lean_box((v_res_268_) as usize);
    return v_r_269_;
}
pub unsafe fn l_Array_instDecidableEmpEq(
    mut v_00_u03b1_270_: *mut crate::leanh::LeanObject,
    mut v_ys_271_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_272_: u8 = 0;
    v___x_272_ = l_Array_instDecidableEmpEq___redArg(v_ys_271_);
    return v___x_272_;
}
pub unsafe fn l_Array_instDecidableEmpEq___boxed(
    mut v_00_u03b1_273_: *mut crate::leanh::LeanObject,
    mut v_ys_274_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_275_: u8 = 0;
    let mut v_r_276_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_275_ = l_Array_instDecidableEmpEq(v_00_u03b1_273_, v_ys_274_);
    v_r_276_ = crate::leanh::lean_box((v_res_275_) as usize);
    return v_r_276_;
}
pub unsafe fn l_Array_instDecidableEqEmpImpl___redArg(
    mut v_xs_277_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_278_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_279_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_280_: u8 = 0;
    v___x_278_ = lean_array_get_size(v_xs_277_);
    v___x_279_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_280_ = lean_nat_dec_eq(v___x_278_, v___x_279_);
    return v___x_280_;
}
pub unsafe fn l_Array_instDecidableEqEmpImpl___redArg___boxed(
    mut v_xs_281_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_282_: u8 = 0;
    let mut v_r_283_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_282_ = l_Array_instDecidableEqEmpImpl___redArg(v_xs_281_);
    crate::leanh::lean_dec_ref(v_xs_281_);
    v_r_283_ = crate::leanh::lean_box((v_res_282_) as usize);
    return v_r_283_;
}
pub unsafe fn l_Array_instDecidableEqEmpImpl(
    mut v_00_u03b1_284_: *mut crate::leanh::LeanObject,
    mut v_xs_285_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_286_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_287_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_288_: u8 = 0;
    v___x_286_ = lean_array_get_size(v_xs_285_);
    v___x_287_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_288_ = lean_nat_dec_eq(v___x_286_, v___x_287_);
    return v___x_288_;
}
pub unsafe fn l_Array_instDecidableEqEmpImpl___boxed(
    mut v_00_u03b1_289_: *mut crate::leanh::LeanObject,
    mut v_xs_290_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_291_: u8 = 0;
    let mut v_r_292_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_291_ = l_Array_instDecidableEqEmpImpl(v_00_u03b1_289_, v_xs_290_);
    crate::leanh::lean_dec_ref(v_xs_290_);
    v_r_292_ = crate::leanh::lean_box((v_res_291_) as usize);
    return v_r_292_;
}
pub unsafe fn l_Array_instDecidableEmpEqImpl___redArg(
    mut v_xs_293_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_294_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_295_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_296_: u8 = 0;
    v___x_294_ = lean_array_get_size(v_xs_293_);
    v___x_295_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_296_ = lean_nat_dec_eq(v___x_294_, v___x_295_);
    return v___x_296_;
}
pub unsafe fn l_Array_instDecidableEmpEqImpl___redArg___boxed(
    mut v_xs_297_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_298_: u8 = 0;
    let mut v_r_299_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_298_ = l_Array_instDecidableEmpEqImpl___redArg(v_xs_297_);
    crate::leanh::lean_dec_ref(v_xs_297_);
    v_r_299_ = crate::leanh::lean_box((v_res_298_) as usize);
    return v_r_299_;
}
pub unsafe fn l_Array_instDecidableEmpEqImpl(
    mut v_00_u03b1_300_: *mut crate::leanh::LeanObject,
    mut v_xs_301_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_302_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_303_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_304_: u8 = 0;
    v___x_302_ = lean_array_get_size(v_xs_301_);
    v___x_303_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_304_ = lean_nat_dec_eq(v___x_302_, v___x_303_);
    return v___x_304_;
}
pub unsafe fn l_Array_instDecidableEmpEqImpl___boxed(
    mut v_00_u03b1_305_: *mut crate::leanh::LeanObject,
    mut v_xs_306_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_307_: u8 = 0;
    let mut v_r_308_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_307_ = l_Array_instDecidableEmpEqImpl(v_00_u03b1_305_, v_xs_306_);
    crate::leanh::lean_dec_ref(v_xs_306_);
    v_r_308_ = crate::leanh::lean_box((v_res_307_) as usize);
    return v_r_308_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Init_Data_Array_DecidableEq(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Init_Data_Array_Basic(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Array_Basic(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Nat_Lemmas(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_ByCases(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Classical(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_BEq(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Bool(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_List_Nat_BEq(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_RCases(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Init_Data_Array_DecidableEq(
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
pub unsafe fn initialize_Init_Data_Array_DecidableEq(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Init_Data_Array_Basic(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Array_Basic(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Nat_Lemmas(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_ByCases(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Classical(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Data_BEq(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Bool(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Data_List_Nat_BEq(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_RCases(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Array_DecidableEq(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Init_Data_Array_DecidableEq(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Init_Data_Array_DecidableEq(builtin);
}
