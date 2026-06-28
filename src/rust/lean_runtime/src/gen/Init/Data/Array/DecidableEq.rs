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
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_alloc_closure, lean_apply_1, lean_apply_2, lean_box,
    lean_closure_set, lean_dec, lean_dec_ref, lean_dec_ref_known, lean_inc_ref,
    lean_io_result_is_error, lean_io_result_mk_ok, lean_obj_tag, lean_unbox, lean_unsigned_to_nat,
};
pub unsafe fn l___private_Init_Data_Array_DecidableEq_0__Array_isEqvAux_match__1_splitter___redArg(
    mut v_x_155_: *mut LeanObject,
    mut v_h__1_156_: *mut LeanObject,
    mut v_h__2_157_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_zero_158_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isZero_159_: u8 = 0;
    v_zero_158_ = lean_unsigned_to_nat(0);
    v_isZero_159_ = lean_nat_dec_eq(v_x_155_, v_zero_158_);
    if v_isZero_159_ == 1 {
        let mut v___x_160_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_157_);
        v___x_160_ = lean_apply_1(v_h__1_156_, lean_box(0));
        return v___x_160_;
    } else {
        let mut v_one_161_: *mut LeanObject = core::ptr::null_mut();
        let mut v_n_162_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_163_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_156_);
        v_one_161_ = lean_unsigned_to_nat(1);
        v_n_162_ = lean_nat_sub(v_x_155_, v_one_161_);
        v___x_163_ = lean_apply_2(v_h__2_157_, v_n_162_, lean_box(0));
        return v___x_163_;
    }
}
pub unsafe fn l___private_Init_Data_Array_DecidableEq_0__Array_isEqvAux_match__1_splitter___redArg___boxed(
    mut v_x_164_: *mut LeanObject,
    mut v_h__1_165_: *mut LeanObject,
    mut v_h__2_166_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_167_: *mut LeanObject = core::ptr::null_mut();
    v_res_167_ =
        l___private_Init_Data_Array_DecidableEq_0__Array_isEqvAux_match__1_splitter___redArg(
            v_x_164_,
            v_h__1_165_,
            v_h__2_166_,
        );
    lean_dec(v_x_164_);
    return v_res_167_;
}
pub unsafe fn l___private_Init_Data_Array_DecidableEq_0__Array_isEqvAux_match__1_splitter(
    mut v_00_u03b1_168_: *mut LeanObject,
    mut v_xs_169_: *mut LeanObject,
    mut v_motive_170_: *mut LeanObject,
    mut v_x_171_: *mut LeanObject,
    mut v_x_172_: *mut LeanObject,
    mut v_h__1_173_: *mut LeanObject,
    mut v_h__2_174_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_zero_175_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isZero_176_: u8 = 0;
    v_zero_175_ = lean_unsigned_to_nat(0);
    v_isZero_176_ = lean_nat_dec_eq(v_x_171_, v_zero_175_);
    if v_isZero_176_ == 1 {
        let mut v___x_177_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_174_);
        v___x_177_ = lean_apply_1(v_h__1_173_, lean_box(0));
        return v___x_177_;
    } else {
        let mut v_one_178_: *mut LeanObject = core::ptr::null_mut();
        let mut v_n_179_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_180_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_173_);
        v_one_178_ = lean_unsigned_to_nat(1);
        v_n_179_ = lean_nat_sub(v_x_171_, v_one_178_);
        v___x_180_ = lean_apply_2(v_h__2_174_, v_n_179_, lean_box(0));
        return v___x_180_;
    }
}
pub unsafe fn l___private_Init_Data_Array_DecidableEq_0__Array_isEqvAux_match__1_splitter___boxed(
    mut v_00_u03b1_181_: *mut LeanObject,
    mut v_xs_182_: *mut LeanObject,
    mut v_motive_183_: *mut LeanObject,
    mut v_x_184_: *mut LeanObject,
    mut v_x_185_: *mut LeanObject,
    mut v_h__1_186_: *mut LeanObject,
    mut v_h__2_187_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_188_: *mut LeanObject = core::ptr::null_mut();
    v_res_188_ = l___private_Init_Data_Array_DecidableEq_0__Array_isEqvAux_match__1_splitter(
        v_00_u03b1_181_,
        v_xs_182_,
        v_motive_183_,
        v_x_184_,
        v_x_185_,
        v_h__1_186_,
        v_h__2_187_,
    );
    lean_dec(v_x_184_);
    lean_dec_ref(v_xs_182_);
    return v_res_188_;
}
pub unsafe fn l_Array_instDecidableEqImpl___redArg___lam__0(
    mut v_inst_189_: *mut LeanObject,
    mut v_a_190_: *mut LeanObject,
    mut v_b_191_: *mut LeanObject,
) -> u8 {
    let mut v___x_192_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_193_: u8 = 0;
    v___x_192_ = lean_apply_2(v_inst_189_, v_a_190_, v_b_191_);
    v___x_193_ = (lean_unbox(v___x_192_) as u8);
    return v___x_193_;
}
pub unsafe fn l_Array_instDecidableEqImpl___redArg___lam__0___boxed(
    mut v_inst_194_: *mut LeanObject,
    mut v_a_195_: *mut LeanObject,
    mut v_b_196_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_197_: u8 = 0;
    let mut v_r_198_: *mut LeanObject = core::ptr::null_mut();
    v_res_197_ = l_Array_instDecidableEqImpl___redArg___lam__0(v_inst_194_, v_a_195_, v_b_196_);
    v_r_198_ = lean_box((v_res_197_) as usize);
    return v_r_198_;
}
pub unsafe fn l_Array_instDecidableEqImpl___redArg(
    mut v_inst_199_: *mut LeanObject,
    mut v_xs_200_: *mut LeanObject,
    mut v_ys_201_: *mut LeanObject,
) -> u8 {
    let mut v___x_202_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_203_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_204_: u8 = 0;
    v___x_202_ = lean_array_get_size(v_xs_200_);
    v___x_203_ = lean_array_get_size(v_ys_201_);
    v___x_204_ = lean_nat_dec_eq(v___x_202_, v___x_203_);
    if v___x_204_ == 0 {
        lean_dec_ref(v_inst_199_);
        return v___x_204_;
    } else {
        let mut v___f_205_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_206_: u8 = 0;
        v___f_205_ = lean_alloc_closure(
            l_Array_instDecidableEqImpl___redArg___lam__0___boxed as *mut core::ffi::c_void,
            3,
            1,
        );
        lean_closure_set(v___f_205_, 0, v_inst_199_);
        v___x_206_ = l_Array_isEqvAux___redArg(v_xs_200_, v_ys_201_, v___f_205_, v___x_202_);
        return v___x_206_;
    }
}
pub unsafe fn l_Array_instDecidableEqImpl___redArg___boxed(
    mut v_inst_207_: *mut LeanObject,
    mut v_xs_208_: *mut LeanObject,
    mut v_ys_209_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_210_: u8 = 0;
    let mut v_r_211_: *mut LeanObject = core::ptr::null_mut();
    v_res_210_ = l_Array_instDecidableEqImpl___redArg(v_inst_207_, v_xs_208_, v_ys_209_);
    lean_dec_ref(v_ys_209_);
    lean_dec_ref(v_xs_208_);
    v_r_211_ = lean_box((v_res_210_) as usize);
    return v_r_211_;
}
pub unsafe fn l_Array_instDecidableEqImpl(
    mut v_00_u03b1_212_: *mut LeanObject,
    mut v_inst_213_: *mut LeanObject,
    mut v_xs_214_: *mut LeanObject,
    mut v_ys_215_: *mut LeanObject,
) -> u8 {
    let mut v___x_216_: u8 = 0;
    v___x_216_ = l_Array_instDecidableEqImpl___redArg(v_inst_213_, v_xs_214_, v_ys_215_);
    return v___x_216_;
}
pub unsafe fn l_Array_instDecidableEqImpl___boxed(
    mut v_00_u03b1_217_: *mut LeanObject,
    mut v_inst_218_: *mut LeanObject,
    mut v_xs_219_: *mut LeanObject,
    mut v_ys_220_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_221_: u8 = 0;
    let mut v_r_222_: *mut LeanObject = core::ptr::null_mut();
    v_res_221_ = l_Array_instDecidableEqImpl(v_00_u03b1_217_, v_inst_218_, v_xs_219_, v_ys_220_);
    lean_dec_ref(v_ys_220_);
    lean_dec_ref(v_xs_219_);
    v_r_222_ = lean_box((v_res_221_) as usize);
    return v_r_222_;
}
pub unsafe fn l_Array_instDecidableEq___redArg(
    mut v_inst_223_: *mut LeanObject,
    mut v_xs_224_: *mut LeanObject,
    mut v_ys_225_: *mut LeanObject,
) -> u8 {
    let mut v_toList_226_: *mut LeanObject = core::ptr::null_mut();
    lean_inc_ref(v_xs_224_);
    v_toList_226_ = lean_array_to_list(v_xs_224_);
    if lean_obj_tag(v_toList_226_) == 0 {
        let mut v_toList_227_: *mut LeanObject = core::ptr::null_mut();
        lean_dec_ref(v_xs_224_);
        lean_dec_ref(v_inst_223_);
        v_toList_227_ = lean_array_to_list(v_ys_225_);
        if lean_obj_tag(v_toList_227_) == 0 {
            let mut v___x_228_: u8 = 0;
            v___x_228_ = 1;
            return v___x_228_;
        } else {
            let mut v___x_229_: u8 = 0;
            lean_dec_ref_known(v_toList_227_, 2);
            v___x_229_ = 0;
            return v___x_229_;
        }
    } else {
        let mut v_toList_230_: *mut LeanObject = core::ptr::null_mut();
        lean_dec_ref_known(v_toList_226_, 2);
        lean_inc_ref(v_ys_225_);
        v_toList_230_ = lean_array_to_list(v_ys_225_);
        if lean_obj_tag(v_toList_230_) == 0 {
            let mut v___x_231_: u8 = 0;
            lean_dec_ref(v_ys_225_);
            lean_dec_ref(v_xs_224_);
            lean_dec_ref(v_inst_223_);
            v___x_231_ = 0;
            return v___x_231_;
        } else {
            let mut v___x_232_: u8 = 0;
            lean_dec_ref_known(v_toList_230_, 2);
            v___x_232_ = l_Array_instDecidableEqImpl___redArg(v_inst_223_, v_xs_224_, v_ys_225_);
            lean_dec_ref(v_ys_225_);
            lean_dec_ref(v_xs_224_);
            return v___x_232_;
        }
    }
}
pub unsafe fn l_Array_instDecidableEq___redArg___boxed(
    mut v_inst_233_: *mut LeanObject,
    mut v_xs_234_: *mut LeanObject,
    mut v_ys_235_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_236_: u8 = 0;
    let mut v_r_237_: *mut LeanObject = core::ptr::null_mut();
    v_res_236_ = l_Array_instDecidableEq___redArg(v_inst_233_, v_xs_234_, v_ys_235_);
    v_r_237_ = lean_box((v_res_236_) as usize);
    return v_r_237_;
}
pub unsafe fn l_Array_instDecidableEq(
    mut v_00_u03b1_238_: *mut LeanObject,
    mut v_inst_239_: *mut LeanObject,
    mut v_xs_240_: *mut LeanObject,
    mut v_ys_241_: *mut LeanObject,
) -> u8 {
    let mut v___x_242_: u8 = 0;
    v___x_242_ = l_Array_instDecidableEq___redArg(v_inst_239_, v_xs_240_, v_ys_241_);
    return v___x_242_;
}
pub unsafe fn l_Array_instDecidableEq___boxed(
    mut v_00_u03b1_243_: *mut LeanObject,
    mut v_inst_244_: *mut LeanObject,
    mut v_xs_245_: *mut LeanObject,
    mut v_ys_246_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_247_: u8 = 0;
    let mut v_r_248_: *mut LeanObject = core::ptr::null_mut();
    v_res_247_ = l_Array_instDecidableEq(v_00_u03b1_243_, v_inst_244_, v_xs_245_, v_ys_246_);
    v_r_248_ = lean_box((v_res_247_) as usize);
    return v_r_248_;
}
pub unsafe fn l_Array_instDecidableEqEmp___redArg(mut v_xs_249_: *mut LeanObject) -> u8 {
    let mut v_toList_250_: *mut LeanObject = core::ptr::null_mut();
    v_toList_250_ = lean_array_to_list(v_xs_249_);
    if lean_obj_tag(v_toList_250_) == 0 {
        let mut v___x_251_: u8 = 0;
        v___x_251_ = 1;
        return v___x_251_;
    } else {
        let mut v___x_252_: u8 = 0;
        lean_dec_ref_known(v_toList_250_, 2);
        v___x_252_ = 0;
        return v___x_252_;
    }
}
pub unsafe fn l_Array_instDecidableEqEmp___redArg___boxed(
    mut v_xs_253_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_254_: u8 = 0;
    let mut v_r_255_: *mut LeanObject = core::ptr::null_mut();
    v_res_254_ = l_Array_instDecidableEqEmp___redArg(v_xs_253_);
    v_r_255_ = lean_box((v_res_254_) as usize);
    return v_r_255_;
}
pub unsafe fn l_Array_instDecidableEqEmp(
    mut v_00_u03b1_256_: *mut LeanObject,
    mut v_xs_257_: *mut LeanObject,
) -> u8 {
    let mut v___x_258_: u8 = 0;
    v___x_258_ = l_Array_instDecidableEqEmp___redArg(v_xs_257_);
    return v___x_258_;
}
pub unsafe fn l_Array_instDecidableEqEmp___boxed(
    mut v_00_u03b1_259_: *mut LeanObject,
    mut v_xs_260_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_261_: u8 = 0;
    let mut v_r_262_: *mut LeanObject = core::ptr::null_mut();
    v_res_261_ = l_Array_instDecidableEqEmp(v_00_u03b1_259_, v_xs_260_);
    v_r_262_ = lean_box((v_res_261_) as usize);
    return v_r_262_;
}
pub unsafe fn l_Array_instDecidableEmpEq___redArg(mut v_ys_263_: *mut LeanObject) -> u8 {
    let mut v_toList_264_: *mut LeanObject = core::ptr::null_mut();
    v_toList_264_ = lean_array_to_list(v_ys_263_);
    if lean_obj_tag(v_toList_264_) == 0 {
        let mut v___x_265_: u8 = 0;
        v___x_265_ = 1;
        return v___x_265_;
    } else {
        let mut v___x_266_: u8 = 0;
        lean_dec_ref_known(v_toList_264_, 2);
        v___x_266_ = 0;
        return v___x_266_;
    }
}
pub unsafe fn l_Array_instDecidableEmpEq___redArg___boxed(
    mut v_ys_267_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_268_: u8 = 0;
    let mut v_r_269_: *mut LeanObject = core::ptr::null_mut();
    v_res_268_ = l_Array_instDecidableEmpEq___redArg(v_ys_267_);
    v_r_269_ = lean_box((v_res_268_) as usize);
    return v_r_269_;
}
pub unsafe fn l_Array_instDecidableEmpEq(
    mut v_00_u03b1_270_: *mut LeanObject,
    mut v_ys_271_: *mut LeanObject,
) -> u8 {
    let mut v___x_272_: u8 = 0;
    v___x_272_ = l_Array_instDecidableEmpEq___redArg(v_ys_271_);
    return v___x_272_;
}
pub unsafe fn l_Array_instDecidableEmpEq___boxed(
    mut v_00_u03b1_273_: *mut LeanObject,
    mut v_ys_274_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_275_: u8 = 0;
    let mut v_r_276_: *mut LeanObject = core::ptr::null_mut();
    v_res_275_ = l_Array_instDecidableEmpEq(v_00_u03b1_273_, v_ys_274_);
    v_r_276_ = lean_box((v_res_275_) as usize);
    return v_r_276_;
}
pub unsafe fn l_Array_instDecidableEqEmpImpl___redArg(mut v_xs_277_: *mut LeanObject) -> u8 {
    let mut v___x_278_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_279_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_280_: u8 = 0;
    v___x_278_ = lean_array_get_size(v_xs_277_);
    v___x_279_ = lean_unsigned_to_nat(0);
    v___x_280_ = lean_nat_dec_eq(v___x_278_, v___x_279_);
    return v___x_280_;
}
pub unsafe fn l_Array_instDecidableEqEmpImpl___redArg___boxed(
    mut v_xs_281_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_282_: u8 = 0;
    let mut v_r_283_: *mut LeanObject = core::ptr::null_mut();
    v_res_282_ = l_Array_instDecidableEqEmpImpl___redArg(v_xs_281_);
    lean_dec_ref(v_xs_281_);
    v_r_283_ = lean_box((v_res_282_) as usize);
    return v_r_283_;
}
pub unsafe fn l_Array_instDecidableEqEmpImpl(
    mut v_00_u03b1_284_: *mut LeanObject,
    mut v_xs_285_: *mut LeanObject,
) -> u8 {
    let mut v___x_286_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_287_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_288_: u8 = 0;
    v___x_286_ = lean_array_get_size(v_xs_285_);
    v___x_287_ = lean_unsigned_to_nat(0);
    v___x_288_ = lean_nat_dec_eq(v___x_286_, v___x_287_);
    return v___x_288_;
}
pub unsafe fn l_Array_instDecidableEqEmpImpl___boxed(
    mut v_00_u03b1_289_: *mut LeanObject,
    mut v_xs_290_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_291_: u8 = 0;
    let mut v_r_292_: *mut LeanObject = core::ptr::null_mut();
    v_res_291_ = l_Array_instDecidableEqEmpImpl(v_00_u03b1_289_, v_xs_290_);
    lean_dec_ref(v_xs_290_);
    v_r_292_ = lean_box((v_res_291_) as usize);
    return v_r_292_;
}
pub unsafe fn l_Array_instDecidableEmpEqImpl___redArg(mut v_xs_293_: *mut LeanObject) -> u8 {
    let mut v___x_294_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_295_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_296_: u8 = 0;
    v___x_294_ = lean_array_get_size(v_xs_293_);
    v___x_295_ = lean_unsigned_to_nat(0);
    v___x_296_ = lean_nat_dec_eq(v___x_294_, v___x_295_);
    return v___x_296_;
}
pub unsafe fn l_Array_instDecidableEmpEqImpl___redArg___boxed(
    mut v_xs_297_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_298_: u8 = 0;
    let mut v_r_299_: *mut LeanObject = core::ptr::null_mut();
    v_res_298_ = l_Array_instDecidableEmpEqImpl___redArg(v_xs_297_);
    lean_dec_ref(v_xs_297_);
    v_r_299_ = lean_box((v_res_298_) as usize);
    return v_r_299_;
}
pub unsafe fn l_Array_instDecidableEmpEqImpl(
    mut v_00_u03b1_300_: *mut LeanObject,
    mut v_xs_301_: *mut LeanObject,
) -> u8 {
    let mut v___x_302_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_303_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_304_: u8 = 0;
    v___x_302_ = lean_array_get_size(v_xs_301_);
    v___x_303_ = lean_unsigned_to_nat(0);
    v___x_304_ = lean_nat_dec_eq(v___x_302_, v___x_303_);
    return v___x_304_;
}
pub unsafe fn l_Array_instDecidableEmpEqImpl___boxed(
    mut v_00_u03b1_305_: *mut LeanObject,
    mut v_xs_306_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_307_: u8 = 0;
    let mut v_r_308_: *mut LeanObject = core::ptr::null_mut();
    v_res_307_ = l_Array_instDecidableEmpEqImpl(v_00_u03b1_305_, v_xs_306_);
    lean_dec_ref(v_xs_306_);
    v_r_308_ = lean_box((v_res_307_) as usize);
    return v_r_308_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Init_Data_Array_DecidableEq(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Init_Data_Array_Basic(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Nat_Lemmas(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_ByCases(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Classical(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_BEq(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Bool(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_List_Nat_BEq(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_RCases(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Init_Data_Array_DecidableEq(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_meta_initialized = true;
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Init_Data_Array_DecidableEq(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Init_Data_Array_Basic(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Data_Nat_Lemmas(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_ByCases(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Classical(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Data_BEq(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Data_Bool(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Data_List_Nat_BEq(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_RCases(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Array_DecidableEq(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Init_Data_Array_DecidableEq(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Init_Data_Array_DecidableEq(builtin);
}
