// Lean compiler output
// Module: Std.Sat.AIG.If
// Imports: Std.Sat.AIG.LawfulVecOperator Init.Omega
use crate::ffi::{
    lean_array_fget_borrowed, lean_array_push, lean_mk_empty_array_with_capacity, lean_nat_add,
    lean_nat_dec_eq, lean_nat_dec_lt, lean_nat_land, lean_nat_lor, lean_nat_mul, lean_nat_shiftr,
};
use crate::r#gen::Init::Data::Bool::l_Bool_toNat;
use crate::r#gen::Init::Omega::{initialize_Init_Omega, runtime_initialize_Init_Omega};
use crate::r#gen::Std::Sat::AIG::Cached::l_Std_Sat_AIG_mkGateCached___redArg;
use crate::r#gen::Std::Sat::AIG::CachedGates::l_Std_Sat_AIG_mkOrCached___redArg;
use crate::r#gen::Std::Sat::AIG::LawfulVecOperator::{
    initialize_Std_Sat_AIG_LawfulVecOperator, runtime_initialize_Std_Sat_AIG_LawfulVecOperator,
};
pub unsafe fn l_Std_Sat_AIG_mkIfCached___redArg(
    mut v_inst_193_: *mut leanh::LeanObject,
    mut v_inst_194_: *mut leanh::LeanObject,
    mut v_aig_195_: *mut leanh::LeanObject,
    mut v_input_196_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_discr_197_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_lhs_198_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_rhs_199_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_200_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_res_201_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_aig_202_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_203_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_205_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_206_: u8 = 0;
    let mut v_gate_207_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_invert_208_: u8 = 0;
    let mut v___x_210_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_211_: u8 = 0;
    let mut v_gate_212_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_invert_213_: u8 = 0;
    let mut v___x_215_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_216_: u8 = 0;
    let mut v_aig_218_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_219_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_221_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_223_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_res_224_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_aig_225_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_226_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_228_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_229_: u8 = 0;
    let mut v_gate_230_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_invert_231_: u8 = 0;
    let mut v___x_233_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_234_: u8 = 0;
    let mut v_lhsRef_236_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_238_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_239_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_240_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_241_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_242_: u8 = 0;
    let mut v_isSharedCheck_243_: u8 = 0;
    let mut v_reuseFailAlloc_244_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_245_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_246_: u8 = 0;
    let mut v___x_248_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_249_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_250_: u8 = 0;
    let mut v___x_252_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_253_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_254_: u8 = 0;
    let mut v_isSharedCheck_255_: u8 = 0;
    let mut v_isSharedCheck_256_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_discr_197_ = leanh::lean_ctor_get(v_input_196_, 0);
                leanh::lean_inc_ref_n(v_discr_197_, 2);
                v_lhs_198_ = leanh::lean_ctor_get(v_input_196_, 1);
                leanh::lean_inc_ref(v_lhs_198_);
                v_rhs_199_ = leanh::lean_ctor_get(v_input_196_, 2);
                leanh::lean_inc_ref(v_rhs_199_);
                leanh::lean_dec_ref(v_input_196_);
                v___x_200_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_200_, 0, v_discr_197_);
                leanh::lean_ctor_set(v___x_200_, 1, v_lhs_198_);
                leanh::lean_inc_ref(v_inst_194_);
                leanh::lean_inc_ref(v_inst_193_);
                v_res_201_ = l_Std_Sat_AIG_mkGateCached___redArg(
                    v_inst_193_,
                    v_inst_194_,
                    v_aig_195_,
                    v___x_200_,
                );
                v_aig_202_ = leanh::lean_ctor_get(v_res_201_, 0);
                v_ref_203_ = leanh::lean_ctor_get(v_res_201_, 1);
                v_isSharedCheck_256_ = (!leanh::lean_is_exclusive(v_res_201_)) as u8;
                if v_isSharedCheck_256_ == 0 {
                    v___x_205_ = v_res_201_;
                    v_isShared_206_ = v_isSharedCheck_256_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_ref_203_);
                    leanh::lean_inc(v_aig_202_);
                    leanh::lean_dec(v_res_201_);
                    v___x_205_ = leanh::lean_box(0);
                    v_isShared_206_ = v_isSharedCheck_256_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_gate_207_ = leanh::lean_ctor_get(v_discr_197_, 0);
                v_invert_208_ = leanh::lean_ctor_get_uint8(
                    v_discr_197_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                );
                v_isSharedCheck_255_ = (!leanh::lean_is_exclusive(v_discr_197_)) as u8;
                if v_isSharedCheck_255_ == 0 {
                    v___x_210_ = v_discr_197_;
                    v_isShared_211_ = v_isSharedCheck_255_;
                    state = 2;
                    continue;
                } else {
                    leanh::lean_inc(v_gate_207_);
                    leanh::lean_dec(v_discr_197_);
                    v___x_210_ = leanh::lean_box(0);
                    v_isShared_211_ = v_isSharedCheck_255_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v_gate_212_ = leanh::lean_ctor_get(v_rhs_199_, 0);
                v_invert_213_ = leanh::lean_ctor_get_uint8(
                    v_rhs_199_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                );
                v_isSharedCheck_254_ = (!leanh::lean_is_exclusive(v_rhs_199_)) as u8;
                if v_isSharedCheck_254_ == 0 {
                    v___x_215_ = v_rhs_199_;
                    v_isShared_216_ = v_isSharedCheck_254_;
                    state = 3;
                    continue;
                } else {
                    leanh::lean_inc(v_gate_212_);
                    leanh::lean_dec(v_rhs_199_);
                    v___x_215_ = leanh::lean_box(0);
                    v_isShared_216_ = v_isSharedCheck_254_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_invert_208_ == 0 {
                    v___x_246_ = 1;
                    if v_isShared_211_ == 0 {
                        v___x_248_ = v___x_210_;
                        state = 11;
                        continue;
                    } else {
                        v_reuseFailAlloc_249_ = leanh::lean_alloc_ctor(0, 1, (1) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_249_, 0, v_gate_207_);
                        v___x_248_ = v_reuseFailAlloc_249_;
                        state = 11;
                        continue;
                    }
                } else {
                    v___x_250_ = 0;
                    if v_isShared_211_ == 0 {
                        v___x_252_ = v___x_210_;
                        state = 12;
                        continue;
                    } else {
                        v_reuseFailAlloc_253_ = leanh::lean_alloc_ctor(0, 1, (1) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_253_, 0, v_gate_207_);
                        v___x_252_ = v_reuseFailAlloc_253_;
                        state = 12;
                        continue;
                    }
                }
            }
            4 => {
                if v_isShared_216_ == 0 {
                    v___x_221_ = v___x_215_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_245_ = leanh::lean_alloc_ctor(0, 1, (1) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_245_, 0, v_gate_212_);
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_245_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                        v_invert_213_,
                    );
                    v___x_221_ = v_reuseFailAlloc_245_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                if v_isShared_206_ == 0 {
                    leanh::lean_ctor_set(v___x_205_, 1, v___x_221_);
                    leanh::lean_ctor_set(v___x_205_, 0, v_ref_219_);
                    v___x_223_ = v___x_205_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_244_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_244_, 0, v_ref_219_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_244_, 1, v___x_221_);
                    v___x_223_ = v_reuseFailAlloc_244_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                leanh::lean_inc_ref(v_inst_194_);
                leanh::lean_inc_ref(v_inst_193_);
                v_res_224_ = l_Std_Sat_AIG_mkGateCached___redArg(
                    v_inst_193_,
                    v_inst_194_,
                    v_aig_218_,
                    v___x_223_,
                );
                v_aig_225_ = leanh::lean_ctor_get(v_res_224_, 0);
                v_ref_226_ = leanh::lean_ctor_get(v_res_224_, 1);
                v_isSharedCheck_243_ = (!leanh::lean_is_exclusive(v_res_224_)) as u8;
                if v_isSharedCheck_243_ == 0 {
                    v___x_228_ = v_res_224_;
                    v_isShared_229_ = v_isSharedCheck_243_;
                    state = 7;
                    continue;
                } else {
                    leanh::lean_inc(v_ref_226_);
                    leanh::lean_inc(v_aig_225_);
                    leanh::lean_dec(v_res_224_);
                    v___x_228_ = leanh::lean_box(0);
                    v_isShared_229_ = v_isSharedCheck_243_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                v_gate_230_ = leanh::lean_ctor_get(v_ref_203_, 0);
                v_invert_231_ = leanh::lean_ctor_get_uint8(
                    v_ref_203_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                );
                v_isSharedCheck_242_ = (!leanh::lean_is_exclusive(v_ref_203_)) as u8;
                if v_isSharedCheck_242_ == 0 {
                    v___x_233_ = v_ref_203_;
                    v_isShared_234_ = v_isSharedCheck_242_;
                    state = 8;
                    continue;
                } else {
                    leanh::lean_inc(v_gate_230_);
                    leanh::lean_dec(v_ref_203_);
                    v___x_233_ = leanh::lean_box(0);
                    v_isShared_234_ = v_isSharedCheck_242_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                if v_isShared_234_ == 0 {
                    v_lhsRef_236_ = v___x_233_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_241_ = leanh::lean_alloc_ctor(0, 1, (1) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_241_, 0, v_gate_230_);
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_241_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                        v_invert_231_,
                    );
                    v_lhsRef_236_ = v_reuseFailAlloc_241_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                if v_isShared_229_ == 0 {
                    leanh::lean_ctor_set(v___x_228_, 0, v_lhsRef_236_);
                    v___x_238_ = v___x_228_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_240_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_240_, 0, v_lhsRef_236_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_240_, 1, v_ref_226_);
                    v___x_238_ = v_reuseFailAlloc_240_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                v___x_239_ = l_Std_Sat_AIG_mkOrCached___redArg(
                    v_inst_193_,
                    v_inst_194_,
                    v_aig_225_,
                    v___x_238_,
                );
                return v___x_239_;
            }
            11 => {
                leanh::lean_ctor_set_uint8(
                    v___x_248_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                    v___x_246_,
                );
                v_aig_218_ = v_aig_202_;
                v_ref_219_ = v___x_248_;
                state = 4;
                continue;
            }
            12 => {
                leanh::lean_ctor_set_uint8(
                    v___x_252_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                    v___x_250_,
                );
                v_aig_218_ = v_aig_202_;
                v_ref_219_ = v___x_252_;
                state = 4;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Sat_AIG_mkIfCached(
    mut v_00_u03b1_257_: *mut leanh::LeanObject,
    mut v_inst_258_: *mut leanh::LeanObject,
    mut v_inst_259_: *mut leanh::LeanObject,
    mut v_aig_260_: *mut leanh::LeanObject,
    mut v_input_261_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_262_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_262_ =
        l_Std_Sat_AIG_mkIfCached___redArg(v_inst_258_, v_inst_259_, v_aig_260_, v_input_261_);
    return v___x_262_;
}
pub unsafe fn l_Std_Sat_AIG_RefVec_ite_go___redArg(
    mut v_inst_263_: *mut leanh::LeanObject,
    mut v_inst_264_: *mut leanh::LeanObject,
    mut v_w_265_: *mut leanh::LeanObject,
    mut v_aig_266_: *mut leanh::LeanObject,
    mut v_curr_267_: *mut leanh::LeanObject,
    mut v_discr_268_: *mut leanh::LeanObject,
    mut v_lhs_269_: *mut leanh::LeanObject,
    mut v_rhs_270_: *mut leanh::LeanObject,
    mut v_s_271_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___y_273_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_274_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_input_275_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_res_276_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_277_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_aig_278_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_gate_279_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_invert_280_: u8 = 0;
    let mut v_gate_281_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_invert_282_: u8 = 0;
    let mut v___x_284_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_285_: u8 = 0;
    let mut v_discr_287_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_288_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_289_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_290_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_291_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_292_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_293_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_s_294_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_296_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_297_: u8 = 0;
    let mut v___x_298_: u8 = 0;
    let mut v___y_300_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_301_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_302_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_303_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_304_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_305_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_306_: u8 = 0;
    let mut v___x_307_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_308_: u8 = 0;
    let mut v___x_309_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_310_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_311_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_312_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_313_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_314_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_315_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_316_: u8 = 0;
    let mut v___x_317_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_318_: u8 = 0;
    let mut v___x_319_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_298_ = lean_nat_dec_lt(v_curr_267_, v_w_265_);
                if v___x_298_ == 0 {
                    leanh::lean_dec_ref(v_discr_268_);
                    leanh::lean_dec(v_curr_267_);
                    leanh::lean_dec_ref(v_inst_264_);
                    leanh::lean_dec_ref(v_inst_263_);
                    v___x_310_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_310_, 0, v_aig_266_);
                    leanh::lean_ctor_set(v___x_310_, 1, v_s_271_);
                    return v___x_310_;
                } else {
                    v_ref_311_ = lean_array_fget_borrowed(v_lhs_269_, v_curr_267_);
                    v___x_312_ = leanh::lean_unsigned_to_nat(1);
                    v___x_313_ = lean_nat_shiftr(v_ref_311_, v___x_312_);
                    v___x_314_ = lean_nat_land(v___x_312_, v_ref_311_);
                    v___x_315_ = leanh::lean_unsigned_to_nat(0);
                    v___x_316_ = lean_nat_dec_eq(v___x_314_, v___x_315_);
                    leanh::lean_dec(v___x_314_);
                    if v___x_316_ == 0 {
                        v___x_317_ = leanh::lean_alloc_ctor(0, 1, (1) as u32);
                        leanh::lean_ctor_set(v___x_317_, 0, v___x_313_);
                        leanh::lean_ctor_set_uint8(
                            v___x_317_,
                            (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                            v___x_298_,
                        );
                        v___y_300_ = v___x_317_;
                        state = 4;
                        continue;
                    } else {
                        v___x_318_ = 0;
                        v___x_319_ = leanh::lean_alloc_ctor(0, 1, (1) as u32);
                        leanh::lean_ctor_set(v___x_319_, 0, v___x_313_);
                        leanh::lean_ctor_set_uint8(
                            v___x_319_,
                            (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                            v___x_318_,
                        );
                        v___y_300_ = v___x_319_;
                        state = 4;
                        continue;
                    }
                }
            }
            1 => {
                leanh::lean_inc_ref(v_discr_268_);
                v_input_275_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
                leanh::lean_ctor_set(v_input_275_, 0, v_discr_268_);
                leanh::lean_ctor_set(v_input_275_, 1, v___y_273_);
                leanh::lean_ctor_set(v_input_275_, 2, v___y_274_);
                leanh::lean_inc_ref(v_inst_264_);
                leanh::lean_inc_ref(v_inst_263_);
                v_res_276_ = l_Std_Sat_AIG_mkIfCached___redArg(
                    v_inst_263_,
                    v_inst_264_,
                    v_aig_266_,
                    v_input_275_,
                );
                v_ref_277_ = leanh::lean_ctor_get(v_res_276_, 1);
                leanh::lean_inc_ref(v_ref_277_);
                v_aig_278_ = leanh::lean_ctor_get(v_res_276_, 0);
                leanh::lean_inc_ref(v_aig_278_);
                leanh::lean_dec_ref(v_res_276_);
                v_gate_279_ = leanh::lean_ctor_get(v_discr_268_, 0);
                leanh::lean_inc(v_gate_279_);
                v_invert_280_ = leanh::lean_ctor_get_uint8(
                    v_discr_268_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                );
                leanh::lean_dec_ref(v_discr_268_);
                v_gate_281_ = leanh::lean_ctor_get(v_ref_277_, 0);
                v_invert_282_ = leanh::lean_ctor_get_uint8(
                    v_ref_277_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                );
                v_isSharedCheck_297_ = (!leanh::lean_is_exclusive(v_ref_277_)) as u8;
                if v_isSharedCheck_297_ == 0 {
                    v___x_284_ = v_ref_277_;
                    v_isShared_285_ = v_isSharedCheck_297_;
                    state = 2;
                    continue;
                } else {
                    leanh::lean_inc(v_gate_281_);
                    leanh::lean_dec(v_ref_277_);
                    v___x_284_ = leanh::lean_box(0);
                    v_isShared_285_ = v_isSharedCheck_297_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                if v_isShared_285_ == 0 {
                    leanh::lean_ctor_set(v___x_284_, 0, v_gate_279_);
                    v_discr_287_ = v___x_284_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_296_ = leanh::lean_alloc_ctor(0, 1, (1) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_296_, 0, v_gate_279_);
                    v_discr_287_ = v_reuseFailAlloc_296_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                leanh::lean_ctor_set_uint8(
                    v_discr_287_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                    v_invert_280_,
                );
                v___x_288_ = leanh::lean_unsigned_to_nat(1);
                v___x_289_ = lean_nat_add(v_curr_267_, v___x_288_);
                leanh::lean_dec(v_curr_267_);
                v___x_290_ = leanh::lean_unsigned_to_nat(2);
                v___x_291_ = lean_nat_mul(v_gate_281_, v___x_290_);
                leanh::lean_dec(v_gate_281_);
                v___x_292_ = l_Bool_toNat(v_invert_282_);
                v___x_293_ = lean_nat_lor(v___x_291_, v___x_292_);
                leanh::lean_dec(v___x_292_);
                leanh::lean_dec(v___x_291_);
                v_s_294_ = lean_array_push(v_s_271_, v___x_293_);
                v_aig_266_ = v_aig_278_;
                v_curr_267_ = v___x_289_;
                v_discr_268_ = v_discr_287_;
                v_s_271_ = v_s_294_;
                state = 0;
                continue;
            }
            4 => {
                v_ref_301_ = lean_array_fget_borrowed(v_rhs_270_, v_curr_267_);
                v___x_302_ = leanh::lean_unsigned_to_nat(1);
                v___x_303_ = lean_nat_shiftr(v_ref_301_, v___x_302_);
                v___x_304_ = lean_nat_land(v___x_302_, v_ref_301_);
                v___x_305_ = leanh::lean_unsigned_to_nat(0);
                v___x_306_ = lean_nat_dec_eq(v___x_304_, v___x_305_);
                leanh::lean_dec(v___x_304_);
                if v___x_306_ == 0 {
                    v___x_307_ = leanh::lean_alloc_ctor(0, 1, (1) as u32);
                    leanh::lean_ctor_set(v___x_307_, 0, v___x_303_);
                    leanh::lean_ctor_set_uint8(
                        v___x_307_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                        v___x_298_,
                    );
                    v___y_273_ = v___y_300_;
                    v___y_274_ = v___x_307_;
                    state = 1;
                    continue;
                } else {
                    v___x_308_ = 0;
                    v___x_309_ = leanh::lean_alloc_ctor(0, 1, (1) as u32);
                    leanh::lean_ctor_set(v___x_309_, 0, v___x_303_);
                    leanh::lean_ctor_set_uint8(
                        v___x_309_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                        v___x_308_,
                    );
                    v___y_273_ = v___y_300_;
                    v___y_274_ = v___x_309_;
                    state = 1;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Sat_AIG_RefVec_ite_go___redArg___boxed(
    mut v_inst_320_: *mut leanh::LeanObject,
    mut v_inst_321_: *mut leanh::LeanObject,
    mut v_w_322_: *mut leanh::LeanObject,
    mut v_aig_323_: *mut leanh::LeanObject,
    mut v_curr_324_: *mut leanh::LeanObject,
    mut v_discr_325_: *mut leanh::LeanObject,
    mut v_lhs_326_: *mut leanh::LeanObject,
    mut v_rhs_327_: *mut leanh::LeanObject,
    mut v_s_328_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_329_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_329_ = l_Std_Sat_AIG_RefVec_ite_go___redArg(
        v_inst_320_,
        v_inst_321_,
        v_w_322_,
        v_aig_323_,
        v_curr_324_,
        v_discr_325_,
        v_lhs_326_,
        v_rhs_327_,
        v_s_328_,
    );
    leanh::lean_dec_ref(v_rhs_327_);
    leanh::lean_dec_ref(v_lhs_326_);
    leanh::lean_dec(v_w_322_);
    return v_res_329_;
}
pub unsafe fn l_Std_Sat_AIG_RefVec_ite_go(
    mut v_00_u03b1_330_: *mut leanh::LeanObject,
    mut v_inst_331_: *mut leanh::LeanObject,
    mut v_inst_332_: *mut leanh::LeanObject,
    mut v_w_333_: *mut leanh::LeanObject,
    mut v_aig_334_: *mut leanh::LeanObject,
    mut v_curr_335_: *mut leanh::LeanObject,
    mut v_hcurr_336_: *mut leanh::LeanObject,
    mut v_discr_337_: *mut leanh::LeanObject,
    mut v_lhs_338_: *mut leanh::LeanObject,
    mut v_rhs_339_: *mut leanh::LeanObject,
    mut v_s_340_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_341_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_341_ = l_Std_Sat_AIG_RefVec_ite_go___redArg(
        v_inst_331_,
        v_inst_332_,
        v_w_333_,
        v_aig_334_,
        v_curr_335_,
        v_discr_337_,
        v_lhs_338_,
        v_rhs_339_,
        v_s_340_,
    );
    return v___x_341_;
}
pub unsafe fn l_Std_Sat_AIG_RefVec_ite_go___boxed(
    mut v_00_u03b1_342_: *mut leanh::LeanObject,
    mut v_inst_343_: *mut leanh::LeanObject,
    mut v_inst_344_: *mut leanh::LeanObject,
    mut v_w_345_: *mut leanh::LeanObject,
    mut v_aig_346_: *mut leanh::LeanObject,
    mut v_curr_347_: *mut leanh::LeanObject,
    mut v_hcurr_348_: *mut leanh::LeanObject,
    mut v_discr_349_: *mut leanh::LeanObject,
    mut v_lhs_350_: *mut leanh::LeanObject,
    mut v_rhs_351_: *mut leanh::LeanObject,
    mut v_s_352_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_353_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_353_ = l_Std_Sat_AIG_RefVec_ite_go(
        v_00_u03b1_342_,
        v_inst_343_,
        v_inst_344_,
        v_w_345_,
        v_aig_346_,
        v_curr_347_,
        v_hcurr_348_,
        v_discr_349_,
        v_lhs_350_,
        v_rhs_351_,
        v_s_352_,
    );
    leanh::lean_dec_ref(v_rhs_351_);
    leanh::lean_dec_ref(v_lhs_350_);
    leanh::lean_dec(v_w_345_);
    return v_res_353_;
}
pub unsafe fn l_Std_Sat_AIG_RefVec_ite___redArg(
    mut v_inst_354_: *mut leanh::LeanObject,
    mut v_inst_355_: *mut leanh::LeanObject,
    mut v_w_356_: *mut leanh::LeanObject,
    mut v_aig_357_: *mut leanh::LeanObject,
    mut v_input_358_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_discr_359_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_lhs_360_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_rhs_361_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_362_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_363_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_364_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_discr_359_ = leanh::lean_ctor_get(v_input_358_, 0);
    leanh::lean_inc_ref(v_discr_359_);
    v_lhs_360_ = leanh::lean_ctor_get(v_input_358_, 1);
    leanh::lean_inc_ref(v_lhs_360_);
    v_rhs_361_ = leanh::lean_ctor_get(v_input_358_, 2);
    leanh::lean_inc_ref(v_rhs_361_);
    leanh::lean_dec_ref(v_input_358_);
    v___x_362_ = leanh::lean_unsigned_to_nat(0);
    v___x_363_ = lean_mk_empty_array_with_capacity(v_w_356_);
    v___x_364_ = l_Std_Sat_AIG_RefVec_ite_go___redArg(
        v_inst_354_,
        v_inst_355_,
        v_w_356_,
        v_aig_357_,
        v___x_362_,
        v_discr_359_,
        v_lhs_360_,
        v_rhs_361_,
        v___x_363_,
    );
    leanh::lean_dec_ref(v_rhs_361_);
    leanh::lean_dec_ref(v_lhs_360_);
    return v___x_364_;
}
pub unsafe fn l_Std_Sat_AIG_RefVec_ite___redArg___boxed(
    mut v_inst_365_: *mut leanh::LeanObject,
    mut v_inst_366_: *mut leanh::LeanObject,
    mut v_w_367_: *mut leanh::LeanObject,
    mut v_aig_368_: *mut leanh::LeanObject,
    mut v_input_369_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_370_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_370_ = l_Std_Sat_AIG_RefVec_ite___redArg(
        v_inst_365_,
        v_inst_366_,
        v_w_367_,
        v_aig_368_,
        v_input_369_,
    );
    leanh::lean_dec(v_w_367_);
    return v_res_370_;
}
pub unsafe fn l_Std_Sat_AIG_RefVec_ite(
    mut v_00_u03b1_371_: *mut leanh::LeanObject,
    mut v_inst_372_: *mut leanh::LeanObject,
    mut v_inst_373_: *mut leanh::LeanObject,
    mut v_w_374_: *mut leanh::LeanObject,
    mut v_aig_375_: *mut leanh::LeanObject,
    mut v_input_376_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_377_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_377_ = l_Std_Sat_AIG_RefVec_ite___redArg(
        v_inst_372_,
        v_inst_373_,
        v_w_374_,
        v_aig_375_,
        v_input_376_,
    );
    return v___x_377_;
}
pub unsafe fn l_Std_Sat_AIG_RefVec_ite___boxed(
    mut v_00_u03b1_378_: *mut leanh::LeanObject,
    mut v_inst_379_: *mut leanh::LeanObject,
    mut v_inst_380_: *mut leanh::LeanObject,
    mut v_w_381_: *mut leanh::LeanObject,
    mut v_aig_382_: *mut leanh::LeanObject,
    mut v_input_383_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_384_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_384_ = l_Std_Sat_AIG_RefVec_ite(
        v_00_u03b1_378_,
        v_inst_379_,
        v_inst_380_,
        v_w_381_,
        v_aig_382_,
        v_input_383_,
    );
    leanh::lean_dec(v_w_381_);
    return v_res_384_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Std_Sat_AIG_If(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Std_Sat_AIG_LawfulVecOperator(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Omega(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Std_Sat_AIG_If(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_meta_initialized = true;
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Std_Sat_AIG_If(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Std_Sat_AIG_LawfulVecOperator(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_Omega(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Std_Sat_AIG_If(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = meta_initialize_Std_Sat_AIG_If(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return initialize_Std_Sat_AIG_If(builtin);
}