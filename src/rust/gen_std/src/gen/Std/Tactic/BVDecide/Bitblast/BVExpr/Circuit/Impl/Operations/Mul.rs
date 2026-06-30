// Lean compiler output
// Module: Std.Tactic.BVDecide.Bitblast.BVExpr.Circuit.Impl.Operations.Mul
// Imports: Std.Tactic.BVDecide.Bitblast.BVExpr.Circuit.Impl.Operations.Add Std.Tactic.BVDecide.Bitblast.BVExpr.Circuit.Impl.Operations.ShiftLeft Std.Tactic.BVDecide.Bitblast.BVExpr.Circuit.Impl.Const Init.Omega
use crate::ffi::{
    lean_array_fget_borrowed, lean_nat_add, lean_nat_dec_eq, lean_nat_dec_lt, lean_nat_land,
    lean_nat_shiftr,
};
use crate::r#gen::Init::Omega::{initialize_Init_Omega, runtime_initialize_Init_Omega};
use crate::r#gen::Init::Prelude::l_BitVec_ofNat;
use crate::r#gen::Std::Sat::AIG::Basic::l_Std_Sat_AIG_isConstant___redArg;
use crate::r#gen::Std::Sat::AIG::If::l_Std_Sat_AIG_RefVec_ite___redArg;
use crate::r#gen::Std::Sat::AIG::RefVec::{
    l_Std_Sat_AIG_RefVec_countKnown___redArg, l_Std_Sat_AIG_RefVec_empty,
};
use crate::r#gen::Std::Tactic::BVDecide::Bitblast::BVExpr::Circuit::Impl::Const::{
    initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Const,
    l_Std_Tactic_BVDecide_BVExpr_bitblast_blastConst___redArg,
    runtime_initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Const,
};
use crate::r#gen::Std::Tactic::BVDecide::Bitblast::BVExpr::Circuit::Impl::Operations::Add::{
    initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Operations_Add,
    l_Std_Tactic_BVDecide_BVExpr_bitblast_blastAdd___redArg,
    runtime_initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Operations_Add,
};
use crate::r#gen::Std::Tactic::BVDecide::Bitblast::BVExpr::Circuit::Impl::Operations::ShiftLeft::{
    initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Operations_ShiftLeft,
    l_Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftLeftConst___redArg,
    runtime_initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Operations_ShiftLeft,
};
pub unsafe fn l_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___redArg(
    mut v_inst_179_: *mut leanh::LeanObject,
    mut v_inst_180_: *mut leanh::LeanObject,
    mut v_w_181_: *mut leanh::LeanObject,
    mut v_aig_182_: *mut leanh::LeanObject,
    mut v_lhs_183_: *mut leanh::LeanObject,
    mut v_rhs_184_: *mut leanh::LeanObject,
    mut v_curr_185_: *mut leanh::LeanObject,
    mut v_acc_186_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___y_188_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_189_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_190_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_191_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_res_192_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_aig_193_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_vec_194_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_195_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_196_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_198_: u8 = 0;
    let mut v___y_200_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_201_: u8 = 0;
    let mut v___x_202_: u8 = 0;
    let mut v___x_203_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_res_204_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_aig_205_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_vec_206_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_208_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_209_: u8 = 0;
    let mut v___x_211_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_res_212_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_aig_213_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_vec_214_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_215_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_216_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_217_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_218_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_219_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_220_: u8 = 0;
    let mut v___x_221_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_222_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_223_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_224_: u8 = 0;
    let mut v___x_225_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_226_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_228_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_229_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_230_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_231_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_232_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_233_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_234_: u8 = 0;
    let mut v___x_235_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_236_: u8 = 0;
    let mut v___x_237_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_198_ = lean_nat_dec_lt(v_curr_185_, v_w_181_);
                if v___x_198_ == 0 {
                    leanh::lean_dec(v_curr_185_);
                    leanh::lean_dec_ref(v_lhs_183_);
                    leanh::lean_dec_ref(v_inst_180_);
                    leanh::lean_dec_ref(v_inst_179_);
                    v___x_228_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_228_, 0, v_aig_182_);
                    leanh::lean_ctor_set(v___x_228_, 1, v_acc_186_);
                    return v___x_228_;
                } else {
                    v_ref_229_ = lean_array_fget_borrowed(v_rhs_184_, v_curr_185_);
                    v___x_230_ = leanh::lean_unsigned_to_nat(1);
                    v___x_231_ = lean_nat_shiftr(v_ref_229_, v___x_230_);
                    v___x_232_ = lean_nat_land(v___x_230_, v_ref_229_);
                    v___x_233_ = leanh::lean_unsigned_to_nat(0);
                    v___x_234_ = lean_nat_dec_eq(v___x_232_, v___x_233_);
                    leanh::lean_dec(v___x_232_);
                    if v___x_234_ == 0 {
                        v___x_235_ = leanh::lean_alloc_ctor(0, 1, (1) as u32);
                        leanh::lean_ctor_set(v___x_235_, 0, v___x_231_);
                        leanh::lean_ctor_set_uint8(
                            v___x_235_,
                            (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                            v___x_198_,
                        );
                        v___y_200_ = v___x_235_;
                        state = 2;
                        continue;
                    } else {
                        v___x_236_ = 0;
                        v___x_237_ = leanh::lean_alloc_ctor(0, 1, (1) as u32);
                        leanh::lean_ctor_set(v___x_237_, 0, v___x_231_);
                        leanh::lean_ctor_set_uint8(
                            v___x_237_,
                            (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                            v___x_236_,
                        );
                        v___y_200_ = v___x_237_;
                        state = 2;
                        continue;
                    }
                }
            }
            1 => {
                v___x_191_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
                leanh::lean_ctor_set(v___x_191_, 0, v___y_190_);
                leanh::lean_ctor_set(v___x_191_, 1, v___y_188_);
                leanh::lean_ctor_set(v___x_191_, 2, v_acc_186_);
                leanh::lean_inc_ref(v_inst_180_);
                leanh::lean_inc_ref(v_inst_179_);
                v_res_192_ = l_Std_Sat_AIG_RefVec_ite___redArg(
                    v_inst_179_,
                    v_inst_180_,
                    v_w_181_,
                    v___y_189_,
                    v___x_191_,
                );
                v_aig_193_ = leanh::lean_ctor_get(v_res_192_, 0);
                leanh::lean_inc_ref(v_aig_193_);
                v_vec_194_ = leanh::lean_ctor_get(v_res_192_, 1);
                leanh::lean_inc_ref(v_vec_194_);
                leanh::lean_dec_ref(v_res_192_);
                v___x_195_ = leanh::lean_unsigned_to_nat(1);
                v___x_196_ = lean_nat_add(v_curr_185_, v___x_195_);
                leanh::lean_dec(v_curr_185_);
                v_aig_182_ = v_aig_193_;
                v_curr_185_ = v___x_196_;
                v_acc_186_ = v_vec_194_;
                state = 0;
                continue;
            }
            2 => {
                v___x_201_ = 0;
                v___x_202_ = l_Std_Sat_AIG_isConstant___redArg(v_aig_182_, v___y_200_, v___x_201_);
                leanh::lean_dec_ref(v___y_200_);
                if v___x_202_ == 0 {
                    leanh::lean_inc(v_curr_185_);
                    leanh::lean_inc_ref(v_lhs_183_);
                    v___x_203_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_203_, 0, v_lhs_183_);
                    leanh::lean_ctor_set(v___x_203_, 1, v_curr_185_);
                    v_res_204_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftLeftConst___redArg(
                        v_w_181_, v_aig_182_, v___x_203_,
                    );
                    leanh::lean_dec_ref_known(v___x_203_, 2);
                    v_aig_205_ = leanh::lean_ctor_get(v_res_204_, 0);
                    v_vec_206_ = leanh::lean_ctor_get(v_res_204_, 1);
                    v_isSharedCheck_224_ = (!leanh::lean_is_exclusive(v_res_204_)) as u8;
                    if v_isSharedCheck_224_ == 0 {
                        v___x_208_ = v_res_204_;
                        v_isShared_209_ = v_isSharedCheck_224_;
                        state = 3;
                        continue;
                    } else {
                        leanh::lean_inc(v_vec_206_);
                        leanh::lean_inc(v_aig_205_);
                        leanh::lean_dec(v_res_204_);
                        v___x_208_ = leanh::lean_box(0);
                        v_isShared_209_ = v_isSharedCheck_224_;
                        state = 3;
                        continue;
                    }
                } else {
                    v___x_225_ = leanh::lean_unsigned_to_nat(1);
                    v___x_226_ = lean_nat_add(v_curr_185_, v___x_225_);
                    leanh::lean_dec(v_curr_185_);
                    v_curr_185_ = v___x_226_;
                    state = 0;
                    continue;
                }
            }
            3 => {
                leanh::lean_inc_ref(v_acc_186_);
                if v_isShared_209_ == 0 {
                    leanh::lean_ctor_set(v___x_208_, 0, v_acc_186_);
                    v___x_211_ = v___x_208_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_223_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_223_, 0, v_acc_186_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_223_, 1, v_vec_206_);
                    v___x_211_ = v_reuseFailAlloc_223_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                leanh::lean_inc_ref(v_inst_180_);
                leanh::lean_inc_ref(v_inst_179_);
                v_res_212_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastAdd___redArg(
                    v_inst_179_,
                    v_inst_180_,
                    v_w_181_,
                    v_aig_205_,
                    v___x_211_,
                );
                v_aig_213_ = leanh::lean_ctor_get(v_res_212_, 0);
                leanh::lean_inc_ref(v_aig_213_);
                v_vec_214_ = leanh::lean_ctor_get(v_res_212_, 1);
                leanh::lean_inc_ref(v_vec_214_);
                leanh::lean_dec_ref(v_res_212_);
                v_ref_215_ = lean_array_fget_borrowed(v_rhs_184_, v_curr_185_);
                v___x_216_ = leanh::lean_unsigned_to_nat(1);
                v___x_217_ = lean_nat_shiftr(v_ref_215_, v___x_216_);
                v___x_218_ = lean_nat_land(v___x_216_, v_ref_215_);
                v___x_219_ = leanh::lean_unsigned_to_nat(0);
                v___x_220_ = lean_nat_dec_eq(v___x_218_, v___x_219_);
                leanh::lean_dec(v___x_218_);
                if v___x_220_ == 0 {
                    v___x_221_ = leanh::lean_alloc_ctor(0, 1, (1) as u32);
                    leanh::lean_ctor_set(v___x_221_, 0, v___x_217_);
                    leanh::lean_ctor_set_uint8(
                        v___x_221_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                        v___x_198_,
                    );
                    v___y_188_ = v_vec_214_;
                    v___y_189_ = v_aig_213_;
                    v___y_190_ = v___x_221_;
                    state = 1;
                    continue;
                } else {
                    v___x_222_ = leanh::lean_alloc_ctor(0, 1, (1) as u32);
                    leanh::lean_ctor_set(v___x_222_, 0, v___x_217_);
                    leanh::lean_ctor_set_uint8(
                        v___x_222_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                        v___x_202_,
                    );
                    v___y_188_ = v_vec_214_;
                    v___y_189_ = v_aig_213_;
                    v___y_190_ = v___x_222_;
                    state = 1;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___redArg___boxed(
    mut v_inst_238_: *mut leanh::LeanObject,
    mut v_inst_239_: *mut leanh::LeanObject,
    mut v_w_240_: *mut leanh::LeanObject,
    mut v_aig_241_: *mut leanh::LeanObject,
    mut v_lhs_242_: *mut leanh::LeanObject,
    mut v_rhs_243_: *mut leanh::LeanObject,
    mut v_curr_244_: *mut leanh::LeanObject,
    mut v_acc_245_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_246_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_246_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___redArg(
        v_inst_238_,
        v_inst_239_,
        v_w_240_,
        v_aig_241_,
        v_lhs_242_,
        v_rhs_243_,
        v_curr_244_,
        v_acc_245_,
    );
    leanh::lean_dec_ref(v_rhs_243_);
    leanh::lean_dec(v_w_240_);
    return v_res_246_;
}
pub unsafe fn l_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go(
    mut v_00_u03b1_247_: *mut leanh::LeanObject,
    mut v_inst_248_: *mut leanh::LeanObject,
    mut v_inst_249_: *mut leanh::LeanObject,
    mut v_w_250_: *mut leanh::LeanObject,
    mut v_aig_251_: *mut leanh::LeanObject,
    mut v_lhs_252_: *mut leanh::LeanObject,
    mut v_rhs_253_: *mut leanh::LeanObject,
    mut v_curr_254_: *mut leanh::LeanObject,
    mut v_acc_255_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_256_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_256_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___redArg(
        v_inst_248_,
        v_inst_249_,
        v_w_250_,
        v_aig_251_,
        v_lhs_252_,
        v_rhs_253_,
        v_curr_254_,
        v_acc_255_,
    );
    return v___x_256_;
}
pub unsafe fn l_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___boxed(
    mut v_00_u03b1_257_: *mut leanh::LeanObject,
    mut v_inst_258_: *mut leanh::LeanObject,
    mut v_inst_259_: *mut leanh::LeanObject,
    mut v_w_260_: *mut leanh::LeanObject,
    mut v_aig_261_: *mut leanh::LeanObject,
    mut v_lhs_262_: *mut leanh::LeanObject,
    mut v_rhs_263_: *mut leanh::LeanObject,
    mut v_curr_264_: *mut leanh::LeanObject,
    mut v_acc_265_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_266_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_266_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go(
        v_00_u03b1_257_,
        v_inst_258_,
        v_inst_259_,
        v_w_260_,
        v_aig_261_,
        v_lhs_262_,
        v_rhs_263_,
        v_curr_264_,
        v_acc_265_,
    );
    leanh::lean_dec_ref(v_rhs_263_);
    leanh::lean_dec(v_w_260_);
    return v_res_266_;
}
pub unsafe fn l_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_blast___redArg(
    mut v_inst_267_: *mut leanh::LeanObject,
    mut v_inst_268_: *mut leanh::LeanObject,
    mut v_w_269_: *mut leanh::LeanObject,
    mut v_aig_270_: *mut leanh::LeanObject,
    mut v_input_271_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_272_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_273_: u8 = 0;
    let mut v_lhs_274_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_rhs_275_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_276_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_zero_277_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_279_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_280_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_res_281_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_aig_282_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_vec_283_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_284_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_285_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_286_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_287_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_288_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_289_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_290_: u8 = 0;
    let mut v___x_291_: u8 = 0;
    let mut v___x_292_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_293_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_294_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_295_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_272_ = leanh::lean_unsigned_to_nat(0);
                v___x_273_ = lean_nat_dec_eq(v_w_269_, v___x_272_);
                if v___x_273_ == 0 {
                    v_lhs_274_ = leanh::lean_ctor_get(v_input_271_, 0);
                    leanh::lean_inc_ref(v_lhs_274_);
                    v_rhs_275_ = leanh::lean_ctor_get(v_input_271_, 1);
                    leanh::lean_inc_ref(v_rhs_275_);
                    leanh::lean_dec_ref(v_input_271_);
                    v___x_276_ = l_BitVec_ofNat(v_w_269_, v___x_272_);
                    v_zero_277_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastConst___redArg(
                        v_w_269_, v___x_276_,
                    );
                    leanh::lean_dec(v___x_276_);
                    v_ref_286_ = lean_array_fget_borrowed(v_rhs_275_, v___x_272_);
                    v___x_287_ = leanh::lean_unsigned_to_nat(1);
                    v___x_288_ = lean_nat_shiftr(v_ref_286_, v___x_287_);
                    v___x_289_ = lean_nat_land(v___x_287_, v_ref_286_);
                    v___x_290_ = lean_nat_dec_eq(v___x_289_, v___x_272_);
                    leanh::lean_dec(v___x_289_);
                    if v___x_290_ == 0 {
                        v___x_291_ = 1;
                        v___x_292_ = leanh::lean_alloc_ctor(0, 1, (1) as u32);
                        leanh::lean_ctor_set(v___x_292_, 0, v___x_288_);
                        leanh::lean_ctor_set_uint8(
                            v___x_292_,
                            (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                            v___x_291_,
                        );
                        v___y_279_ = v___x_292_;
                        state = 1;
                        continue;
                    } else {
                        v___x_293_ = leanh::lean_alloc_ctor(0, 1, (1) as u32);
                        leanh::lean_ctor_set(v___x_293_, 0, v___x_288_);
                        leanh::lean_ctor_set_uint8(
                            v___x_293_,
                            (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                            v___x_273_,
                        );
                        v___y_279_ = v___x_293_;
                        state = 1;
                        continue;
                    }
                } else {
                    leanh::lean_dec_ref(v_input_271_);
                    v___x_294_ = l_Std_Sat_AIG_RefVec_empty(
                        leanh::lean_box(0),
                        v_inst_267_,
                        v_inst_268_,
                        v_aig_270_,
                    );
                    leanh::lean_dec_ref(v_inst_268_);
                    leanh::lean_dec_ref(v_inst_267_);
                    v___x_295_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_295_, 0, v_aig_270_);
                    leanh::lean_ctor_set(v___x_295_, 1, v___x_294_);
                    return v___x_295_;
                }
            }
            1 => {
                leanh::lean_inc_ref(v_lhs_274_);
                v___x_280_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
                leanh::lean_ctor_set(v___x_280_, 0, v___y_279_);
                leanh::lean_ctor_set(v___x_280_, 1, v_lhs_274_);
                leanh::lean_ctor_set(v___x_280_, 2, v_zero_277_);
                leanh::lean_inc_ref(v_inst_268_);
                leanh::lean_inc_ref(v_inst_267_);
                v_res_281_ = l_Std_Sat_AIG_RefVec_ite___redArg(
                    v_inst_267_,
                    v_inst_268_,
                    v_w_269_,
                    v_aig_270_,
                    v___x_280_,
                );
                v_aig_282_ = leanh::lean_ctor_get(v_res_281_, 0);
                leanh::lean_inc_ref(v_aig_282_);
                v_vec_283_ = leanh::lean_ctor_get(v_res_281_, 1);
                leanh::lean_inc_ref(v_vec_283_);
                leanh::lean_dec_ref(v_res_281_);
                v___x_284_ = leanh::lean_unsigned_to_nat(1);
                v___x_285_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___redArg(
                    v_inst_267_,
                    v_inst_268_,
                    v_w_269_,
                    v_aig_282_,
                    v_lhs_274_,
                    v_rhs_275_,
                    v___x_284_,
                    v_vec_283_,
                );
                leanh::lean_dec_ref(v_rhs_275_);
                return v___x_285_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_blast___redArg___boxed(
    mut v_inst_296_: *mut leanh::LeanObject,
    mut v_inst_297_: *mut leanh::LeanObject,
    mut v_w_298_: *mut leanh::LeanObject,
    mut v_aig_299_: *mut leanh::LeanObject,
    mut v_input_300_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_301_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_301_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_blast___redArg(
        v_inst_296_,
        v_inst_297_,
        v_w_298_,
        v_aig_299_,
        v_input_300_,
    );
    leanh::lean_dec(v_w_298_);
    return v_res_301_;
}
pub unsafe fn l_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_blast(
    mut v_00_u03b1_302_: *mut leanh::LeanObject,
    mut v_inst_303_: *mut leanh::LeanObject,
    mut v_inst_304_: *mut leanh::LeanObject,
    mut v_w_305_: *mut leanh::LeanObject,
    mut v_aig_306_: *mut leanh::LeanObject,
    mut v_input_307_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_308_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_308_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_blast___redArg(
        v_inst_303_,
        v_inst_304_,
        v_w_305_,
        v_aig_306_,
        v_input_307_,
    );
    return v___x_308_;
}
pub unsafe fn l_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_blast___boxed(
    mut v_00_u03b1_309_: *mut leanh::LeanObject,
    mut v_inst_310_: *mut leanh::LeanObject,
    mut v_inst_311_: *mut leanh::LeanObject,
    mut v_w_312_: *mut leanh::LeanObject,
    mut v_aig_313_: *mut leanh::LeanObject,
    mut v_input_314_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_315_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_315_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_blast(
        v_00_u03b1_309_,
        v_inst_310_,
        v_inst_311_,
        v_w_312_,
        v_aig_313_,
        v_input_314_,
    );
    leanh::lean_dec(v_w_312_);
    return v_res_315_;
}
pub unsafe fn l_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul___redArg(
    mut v_inst_316_: *mut leanh::LeanObject,
    mut v_inst_317_: *mut leanh::LeanObject,
    mut v_w_318_: *mut leanh::LeanObject,
    mut v_aig_319_: *mut leanh::LeanObject,
    mut v_input_320_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_lhs_321_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_rhs_322_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_323_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_324_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_325_: u8 = 0;
    let mut v___x_327_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_328_: u8 = 0;
    let mut v___x_330_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_331_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_332_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_333_: u8 = 0;
    let mut v_unused_334_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_335_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_336_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_lhs_321_ = leanh::lean_ctor_get(v_input_320_, 0);
                v_rhs_322_ = leanh::lean_ctor_get(v_input_320_, 1);
                v___x_323_ =
                    l_Std_Sat_AIG_RefVec_countKnown___redArg(v_w_318_, v_aig_319_, v_lhs_321_);
                v___x_324_ =
                    l_Std_Sat_AIG_RefVec_countKnown___redArg(v_w_318_, v_aig_319_, v_rhs_322_);
                v___x_325_ = lean_nat_dec_lt(v___x_323_, v___x_324_);
                leanh::lean_dec(v___x_324_);
                leanh::lean_dec(v___x_323_);
                if v___x_325_ == 0 {
                    leanh::lean_inc_ref(v_rhs_322_);
                    leanh::lean_inc_ref(v_lhs_321_);
                    v_isSharedCheck_333_ = (!leanh::lean_is_exclusive(v_input_320_)) as u8;
                    if v_isSharedCheck_333_ == 0 {
                        v_unused_334_ = leanh::lean_ctor_get(v_input_320_, 1);
                        leanh::lean_dec(v_unused_334_);
                        v_unused_335_ = leanh::lean_ctor_get(v_input_320_, 0);
                        leanh::lean_dec(v_unused_335_);
                        v___x_327_ = v_input_320_;
                        v_isShared_328_ = v_isSharedCheck_333_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_dec(v_input_320_);
                        v___x_327_ = leanh::lean_box(0);
                        v_isShared_328_ = v_isSharedCheck_333_;
                        state = 1;
                        continue;
                    }
                } else {
                    v___x_336_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_blast___redArg(
                        v_inst_316_,
                        v_inst_317_,
                        v_w_318_,
                        v_aig_319_,
                        v_input_320_,
                    );
                    return v___x_336_;
                }
            }
            1 => {
                if v_isShared_328_ == 0 {
                    leanh::lean_ctor_set(v___x_327_, 1, v_lhs_321_);
                    leanh::lean_ctor_set(v___x_327_, 0, v_rhs_322_);
                    v___x_330_ = v___x_327_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_332_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_332_, 0, v_rhs_322_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_332_, 1, v_lhs_321_);
                    v___x_330_ = v_reuseFailAlloc_332_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_331_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_blast___redArg(
                    v_inst_316_,
                    v_inst_317_,
                    v_w_318_,
                    v_aig_319_,
                    v___x_330_,
                );
                return v___x_331_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul___redArg___boxed(
    mut v_inst_337_: *mut leanh::LeanObject,
    mut v_inst_338_: *mut leanh::LeanObject,
    mut v_w_339_: *mut leanh::LeanObject,
    mut v_aig_340_: *mut leanh::LeanObject,
    mut v_input_341_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_342_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_342_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul___redArg(
        v_inst_337_,
        v_inst_338_,
        v_w_339_,
        v_aig_340_,
        v_input_341_,
    );
    leanh::lean_dec(v_w_339_);
    return v_res_342_;
}
pub unsafe fn l_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul(
    mut v_00_u03b1_343_: *mut leanh::LeanObject,
    mut v_inst_344_: *mut leanh::LeanObject,
    mut v_inst_345_: *mut leanh::LeanObject,
    mut v_w_346_: *mut leanh::LeanObject,
    mut v_aig_347_: *mut leanh::LeanObject,
    mut v_input_348_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_349_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_349_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul___redArg(
        v_inst_344_,
        v_inst_345_,
        v_w_346_,
        v_aig_347_,
        v_input_348_,
    );
    return v___x_349_;
}
pub unsafe fn l_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul___boxed(
    mut v_00_u03b1_350_: *mut leanh::LeanObject,
    mut v_inst_351_: *mut leanh::LeanObject,
    mut v_inst_352_: *mut leanh::LeanObject,
    mut v_w_353_: *mut leanh::LeanObject,
    mut v_aig_354_: *mut leanh::LeanObject,
    mut v_input_355_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_356_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_356_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul(
        v_00_u03b1_350_,
        v_inst_351_,
        v_inst_352_,
        v_w_353_,
        v_aig_354_,
        v_input_355_,
    );
    leanh::lean_dec(v_w_353_);
    return v_res_356_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Operations_Mul(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res =
        runtime_initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Operations_Add(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Operations_ShiftLeft(
        builtin,
    );
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Const(builtin);
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
pub unsafe fn meta_initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Operations_Mul(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_meta_initialized = true;
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Operations_Mul(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Operations_Add(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Operations_ShiftLeft(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Const(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_Omega(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res =
        runtime_initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Operations_Mul(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = meta_initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Operations_Mul(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Operations_Mul(builtin);
}