// Lean compiler output
// Module: Std.Tactic.BVDecide.Bitblast.BVExpr.Circuit.Impl.Operations.ShiftLeft
// Imports: Std.Tactic.BVDecide.Bitblast.BVExpr.Basic Std.Sat.AIG.If Init.Omega
use crate::r#gen::Init::Data::Bool::l_Bool_toNat;
use crate::r#gen::Init::Omega::{initialize_Init_Omega, runtime_initialize_Init_Omega};
use crate::r#gen::Std::Sat::AIG::If::{
    initialize_Std_Sat_AIG_If, l_Std_Sat_AIG_RefVec_ite___redArg, runtime_initialize_Std_Sat_AIG_If,
};
use crate::r#gen::Std::Tactic::BVDecide::Bitblast::BVExpr::Basic::{
    initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Basic,
    runtime_initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Basic,
};
use crate::lean_imports_rs::Init::Data::Nat::Bitwise::Basic::{
    lean_nat_land, lean_nat_lor, lean_nat_shiftr,
};
use crate::lean_imports_rs::Init::Prelude::{
    lean_array_fget_borrowed, lean_array_push, lean_mk_empty_array_with_capacity, lean_nat_add,
    lean_nat_dec_eq, lean_nat_dec_lt, lean_nat_mul, lean_nat_pow, lean_nat_sub,
};
static mut l_Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftLeftConst_go___redArg___closed__0_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftLeftConst_go___redArg___closed__0:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftLeftConst_go___redArg___closed__1_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftLeftConst_go___redArg___closed__1:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub unsafe fn _init_l_Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftLeftConst_go___redArg___closed__0()
-> *mut crate::leanh::LeanObject {
    let mut v___x_226_: u8 = 0;
    let mut v___x_227_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_226_ = 0;
    v___x_227_ = l_Bool_toNat(v___x_226_);
    return v___x_227_;
}
pub unsafe fn _init_l_Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftLeftConst_go___redArg___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_228_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_229_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_230_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_228_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftLeftConst_go___redArg___closed__0
        ),
        core::ptr::addr_of_mut!(
            l_Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftLeftConst_go___redArg___closed__0_once
        ),
        _init_l_Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftLeftConst_go___redArg___closed__0,
    );
    v___x_229_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_230_ = lean_nat_lor(v___x_229_, v___x_228_);
    return v___x_230_;
}
pub unsafe fn l_Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftLeftConst_go___redArg(
    mut v_w_231_: *mut crate::leanh::LeanObject,
    mut v_aig_232_: *mut crate::leanh::LeanObject,
    mut v_input_233_: *mut crate::leanh::LeanObject,
    mut v_distance_234_: *mut crate::leanh::LeanObject,
    mut v_curr_235_: *mut crate::leanh::LeanObject,
    mut v_s_236_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_gate_238_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_invert_239_: u8 = 0;
    let mut v___x_240_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_241_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_242_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_243_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_244_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_245_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_s_246_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_248_: u8 = 0;
    let mut v___x_249_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_250_: u8 = 0;
    let mut v___x_251_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_252_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_253_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_254_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_255_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_256_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_257_: u8 = 0;
    let mut v___x_258_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_259_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_260_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_s_261_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_248_ = lean_nat_dec_lt(v_curr_235_, v_w_231_);
                if v___x_248_ == 0 {
                    crate::leanh::lean_dec(v_curr_235_);
                    v___x_249_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_249_, 0, v_aig_232_);
                    crate::leanh::lean_ctor_set(v___x_249_, 1, v_s_236_);
                    return v___x_249_;
                } else {
                    v___x_250_ = lean_nat_dec_lt(v_curr_235_, v_distance_234_);
                    if v___x_250_ == 0 {
                        v___x_251_ = lean_nat_sub(v_curr_235_, v_distance_234_);
                        v_ref_252_ = lean_array_fget_borrowed(v_input_233_, v___x_251_);
                        crate::leanh::lean_dec(v___x_251_);
                        v___x_253_ = crate::leanh::lean_unsigned_to_nat(1);
                        v___x_254_ = lean_nat_shiftr(v_ref_252_, v___x_253_);
                        v___x_255_ = lean_nat_land(v___x_253_, v_ref_252_);
                        v___x_256_ = crate::leanh::lean_unsigned_to_nat(0);
                        v___x_257_ = lean_nat_dec_eq(v___x_255_, v___x_256_);
                        crate::leanh::lean_dec(v___x_255_);
                        if v___x_257_ == 0 {
                            v_gate_238_ = v___x_254_;
                            v_invert_239_ = v___x_248_;
                            state = 1;
                            continue;
                        } else {
                            v_gate_238_ = v___x_254_;
                            v_invert_239_ = v___x_250_;
                            state = 1;
                            continue;
                        }
                    } else {
                        v___x_258_ = crate::leanh::lean_unsigned_to_nat(1);
                        v___x_259_ = lean_nat_add(v_curr_235_, v___x_258_);
                        crate::leanh::lean_dec(v_curr_235_);
                        v___x_260_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftLeftConst_go___redArg___closed__1), core::ptr::addr_of_mut!(l_Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftLeftConst_go___redArg___closed__1_once), _init_l_Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftLeftConst_go___redArg___closed__1);
                        v_s_261_ = lean_array_push(v_s_236_, v___x_260_);
                        v_curr_235_ = v___x_259_;
                        v_s_236_ = v_s_261_;
                        state = 0;
                        continue;
                    }
                }
            }
            1 => {
                v___x_240_ = crate::leanh::lean_unsigned_to_nat(1);
                v___x_241_ = lean_nat_add(v_curr_235_, v___x_240_);
                crate::leanh::lean_dec(v_curr_235_);
                v___x_242_ = crate::leanh::lean_unsigned_to_nat(2);
                v___x_243_ = lean_nat_mul(v_gate_238_, v___x_242_);
                crate::leanh::lean_dec(v_gate_238_);
                v___x_244_ = l_Bool_toNat(v_invert_239_);
                v___x_245_ = lean_nat_lor(v___x_243_, v___x_244_);
                crate::leanh::lean_dec(v___x_244_);
                crate::leanh::lean_dec(v___x_243_);
                v_s_246_ = lean_array_push(v_s_236_, v___x_245_);
                v_curr_235_ = v___x_241_;
                v_s_236_ = v_s_246_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftLeftConst_go___redArg___boxed(
    mut v_w_263_: *mut crate::leanh::LeanObject,
    mut v_aig_264_: *mut crate::leanh::LeanObject,
    mut v_input_265_: *mut crate::leanh::LeanObject,
    mut v_distance_266_: *mut crate::leanh::LeanObject,
    mut v_curr_267_: *mut crate::leanh::LeanObject,
    mut v_s_268_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_269_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_269_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftLeftConst_go___redArg(
        v_w_263_,
        v_aig_264_,
        v_input_265_,
        v_distance_266_,
        v_curr_267_,
        v_s_268_,
    );
    crate::leanh::lean_dec(v_distance_266_);
    crate::leanh::lean_dec_ref(v_input_265_);
    crate::leanh::lean_dec(v_w_263_);
    return v_res_269_;
}
pub unsafe fn l_Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftLeftConst_go(
    mut v_00_u03b1_270_: *mut crate::leanh::LeanObject,
    mut v_inst_271_: *mut crate::leanh::LeanObject,
    mut v_inst_272_: *mut crate::leanh::LeanObject,
    mut v_w_273_: *mut crate::leanh::LeanObject,
    mut v_aig_274_: *mut crate::leanh::LeanObject,
    mut v_input_275_: *mut crate::leanh::LeanObject,
    mut v_distance_276_: *mut crate::leanh::LeanObject,
    mut v_curr_277_: *mut crate::leanh::LeanObject,
    mut v_hcurr_278_: *mut crate::leanh::LeanObject,
    mut v_s_279_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_280_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_280_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftLeftConst_go___redArg(
        v_w_273_,
        v_aig_274_,
        v_input_275_,
        v_distance_276_,
        v_curr_277_,
        v_s_279_,
    );
    return v___x_280_;
}
pub unsafe fn l_Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftLeftConst_go___boxed(
    mut v_00_u03b1_281_: *mut crate::leanh::LeanObject,
    mut v_inst_282_: *mut crate::leanh::LeanObject,
    mut v_inst_283_: *mut crate::leanh::LeanObject,
    mut v_w_284_: *mut crate::leanh::LeanObject,
    mut v_aig_285_: *mut crate::leanh::LeanObject,
    mut v_input_286_: *mut crate::leanh::LeanObject,
    mut v_distance_287_: *mut crate::leanh::LeanObject,
    mut v_curr_288_: *mut crate::leanh::LeanObject,
    mut v_hcurr_289_: *mut crate::leanh::LeanObject,
    mut v_s_290_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_291_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_291_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftLeftConst_go(
        v_00_u03b1_281_,
        v_inst_282_,
        v_inst_283_,
        v_w_284_,
        v_aig_285_,
        v_input_286_,
        v_distance_287_,
        v_curr_288_,
        v_hcurr_289_,
        v_s_290_,
    );
    crate::leanh::lean_dec(v_distance_287_);
    crate::leanh::lean_dec_ref(v_input_286_);
    crate::leanh::lean_dec(v_w_284_);
    crate::leanh::lean_dec_ref(v_inst_283_);
    crate::leanh::lean_dec_ref(v_inst_282_);
    return v_res_291_;
}
pub unsafe fn l_Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftLeftConst___redArg(
    mut v_w_292_: *mut crate::leanh::LeanObject,
    mut v_aig_293_: *mut crate::leanh::LeanObject,
    mut v_target_294_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_vec_295_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_distance_296_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_297_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_298_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_299_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_vec_295_ = crate::leanh::lean_ctor_get(v_target_294_, 0);
    v_distance_296_ = crate::leanh::lean_ctor_get(v_target_294_, 1);
    v___x_297_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_298_ = lean_mk_empty_array_with_capacity(v_w_292_);
    v___x_299_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftLeftConst_go___redArg(
        v_w_292_,
        v_aig_293_,
        v_vec_295_,
        v_distance_296_,
        v___x_297_,
        v___x_298_,
    );
    return v___x_299_;
}
pub unsafe fn l_Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftLeftConst___redArg___boxed(
    mut v_w_300_: *mut crate::leanh::LeanObject,
    mut v_aig_301_: *mut crate::leanh::LeanObject,
    mut v_target_302_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_303_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_303_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftLeftConst___redArg(
        v_w_300_,
        v_aig_301_,
        v_target_302_,
    );
    crate::leanh::lean_dec_ref(v_target_302_);
    crate::leanh::lean_dec(v_w_300_);
    return v_res_303_;
}
pub unsafe fn l_Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftLeftConst(
    mut v_00_u03b1_304_: *mut crate::leanh::LeanObject,
    mut v_inst_305_: *mut crate::leanh::LeanObject,
    mut v_inst_306_: *mut crate::leanh::LeanObject,
    mut v_w_307_: *mut crate::leanh::LeanObject,
    mut v_aig_308_: *mut crate::leanh::LeanObject,
    mut v_target_309_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_310_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_310_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftLeftConst___redArg(
        v_w_307_,
        v_aig_308_,
        v_target_309_,
    );
    return v___x_310_;
}
pub unsafe fn l_Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftLeftConst___boxed(
    mut v_00_u03b1_311_: *mut crate::leanh::LeanObject,
    mut v_inst_312_: *mut crate::leanh::LeanObject,
    mut v_inst_313_: *mut crate::leanh::LeanObject,
    mut v_w_314_: *mut crate::leanh::LeanObject,
    mut v_aig_315_: *mut crate::leanh::LeanObject,
    mut v_target_316_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_317_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_317_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftLeftConst(
        v_00_u03b1_311_,
        v_inst_312_,
        v_inst_313_,
        v_w_314_,
        v_aig_315_,
        v_target_316_,
    );
    crate::leanh::lean_dec_ref(v_target_316_);
    crate::leanh::lean_dec(v_w_314_);
    crate::leanh::lean_dec_ref(v_inst_313_);
    crate::leanh::lean_dec_ref(v_inst_312_);
    return v_res_317_;
}
pub unsafe fn l_Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftLeft_twoPowShift___redArg(
    mut v_inst_318_: *mut crate::leanh::LeanObject,
    mut v_inst_319_: *mut crate::leanh::LeanObject,
    mut v_w_320_: *mut crate::leanh::LeanObject,
    mut v_aig_321_: *mut crate::leanh::LeanObject,
    mut v_target_322_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_n_323_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_lhs_324_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_rhs_325_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_pow_326_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_327_: u8 = 0;
    let mut v___x_328_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_329_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_330_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_331_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_res_332_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_aig_333_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_vec_334_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_336_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_337_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_338_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_339_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_340_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_341_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_342_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_343_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_344_: u8 = 0;
    let mut v___x_345_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_346_: u8 = 0;
    let mut v___x_347_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_n_323_ = crate::leanh::lean_ctor_get(v_target_322_, 0);
                v_lhs_324_ = crate::leanh::lean_ctor_get(v_target_322_, 1);
                v_rhs_325_ = crate::leanh::lean_ctor_get(v_target_322_, 2);
                v_pow_326_ = crate::leanh::lean_ctor_get(v_target_322_, 3);
                v___x_327_ = lean_nat_dec_lt(v_pow_326_, v_n_323_);
                if v___x_327_ == 0 {
                    crate::leanh::lean_dec_ref(v_inst_319_);
                    crate::leanh::lean_dec_ref(v_inst_318_);
                    crate::leanh::lean_inc_ref(v_lhs_324_);
                    v___x_328_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_328_, 0, v_aig_321_);
                    crate::leanh::lean_ctor_set(v___x_328_, 1, v_lhs_324_);
                    return v___x_328_;
                } else {
                    v___x_329_ = crate::leanh::lean_unsigned_to_nat(2);
                    v___x_330_ = lean_nat_pow(v___x_329_, v_pow_326_);
                    crate::leanh::lean_inc_ref(v_lhs_324_);
                    v___x_331_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_331_, 0, v_lhs_324_);
                    crate::leanh::lean_ctor_set(v___x_331_, 1, v___x_330_);
                    v_res_332_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftLeftConst___redArg(
                        v_w_320_, v_aig_321_, v___x_331_,
                    );
                    crate::leanh::lean_dec_ref_known(v___x_331_, 2);
                    v_aig_333_ = crate::leanh::lean_ctor_get(v_res_332_, 0);
                    crate::leanh::lean_inc_ref(v_aig_333_);
                    v_vec_334_ = crate::leanh::lean_ctor_get(v_res_332_, 1);
                    crate::leanh::lean_inc_ref(v_vec_334_);
                    crate::leanh::lean_dec_ref(v_res_332_);
                    v_ref_339_ = lean_array_fget_borrowed(v_rhs_325_, v_pow_326_);
                    v___x_340_ = crate::leanh::lean_unsigned_to_nat(1);
                    v___x_341_ = lean_nat_shiftr(v_ref_339_, v___x_340_);
                    v___x_342_ = lean_nat_land(v___x_340_, v_ref_339_);
                    v___x_343_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___x_344_ = lean_nat_dec_eq(v___x_342_, v___x_343_);
                    crate::leanh::lean_dec(v___x_342_);
                    if v___x_344_ == 0 {
                        v___x_345_ = crate::leanh::lean_alloc_ctor(0, 1, (1) as u32);
                        crate::leanh::lean_ctor_set(v___x_345_, 0, v___x_341_);
                        crate::leanh::lean_ctor_set_uint8(
                            v___x_345_,
                            (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                            v___x_327_,
                        );
                        v___y_336_ = v___x_345_;
                        state = 1;
                        continue;
                    } else {
                        v___x_346_ = 0;
                        v___x_347_ = crate::leanh::lean_alloc_ctor(0, 1, (1) as u32);
                        crate::leanh::lean_ctor_set(v___x_347_, 0, v___x_341_);
                        crate::leanh::lean_ctor_set_uint8(
                            v___x_347_,
                            (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                            v___x_346_,
                        );
                        v___y_336_ = v___x_347_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                crate::leanh::lean_inc_ref(v_lhs_324_);
                v___x_337_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_337_, 0, v___y_336_);
                crate::leanh::lean_ctor_set(v___x_337_, 1, v_vec_334_);
                crate::leanh::lean_ctor_set(v___x_337_, 2, v_lhs_324_);
                v___x_338_ = l_Std_Sat_AIG_RefVec_ite___redArg(
                    v_inst_318_,
                    v_inst_319_,
                    v_w_320_,
                    v_aig_333_,
                    v___x_337_,
                );
                return v___x_338_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftLeft_twoPowShift___redArg___boxed(
    mut v_inst_348_: *mut crate::leanh::LeanObject,
    mut v_inst_349_: *mut crate::leanh::LeanObject,
    mut v_w_350_: *mut crate::leanh::LeanObject,
    mut v_aig_351_: *mut crate::leanh::LeanObject,
    mut v_target_352_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_353_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_353_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftLeft_twoPowShift___redArg(
        v_inst_348_,
        v_inst_349_,
        v_w_350_,
        v_aig_351_,
        v_target_352_,
    );
    crate::leanh::lean_dec_ref(v_target_352_);
    crate::leanh::lean_dec(v_w_350_);
    return v_res_353_;
}
pub unsafe fn l_Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftLeft_twoPowShift(
    mut v_00_u03b1_354_: *mut crate::leanh::LeanObject,
    mut v_inst_355_: *mut crate::leanh::LeanObject,
    mut v_inst_356_: *mut crate::leanh::LeanObject,
    mut v_w_357_: *mut crate::leanh::LeanObject,
    mut v_aig_358_: *mut crate::leanh::LeanObject,
    mut v_target_359_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_360_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_360_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftLeft_twoPowShift___redArg(
        v_inst_355_,
        v_inst_356_,
        v_w_357_,
        v_aig_358_,
        v_target_359_,
    );
    return v___x_360_;
}
pub unsafe fn l_Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftLeft_twoPowShift___boxed(
    mut v_00_u03b1_361_: *mut crate::leanh::LeanObject,
    mut v_inst_362_: *mut crate::leanh::LeanObject,
    mut v_inst_363_: *mut crate::leanh::LeanObject,
    mut v_w_364_: *mut crate::leanh::LeanObject,
    mut v_aig_365_: *mut crate::leanh::LeanObject,
    mut v_target_366_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_367_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_367_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftLeft_twoPowShift(
        v_00_u03b1_361_,
        v_inst_362_,
        v_inst_363_,
        v_w_364_,
        v_aig_365_,
        v_target_366_,
    );
    crate::leanh::lean_dec_ref(v_target_366_);
    crate::leanh::lean_dec(v_w_364_);
    return v_res_367_;
}
pub unsafe fn l_Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftLeft_go___redArg(
    mut v_inst_368_: *mut crate::leanh::LeanObject,
    mut v_inst_369_: *mut crate::leanh::LeanObject,
    mut v_w_370_: *mut crate::leanh::LeanObject,
    mut v_n_371_: *mut crate::leanh::LeanObject,
    mut v_aig_372_: *mut crate::leanh::LeanObject,
    mut v_distance_373_: *mut crate::leanh::LeanObject,
    mut v_curr_374_: *mut crate::leanh::LeanObject,
    mut v_acc_375_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_376_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_377_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_378_: u8 = 0;
    let mut v___x_379_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_380_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_381_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_res_382_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_aig_383_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_vec_384_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_376_ = crate::leanh::lean_unsigned_to_nat(1);
                v___x_377_ = lean_nat_sub(v_n_371_, v___x_376_);
                v___x_378_ = lean_nat_dec_lt(v_curr_374_, v___x_377_);
                crate::leanh::lean_dec(v___x_377_);
                if v___x_378_ == 0 {
                    crate::leanh::lean_dec(v_curr_374_);
                    crate::leanh::lean_dec_ref(v_distance_373_);
                    crate::leanh::lean_dec(v_n_371_);
                    crate::leanh::lean_dec_ref(v_inst_369_);
                    crate::leanh::lean_dec_ref(v_inst_368_);
                    v___x_379_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_379_, 0, v_aig_372_);
                    crate::leanh::lean_ctor_set(v___x_379_, 1, v_acc_375_);
                    return v___x_379_;
                } else {
                    v___x_380_ = lean_nat_add(v_curr_374_, v___x_376_);
                    crate::leanh::lean_dec(v_curr_374_);
                    crate::leanh::lean_inc(v___x_380_);
                    crate::leanh::lean_inc_ref(v_distance_373_);
                    crate::leanh::lean_inc(v_n_371_);
                    v___x_381_ = crate::leanh::lean_alloc_ctor(0, 4, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_381_, 0, v_n_371_);
                    crate::leanh::lean_ctor_set(v___x_381_, 1, v_acc_375_);
                    crate::leanh::lean_ctor_set(v___x_381_, 2, v_distance_373_);
                    crate::leanh::lean_ctor_set(v___x_381_, 3, v___x_380_);
                    crate::leanh::lean_inc_ref(v_inst_369_);
                    crate::leanh::lean_inc_ref(v_inst_368_);
                    v_res_382_ =
                        l_Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftLeft_twoPowShift___redArg(
                            v_inst_368_,
                            v_inst_369_,
                            v_w_370_,
                            v_aig_372_,
                            v___x_381_,
                        );
                    crate::leanh::lean_dec_ref_known(v___x_381_, 4);
                    v_aig_383_ = crate::leanh::lean_ctor_get(v_res_382_, 0);
                    crate::leanh::lean_inc_ref(v_aig_383_);
                    v_vec_384_ = crate::leanh::lean_ctor_get(v_res_382_, 1);
                    crate::leanh::lean_inc_ref(v_vec_384_);
                    crate::leanh::lean_dec_ref(v_res_382_);
                    v_aig_372_ = v_aig_383_;
                    v_curr_374_ = v___x_380_;
                    v_acc_375_ = v_vec_384_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftLeft_go___redArg___boxed(
    mut v_inst_386_: *mut crate::leanh::LeanObject,
    mut v_inst_387_: *mut crate::leanh::LeanObject,
    mut v_w_388_: *mut crate::leanh::LeanObject,
    mut v_n_389_: *mut crate::leanh::LeanObject,
    mut v_aig_390_: *mut crate::leanh::LeanObject,
    mut v_distance_391_: *mut crate::leanh::LeanObject,
    mut v_curr_392_: *mut crate::leanh::LeanObject,
    mut v_acc_393_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_394_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_394_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftLeft_go___redArg(
        v_inst_386_,
        v_inst_387_,
        v_w_388_,
        v_n_389_,
        v_aig_390_,
        v_distance_391_,
        v_curr_392_,
        v_acc_393_,
    );
    crate::leanh::lean_dec(v_w_388_);
    return v_res_394_;
}
pub unsafe fn l_Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftLeft_go(
    mut v_00_u03b1_395_: *mut crate::leanh::LeanObject,
    mut v_inst_396_: *mut crate::leanh::LeanObject,
    mut v_inst_397_: *mut crate::leanh::LeanObject,
    mut v_w_398_: *mut crate::leanh::LeanObject,
    mut v_n_399_: *mut crate::leanh::LeanObject,
    mut v_aig_400_: *mut crate::leanh::LeanObject,
    mut v_distance_401_: *mut crate::leanh::LeanObject,
    mut v_curr_402_: *mut crate::leanh::LeanObject,
    mut v_acc_403_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_404_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_404_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftLeft_go___redArg(
        v_inst_396_,
        v_inst_397_,
        v_w_398_,
        v_n_399_,
        v_aig_400_,
        v_distance_401_,
        v_curr_402_,
        v_acc_403_,
    );
    return v___x_404_;
}
pub unsafe fn l_Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftLeft_go___boxed(
    mut v_00_u03b1_405_: *mut crate::leanh::LeanObject,
    mut v_inst_406_: *mut crate::leanh::LeanObject,
    mut v_inst_407_: *mut crate::leanh::LeanObject,
    mut v_w_408_: *mut crate::leanh::LeanObject,
    mut v_n_409_: *mut crate::leanh::LeanObject,
    mut v_aig_410_: *mut crate::leanh::LeanObject,
    mut v_distance_411_: *mut crate::leanh::LeanObject,
    mut v_curr_412_: *mut crate::leanh::LeanObject,
    mut v_acc_413_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_414_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_414_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftLeft_go(
        v_00_u03b1_405_,
        v_inst_406_,
        v_inst_407_,
        v_w_408_,
        v_n_409_,
        v_aig_410_,
        v_distance_411_,
        v_curr_412_,
        v_acc_413_,
    );
    crate::leanh::lean_dec(v_w_408_);
    return v_res_414_;
}
pub unsafe fn l_Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftLeft___redArg(
    mut v_inst_415_: *mut crate::leanh::LeanObject,
    mut v_inst_416_: *mut crate::leanh::LeanObject,
    mut v_w_417_: *mut crate::leanh::LeanObject,
    mut v_aig_418_: *mut crate::leanh::LeanObject,
    mut v_target_419_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_n_420_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_target_421_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_distance_422_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_423_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_424_: u8 = 0;
    v_n_420_ = crate::leanh::lean_ctor_get(v_target_419_, 0);
    crate::leanh::lean_inc(v_n_420_);
    v_target_421_ = crate::leanh::lean_ctor_get(v_target_419_, 1);
    crate::leanh::lean_inc_ref(v_target_421_);
    v_distance_422_ = crate::leanh::lean_ctor_get(v_target_419_, 2);
    crate::leanh::lean_inc_ref(v_distance_422_);
    crate::leanh::lean_dec_ref(v_target_419_);
    v___x_423_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_424_ = lean_nat_dec_eq(v_n_420_, v___x_423_);
    if v___x_424_ == 0 {
        let mut v___x_425_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_res_426_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_aig_427_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_vec_428_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_429_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_inc_ref(v_distance_422_);
        crate::leanh::lean_inc(v_n_420_);
        v___x_425_ = crate::leanh::lean_alloc_ctor(0, 4, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_425_, 0, v_n_420_);
        crate::leanh::lean_ctor_set(v___x_425_, 1, v_target_421_);
        crate::leanh::lean_ctor_set(v___x_425_, 2, v_distance_422_);
        crate::leanh::lean_ctor_set(v___x_425_, 3, v___x_423_);
        crate::leanh::lean_inc_ref(v_inst_416_);
        crate::leanh::lean_inc_ref(v_inst_415_);
        v_res_426_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftLeft_twoPowShift___redArg(
            v_inst_415_,
            v_inst_416_,
            v_w_417_,
            v_aig_418_,
            v___x_425_,
        );
        crate::leanh::lean_dec_ref_known(v___x_425_, 4);
        v_aig_427_ = crate::leanh::lean_ctor_get(v_res_426_, 0);
        crate::leanh::lean_inc_ref(v_aig_427_);
        v_vec_428_ = crate::leanh::lean_ctor_get(v_res_426_, 1);
        crate::leanh::lean_inc_ref(v_vec_428_);
        crate::leanh::lean_dec_ref(v_res_426_);
        v___x_429_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftLeft_go___redArg(
            v_inst_415_,
            v_inst_416_,
            v_w_417_,
            v_n_420_,
            v_aig_427_,
            v_distance_422_,
            v___x_423_,
            v_vec_428_,
        );
        return v___x_429_;
    } else {
        let mut v___x_430_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec_ref(v_distance_422_);
        crate::leanh::lean_dec(v_n_420_);
        crate::leanh::lean_dec_ref(v_inst_416_);
        crate::leanh::lean_dec_ref(v_inst_415_);
        v___x_430_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_430_, 0, v_aig_418_);
        crate::leanh::lean_ctor_set(v___x_430_, 1, v_target_421_);
        return v___x_430_;
    }
}
pub unsafe fn l_Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftLeft___redArg___boxed(
    mut v_inst_431_: *mut crate::leanh::LeanObject,
    mut v_inst_432_: *mut crate::leanh::LeanObject,
    mut v_w_433_: *mut crate::leanh::LeanObject,
    mut v_aig_434_: *mut crate::leanh::LeanObject,
    mut v_target_435_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_436_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_436_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftLeft___redArg(
        v_inst_431_,
        v_inst_432_,
        v_w_433_,
        v_aig_434_,
        v_target_435_,
    );
    crate::leanh::lean_dec(v_w_433_);
    return v_res_436_;
}
pub unsafe fn l_Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftLeft(
    mut v_00_u03b1_437_: *mut crate::leanh::LeanObject,
    mut v_inst_438_: *mut crate::leanh::LeanObject,
    mut v_inst_439_: *mut crate::leanh::LeanObject,
    mut v_w_440_: *mut crate::leanh::LeanObject,
    mut v_aig_441_: *mut crate::leanh::LeanObject,
    mut v_target_442_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_443_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_443_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftLeft___redArg(
        v_inst_438_,
        v_inst_439_,
        v_w_440_,
        v_aig_441_,
        v_target_442_,
    );
    return v___x_443_;
}
pub unsafe fn l_Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftLeft___boxed(
    mut v_00_u03b1_444_: *mut crate::leanh::LeanObject,
    mut v_inst_445_: *mut crate::leanh::LeanObject,
    mut v_inst_446_: *mut crate::leanh::LeanObject,
    mut v_w_447_: *mut crate::leanh::LeanObject,
    mut v_aig_448_: *mut crate::leanh::LeanObject,
    mut v_target_449_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_450_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_450_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftLeft(
        v_00_u03b1_444_,
        v_inst_445_,
        v_inst_446_,
        v_w_447_,
        v_aig_448_,
        v_target_449_,
    );
    crate::leanh::lean_dec(v_w_447_);
    return v_res_450_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Operations_ShiftLeft(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Basic(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Std_Sat_AIG_If(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Omega(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Operations_ShiftLeft(
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
pub unsafe fn initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Operations_ShiftLeft(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Basic(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Std_Sat_AIG_If(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Omega(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Operations_ShiftLeft(
        builtin,
    );
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Operations_ShiftLeft(
        builtin,
    );
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Operations_ShiftLeft(
        builtin,
    );
}
