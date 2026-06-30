// Lean compiler output
// Module: Std.Tactic.BVDecide.Bitblast.BVExpr.Circuit.Impl.Operations.Cpop
// Imports: Std.Tactic.BVDecide.Bitblast.BVExpr.Circuit.Impl.Const Std.Tactic.BVDecide.Bitblast.BVExpr.Circuit.Impl.Operations.Sub Std.Tactic.BVDecide.Bitblast.BVExpr.Circuit.Impl.Operations.Extract Std.Tactic.BVDecide.Bitblast.BVExpr.Circuit.Impl.Operations.Append Std.Tactic.BVDecide.Bitblast.BVExpr.Circuit.Impl.Operations.ZeroExtend Std.Sat.AIG.If Init.Omega
use crate::r#gen::Std::Tactic::BVDecide::Bitblast::BVExpr::Circuit::Impl::Const::{initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Const, l_Std_Tactic_BVDecide_BVExpr_bitblast_blastConst___redArg, runtime_initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Const};
use crate::r#gen::Std::Tactic::BVDecide::Bitblast::BVExpr::Circuit::Impl::Operations::Sub::{initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Operations_Sub, runtime_initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Operations_Sub};
use crate::r#gen::Std::Tactic::BVDecide::Bitblast::BVExpr::Circuit::Impl::Operations::Extract::{initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Operations_Extract, l_Std_Tactic_BVDecide_BVExpr_bitblast_blastExtract___redArg, runtime_initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Operations_Extract};
use crate::r#gen::Std::Tactic::BVDecide::Bitblast::BVExpr::Circuit::Impl::Operations::Append::{initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Operations_Append, l_Std_Tactic_BVDecide_BVExpr_bitblast_blastAppend___redArg, runtime_initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Operations_Append};
use crate::r#gen::Std::Tactic::BVDecide::Bitblast::BVExpr::Circuit::Impl::Operations::ZeroExtend::{initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Operations_ZeroExtend, l_Std_Tactic_BVDecide_BVExpr_bitblast_blastZeroExtend___redArg, runtime_initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Operations_ZeroExtend};
use crate::r#gen::Std::Sat::AIG::If::{initialize_Std_Sat_AIG_If, runtime_initialize_Std_Sat_AIG_If};
use crate::r#gen::Init::Omega::{initialize_Init_Omega, runtime_initialize_Init_Omega};
use crate::r#gen::Init::Prelude::l_BitVec_ofNat;
use crate::r#gen::Init::Data::Array::Basic::l_Array_append___redArg;
use crate::r#gen::Std::Tactic::BVDecide::Bitblast::BVExpr::Circuit::Impl::Operations::Add::l_Std_Tactic_BVDecide_BVExpr_bitblast_blastAdd___redArg;
use crate::ffi::{lean_nat_add, lean_nat_dec_lt, lean_nat_mul, lean_nat_shiftr, lean_nat_sub};
static mut l_Std_Tactic_BVDecide_BVExpr_bitblast_blastExtractAndExtend___redArg___closed__0_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_Tactic_BVDecide_BVExpr_bitblast_blastExtractAndExtend___redArg___closed__0:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Std_Tactic_BVDecide_BVExpr_bitblast_blastExtractAndExtend___redArg___closed__1_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_Tactic_BVDecide_BVExpr_bitblast_blastExtractAndExtend___redArg___closed__1:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub unsafe fn l_Std_Tactic_BVDecide_BVExpr_bitblast_blastExtractAndExtendBit___redArg(
    mut v_w_287_: *mut leanh::LeanObject,
    mut v_aig_288_: *mut leanh::LeanObject,
    mut v_target_289_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_start_290_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_x_291_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_292_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_293_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_res_294_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_aig_295_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_vec_296_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_298_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_299_: u8 = 0;
    let mut v___x_301_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_res_302_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_aig_303_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_vec_304_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_306_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_307_: u8 = 0;
    let mut v___x_309_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_310_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_311_: u8 = 0;
    let mut v_reuseFailAlloc_312_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_313_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_start_290_ = leanh::lean_ctor_get(v_target_289_, 0);
                v_x_291_ = leanh::lean_ctor_get(v_target_289_, 1);
                v___x_292_ = leanh::lean_unsigned_to_nat(1);
                leanh::lean_inc(v_start_290_);
                leanh::lean_inc_ref(v_x_291_);
                leanh::lean_inc(v_w_287_);
                v___x_293_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
                leanh::lean_ctor_set(v___x_293_, 0, v_w_287_);
                leanh::lean_ctor_set(v___x_293_, 1, v_x_291_);
                leanh::lean_ctor_set(v___x_293_, 2, v_start_290_);
                v_res_294_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastExtract___redArg(
                    v___x_292_, v_aig_288_, v___x_293_,
                );
                leanh::lean_dec_ref_known(v___x_293_, 3);
                v_aig_295_ = leanh::lean_ctor_get(v_res_294_, 0);
                v_vec_296_ = leanh::lean_ctor_get(v_res_294_, 1);
                v_isSharedCheck_313_ = (!leanh::lean_is_exclusive(v_res_294_)) as u8;
                if v_isSharedCheck_313_ == 0 {
                    v___x_298_ = v_res_294_;
                    v_isShared_299_ = v_isSharedCheck_313_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_vec_296_);
                    leanh::lean_inc(v_aig_295_);
                    leanh::lean_dec(v_res_294_);
                    v___x_298_ = leanh::lean_box(0);
                    v_isShared_299_ = v_isSharedCheck_313_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                if v_isShared_299_ == 0 {
                    leanh::lean_ctor_set(v___x_298_, 0, v___x_292_);
                    v___x_301_ = v___x_298_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_312_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_312_, 0, v___x_292_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_312_, 1, v_vec_296_);
                    v___x_301_ = v_reuseFailAlloc_312_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v_res_302_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastZeroExtend___redArg(
                    v_w_287_, v_aig_295_, v___x_301_,
                );
                leanh::lean_dec_ref(v___x_301_);
                leanh::lean_dec(v_w_287_);
                v_aig_303_ = leanh::lean_ctor_get(v_res_302_, 0);
                v_vec_304_ = leanh::lean_ctor_get(v_res_302_, 1);
                v_isSharedCheck_311_ = (!leanh::lean_is_exclusive(v_res_302_)) as u8;
                if v_isSharedCheck_311_ == 0 {
                    v___x_306_ = v_res_302_;
                    v_isShared_307_ = v_isSharedCheck_311_;
                    state = 3;
                    continue;
                } else {
                    leanh::lean_inc(v_vec_304_);
                    leanh::lean_inc(v_aig_303_);
                    leanh::lean_dec(v_res_302_);
                    v___x_306_ = leanh::lean_box(0);
                    v_isShared_307_ = v_isSharedCheck_311_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_307_ == 0 {
                    v___x_309_ = v___x_306_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_310_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_310_, 0, v_aig_303_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_310_, 1, v_vec_304_);
                    v___x_309_ = v_reuseFailAlloc_310_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_309_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Tactic_BVDecide_BVExpr_bitblast_blastExtractAndExtendBit___redArg___boxed(
    mut v_w_314_: *mut leanh::LeanObject,
    mut v_aig_315_: *mut leanh::LeanObject,
    mut v_target_316_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_317_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_317_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastExtractAndExtendBit___redArg(
        v_w_314_,
        v_aig_315_,
        v_target_316_,
    );
    leanh::lean_dec_ref(v_target_316_);
    return v_res_317_;
}
pub unsafe fn l_Std_Tactic_BVDecide_BVExpr_bitblast_blastExtractAndExtendBit(
    mut v_00_u03b1_318_: *mut leanh::LeanObject,
    mut v_inst_319_: *mut leanh::LeanObject,
    mut v_inst_320_: *mut leanh::LeanObject,
    mut v_w_321_: *mut leanh::LeanObject,
    mut v_aig_322_: *mut leanh::LeanObject,
    mut v_target_323_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_324_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_324_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastExtractAndExtendBit___redArg(
        v_w_321_,
        v_aig_322_,
        v_target_323_,
    );
    return v___x_324_;
}
pub unsafe fn l_Std_Tactic_BVDecide_BVExpr_bitblast_blastExtractAndExtendBit___boxed(
    mut v_00_u03b1_325_: *mut leanh::LeanObject,
    mut v_inst_326_: *mut leanh::LeanObject,
    mut v_inst_327_: *mut leanh::LeanObject,
    mut v_w_328_: *mut leanh::LeanObject,
    mut v_aig_329_: *mut leanh::LeanObject,
    mut v_target_330_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_331_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_331_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastExtractAndExtendBit(
        v_00_u03b1_325_,
        v_inst_326_,
        v_inst_327_,
        v_w_328_,
        v_aig_329_,
        v_target_330_,
    );
    leanh::lean_dec_ref(v_target_330_);
    leanh::lean_dec_ref(v_inst_327_);
    leanh::lean_dec_ref(v_inst_326_);
    return v_res_331_;
}
pub unsafe fn l_Std_Tactic_BVDecide_BVExpr_bitblast_blastExtractAndExtend_go___redArg(
    mut v_aig_332_: *mut leanh::LeanObject,
    mut v_w_333_: *mut leanh::LeanObject,
    mut v_idx_334_: *mut leanh::LeanObject,
    mut v_x_335_: *mut leanh::LeanObject,
    mut v_acc_336_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_337_: u8 = 0;
    let mut v___x_338_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_339_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_res_340_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_aig_341_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_vec_342_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_acc_343_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_344_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_345_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_337_ = lean_nat_dec_lt(v_idx_334_, v_w_333_);
                if v___x_337_ == 0 {
                    leanh::lean_dec_ref(v_x_335_);
                    leanh::lean_dec(v_idx_334_);
                    leanh::lean_dec(v_w_333_);
                    v___x_338_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_338_, 0, v_aig_332_);
                    leanh::lean_ctor_set(v___x_338_, 1, v_acc_336_);
                    return v___x_338_;
                } else {
                    leanh::lean_inc_ref(v_x_335_);
                    leanh::lean_inc(v_idx_334_);
                    v___x_339_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_339_, 0, v_idx_334_);
                    leanh::lean_ctor_set(v___x_339_, 1, v_x_335_);
                    leanh::lean_inc(v_w_333_);
                    v_res_340_ =
                        l_Std_Tactic_BVDecide_BVExpr_bitblast_blastExtractAndExtendBit___redArg(
                            v_w_333_, v_aig_332_, v___x_339_,
                        );
                    leanh::lean_dec_ref_known(v___x_339_, 2);
                    v_aig_341_ = leanh::lean_ctor_get(v_res_340_, 0);
                    leanh::lean_inc_ref(v_aig_341_);
                    v_vec_342_ = leanh::lean_ctor_get(v_res_340_, 1);
                    leanh::lean_inc_ref(v_vec_342_);
                    leanh::lean_dec_ref(v_res_340_);
                    v_acc_343_ = l_Array_append___redArg(v_acc_336_, v_vec_342_);
                    leanh::lean_dec_ref(v_vec_342_);
                    v___x_344_ = leanh::lean_unsigned_to_nat(1);
                    v___x_345_ = lean_nat_add(v_idx_334_, v___x_344_);
                    leanh::lean_dec(v_idx_334_);
                    v_aig_332_ = v_aig_341_;
                    v_idx_334_ = v___x_345_;
                    v_acc_336_ = v_acc_343_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Tactic_BVDecide_BVExpr_bitblast_blastExtractAndExtend_go(
    mut v_00_u03b1_347_: *mut leanh::LeanObject,
    mut v_inst_348_: *mut leanh::LeanObject,
    mut v_inst_349_: *mut leanh::LeanObject,
    mut v_outWidth_350_: *mut leanh::LeanObject,
    mut v_aig_351_: *mut leanh::LeanObject,
    mut v_w_352_: *mut leanh::LeanObject,
    mut v_idx_353_: *mut leanh::LeanObject,
    mut v_x_354_: *mut leanh::LeanObject,
    mut v_acc_355_: *mut leanh::LeanObject,
    mut v_h_356_: *mut leanh::LeanObject,
    mut v_h_x27_357_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_358_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_358_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastExtractAndExtend_go___redArg(
        v_aig_351_, v_w_352_, v_idx_353_, v_x_354_, v_acc_355_,
    );
    return v___x_358_;
}
pub unsafe fn l_Std_Tactic_BVDecide_BVExpr_bitblast_blastExtractAndExtend_go___boxed(
    mut v_00_u03b1_359_: *mut leanh::LeanObject,
    mut v_inst_360_: *mut leanh::LeanObject,
    mut v_inst_361_: *mut leanh::LeanObject,
    mut v_outWidth_362_: *mut leanh::LeanObject,
    mut v_aig_363_: *mut leanh::LeanObject,
    mut v_w_364_: *mut leanh::LeanObject,
    mut v_idx_365_: *mut leanh::LeanObject,
    mut v_x_366_: *mut leanh::LeanObject,
    mut v_acc_367_: *mut leanh::LeanObject,
    mut v_h_368_: *mut leanh::LeanObject,
    mut v_h_x27_369_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_370_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_370_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastExtractAndExtend_go(
        v_00_u03b1_359_,
        v_inst_360_,
        v_inst_361_,
        v_outWidth_362_,
        v_aig_363_,
        v_w_364_,
        v_idx_365_,
        v_x_366_,
        v_acc_367_,
        v_h_368_,
        v_h_x27_369_,
    );
    leanh::lean_dec(v_outWidth_362_);
    leanh::lean_dec_ref(v_inst_361_);
    leanh::lean_dec_ref(v_inst_360_);
    return v_res_370_;
}
pub unsafe fn _init_l_Std_Tactic_BVDecide_BVExpr_bitblast_blastExtractAndExtend___redArg___closed__0()
-> *mut leanh::LeanObject {
    let mut v___x_371_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_372_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_371_ = leanh::lean_unsigned_to_nat(0);
    v___x_372_ = l_BitVec_ofNat(v___x_371_, v___x_371_);
    return v___x_372_;
}
pub unsafe fn _init_l_Std_Tactic_BVDecide_BVExpr_bitblast_blastExtractAndExtend___redArg___closed__1()
-> *mut leanh::LeanObject {
    let mut v___x_373_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_374_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_initAcc_375_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_373_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Std_Tactic_BVDecide_BVExpr_bitblast_blastExtractAndExtend___redArg___closed__0
        ),
        core::ptr::addr_of_mut!(
            l_Std_Tactic_BVDecide_BVExpr_bitblast_blastExtractAndExtend___redArg___closed__0_once
        ),
        _init_l_Std_Tactic_BVDecide_BVExpr_bitblast_blastExtractAndExtend___redArg___closed__0,
    );
    v___x_374_ = leanh::lean_unsigned_to_nat(0);
    v_initAcc_375_ =
        l_Std_Tactic_BVDecide_BVExpr_bitblast_blastConst___redArg(v___x_374_, v___x_373_);
    return v_initAcc_375_;
}
pub unsafe fn l_Std_Tactic_BVDecide_BVExpr_bitblast_blastExtractAndExtend___redArg(
    mut v_aig_376_: *mut leanh::LeanObject,
    mut v_target_377_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_w_378_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_x_379_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_380_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_initAcc_381_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_382_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_w_378_ = leanh::lean_ctor_get(v_target_377_, 0);
    leanh::lean_inc(v_w_378_);
    v_x_379_ = leanh::lean_ctor_get(v_target_377_, 1);
    leanh::lean_inc_ref(v_x_379_);
    leanh::lean_dec_ref(v_target_377_);
    v___x_380_ = leanh::lean_unsigned_to_nat(0);
    v_initAcc_381_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Std_Tactic_BVDecide_BVExpr_bitblast_blastExtractAndExtend___redArg___closed__1
        ),
        core::ptr::addr_of_mut!(
            l_Std_Tactic_BVDecide_BVExpr_bitblast_blastExtractAndExtend___redArg___closed__1_once
        ),
        _init_l_Std_Tactic_BVDecide_BVExpr_bitblast_blastExtractAndExtend___redArg___closed__1,
    );
    v___x_382_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastExtractAndExtend_go___redArg(
        v_aig_376_,
        v_w_378_,
        v___x_380_,
        v_x_379_,
        v_initAcc_381_,
    );
    return v___x_382_;
}
pub unsafe fn l_Std_Tactic_BVDecide_BVExpr_bitblast_blastExtractAndExtend(
    mut v_00_u03b1_383_: *mut leanh::LeanObject,
    mut v_inst_384_: *mut leanh::LeanObject,
    mut v_inst_385_: *mut leanh::LeanObject,
    mut v_outWidth_386_: *mut leanh::LeanObject,
    mut v_aig_387_: *mut leanh::LeanObject,
    mut v_target_388_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_389_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_389_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastExtractAndExtend___redArg(
        v_aig_387_,
        v_target_388_,
    );
    return v___x_389_;
}
pub unsafe fn l_Std_Tactic_BVDecide_BVExpr_bitblast_blastExtractAndExtend___boxed(
    mut v_00_u03b1_390_: *mut leanh::LeanObject,
    mut v_inst_391_: *mut leanh::LeanObject,
    mut v_inst_392_: *mut leanh::LeanObject,
    mut v_outWidth_393_: *mut leanh::LeanObject,
    mut v_aig_394_: *mut leanh::LeanObject,
    mut v_target_395_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_396_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_396_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastExtractAndExtend(
        v_00_u03b1_390_,
        v_inst_391_,
        v_inst_392_,
        v_outWidth_393_,
        v_aig_394_,
        v_target_395_,
    );
    leanh::lean_dec(v_outWidth_393_);
    leanh::lean_dec_ref(v_inst_392_);
    leanh::lean_dec_ref(v_inst_391_);
    return v_res_396_;
}
pub unsafe fn l_Std_Tactic_BVDecide_BVExpr_bitblast_blastCpopLayer_go___redArg(
    mut v_inst_397_: *mut leanh::LeanObject,
    mut v_inst_398_: *mut leanh::LeanObject,
    mut v_aig_399_: *mut leanh::LeanObject,
    mut v_w_400_: *mut leanh::LeanObject,
    mut v_len_401_: *mut leanh::LeanObject,
    mut v_iterNum_402_: *mut leanh::LeanObject,
    mut v_oldLayer_403_: *mut leanh::LeanObject,
    mut v_newLayer_404_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_405_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_406_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_407_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_408_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_409_: u8 = 0;
    let mut v___x_410_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_411_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_412_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_413_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_414_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_res_415_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_aig_416_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_vec_417_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_418_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_419_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_420_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_421_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_res_422_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_aig_423_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_vec_424_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_426_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_427_: u8 = 0;
    let mut v___x_429_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_res_430_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_aig_431_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_vec_432_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_433_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_434_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_res_435_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_aig_436_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_vec_437_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_438_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_440_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_441_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_405_ = leanh::lean_unsigned_to_nat(0);
                v___x_406_ = leanh::lean_unsigned_to_nat(2);
                v___x_407_ = lean_nat_mul(v_iterNum_402_, v___x_406_);
                v___x_408_ = lean_nat_sub(v_len_401_, v___x_407_);
                leanh::lean_dec(v___x_407_);
                v___x_409_ = lean_nat_dec_lt(v___x_405_, v___x_408_);
                leanh::lean_dec(v___x_408_);
                if v___x_409_ == 0 {
                    leanh::lean_dec_ref(v_oldLayer_403_);
                    leanh::lean_dec(v_iterNum_402_);
                    leanh::lean_dec(v_w_400_);
                    leanh::lean_dec_ref(v_inst_398_);
                    leanh::lean_dec_ref(v_inst_397_);
                    v___x_410_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_410_, 0, v_aig_399_);
                    leanh::lean_ctor_set(v___x_410_, 1, v_newLayer_404_);
                    return v___x_410_;
                } else {
                    v___x_411_ = lean_nat_mul(v_len_401_, v_w_400_);
                    v___x_412_ = lean_nat_mul(v___x_406_, v_iterNum_402_);
                    v___x_413_ = lean_nat_mul(v___x_412_, v_w_400_);
                    leanh::lean_inc_ref_n(v_oldLayer_403_, 2);
                    leanh::lean_inc(v___x_411_);
                    v___x_414_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
                    leanh::lean_ctor_set(v___x_414_, 0, v___x_411_);
                    leanh::lean_ctor_set(v___x_414_, 1, v_oldLayer_403_);
                    leanh::lean_ctor_set(v___x_414_, 2, v___x_413_);
                    v_res_415_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastExtract___redArg(
                        v_w_400_, v_aig_399_, v___x_414_,
                    );
                    leanh::lean_dec_ref_known(v___x_414_, 3);
                    v_aig_416_ = leanh::lean_ctor_get(v_res_415_, 0);
                    leanh::lean_inc_ref(v_aig_416_);
                    v_vec_417_ = leanh::lean_ctor_get(v_res_415_, 1);
                    leanh::lean_inc_ref(v_vec_417_);
                    leanh::lean_dec_ref(v_res_415_);
                    v___x_418_ = leanh::lean_unsigned_to_nat(1);
                    v___x_419_ = lean_nat_add(v___x_412_, v___x_418_);
                    leanh::lean_dec(v___x_412_);
                    v___x_420_ = lean_nat_mul(v___x_419_, v_w_400_);
                    leanh::lean_dec(v___x_419_);
                    v___x_421_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
                    leanh::lean_ctor_set(v___x_421_, 0, v___x_411_);
                    leanh::lean_ctor_set(v___x_421_, 1, v_oldLayer_403_);
                    leanh::lean_ctor_set(v___x_421_, 2, v___x_420_);
                    v_res_422_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastExtract___redArg(
                        v_w_400_, v_aig_416_, v___x_421_,
                    );
                    leanh::lean_dec_ref_known(v___x_421_, 3);
                    v_aig_423_ = leanh::lean_ctor_get(v_res_422_, 0);
                    v_vec_424_ = leanh::lean_ctor_get(v_res_422_, 1);
                    v_isSharedCheck_441_ = (!leanh::lean_is_exclusive(v_res_422_)) as u8;
                    if v_isSharedCheck_441_ == 0 {
                        v___x_426_ = v_res_422_;
                        v_isShared_427_ = v_isSharedCheck_441_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_vec_424_);
                        leanh::lean_inc(v_aig_423_);
                        leanh::lean_dec(v_res_422_);
                        v___x_426_ = leanh::lean_box(0);
                        v_isShared_427_ = v_isSharedCheck_441_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_427_ == 0 {
                    leanh::lean_ctor_set(v___x_426_, 0, v_vec_417_);
                    v___x_429_ = v___x_426_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_440_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_440_, 0, v_vec_417_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_440_, 1, v_vec_424_);
                    v___x_429_ = v_reuseFailAlloc_440_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                leanh::lean_inc_ref(v_inst_398_);
                leanh::lean_inc_ref(v_inst_397_);
                v_res_430_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastAdd___redArg(
                    v_inst_397_,
                    v_inst_398_,
                    v_w_400_,
                    v_aig_423_,
                    v___x_429_,
                );
                v_aig_431_ = leanh::lean_ctor_get(v_res_430_, 0);
                leanh::lean_inc_ref(v_aig_431_);
                v_vec_432_ = leanh::lean_ctor_get(v_res_430_, 1);
                leanh::lean_inc_ref(v_vec_432_);
                leanh::lean_dec_ref(v_res_430_);
                v___x_433_ = lean_nat_mul(v_iterNum_402_, v_w_400_);
                leanh::lean_inc(v_w_400_);
                v___x_434_ = leanh::lean_alloc_ctor(0, 4, (0) as u32);
                leanh::lean_ctor_set(v___x_434_, 0, v_w_400_);
                leanh::lean_ctor_set(v___x_434_, 1, v___x_433_);
                leanh::lean_ctor_set(v___x_434_, 2, v_vec_432_);
                leanh::lean_ctor_set(v___x_434_, 3, v_newLayer_404_);
                v_res_435_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastAppend___redArg(
                    v_aig_431_, v___x_434_,
                );
                v_aig_436_ = leanh::lean_ctor_get(v_res_435_, 0);
                leanh::lean_inc_ref(v_aig_436_);
                v_vec_437_ = leanh::lean_ctor_get(v_res_435_, 1);
                leanh::lean_inc_ref(v_vec_437_);
                leanh::lean_dec_ref(v_res_435_);
                v___x_438_ = lean_nat_add(v_iterNum_402_, v___x_418_);
                leanh::lean_dec(v_iterNum_402_);
                v_aig_399_ = v_aig_436_;
                v_iterNum_402_ = v___x_438_;
                v_newLayer_404_ = v_vec_437_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Tactic_BVDecide_BVExpr_bitblast_blastCpopLayer_go___redArg___boxed(
    mut v_inst_442_: *mut leanh::LeanObject,
    mut v_inst_443_: *mut leanh::LeanObject,
    mut v_aig_444_: *mut leanh::LeanObject,
    mut v_w_445_: *mut leanh::LeanObject,
    mut v_len_446_: *mut leanh::LeanObject,
    mut v_iterNum_447_: *mut leanh::LeanObject,
    mut v_oldLayer_448_: *mut leanh::LeanObject,
    mut v_newLayer_449_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_450_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_450_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastCpopLayer_go___redArg(
        v_inst_442_,
        v_inst_443_,
        v_aig_444_,
        v_w_445_,
        v_len_446_,
        v_iterNum_447_,
        v_oldLayer_448_,
        v_newLayer_449_,
    );
    leanh::lean_dec(v_len_446_);
    return v_res_450_;
}
pub unsafe fn l_Std_Tactic_BVDecide_BVExpr_bitblast_blastCpopLayer_go(
    mut v_00_u03b1_451_: *mut leanh::LeanObject,
    mut v_inst_452_: *mut leanh::LeanObject,
    mut v_inst_453_: *mut leanh::LeanObject,
    mut v_outWidth_454_: *mut leanh::LeanObject,
    mut v_aig_455_: *mut leanh::LeanObject,
    mut v_w_456_: *mut leanh::LeanObject,
    mut v_len_457_: *mut leanh::LeanObject,
    mut v_iterNum_458_: *mut leanh::LeanObject,
    mut v_oldLayer_459_: *mut leanh::LeanObject,
    mut v_newLayer_460_: *mut leanh::LeanObject,
    mut v_hold_461_: *mut leanh::LeanObject,
    mut v_hout_462_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_463_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_463_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastCpopLayer_go___redArg(
        v_inst_452_,
        v_inst_453_,
        v_aig_455_,
        v_w_456_,
        v_len_457_,
        v_iterNum_458_,
        v_oldLayer_459_,
        v_newLayer_460_,
    );
    return v___x_463_;
}
pub unsafe fn l_Std_Tactic_BVDecide_BVExpr_bitblast_blastCpopLayer_go___boxed(
    mut v_00_u03b1_464_: *mut leanh::LeanObject,
    mut v_inst_465_: *mut leanh::LeanObject,
    mut v_inst_466_: *mut leanh::LeanObject,
    mut v_outWidth_467_: *mut leanh::LeanObject,
    mut v_aig_468_: *mut leanh::LeanObject,
    mut v_w_469_: *mut leanh::LeanObject,
    mut v_len_470_: *mut leanh::LeanObject,
    mut v_iterNum_471_: *mut leanh::LeanObject,
    mut v_oldLayer_472_: *mut leanh::LeanObject,
    mut v_newLayer_473_: *mut leanh::LeanObject,
    mut v_hold_474_: *mut leanh::LeanObject,
    mut v_hout_475_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_476_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_476_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastCpopLayer_go(
        v_00_u03b1_464_,
        v_inst_465_,
        v_inst_466_,
        v_outWidth_467_,
        v_aig_468_,
        v_w_469_,
        v_len_470_,
        v_iterNum_471_,
        v_oldLayer_472_,
        v_newLayer_473_,
        v_hold_474_,
        v_hout_475_,
    );
    leanh::lean_dec(v_len_470_);
    leanh::lean_dec(v_outWidth_467_);
    return v_res_476_;
}
pub unsafe fn l_Std_Tactic_BVDecide_BVExpr_bitblast_blastCpopLayer___redArg(
    mut v_inst_477_: *mut leanh::LeanObject,
    mut v_inst_478_: *mut leanh::LeanObject,
    mut v_aig_479_: *mut leanh::LeanObject,
    mut v_target_480_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_w_481_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_len_482_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_oldLayer_483_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_484_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_initAcc_485_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_486_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_w_481_ = leanh::lean_ctor_get(v_target_480_, 0);
    leanh::lean_inc(v_w_481_);
    v_len_482_ = leanh::lean_ctor_get(v_target_480_, 1);
    leanh::lean_inc(v_len_482_);
    v_oldLayer_483_ = leanh::lean_ctor_get(v_target_480_, 2);
    leanh::lean_inc_ref(v_oldLayer_483_);
    leanh::lean_dec_ref(v_target_480_);
    v___x_484_ = leanh::lean_unsigned_to_nat(0);
    v_initAcc_485_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Std_Tactic_BVDecide_BVExpr_bitblast_blastExtractAndExtend___redArg___closed__1
        ),
        core::ptr::addr_of_mut!(
            l_Std_Tactic_BVDecide_BVExpr_bitblast_blastExtractAndExtend___redArg___closed__1_once
        ),
        _init_l_Std_Tactic_BVDecide_BVExpr_bitblast_blastExtractAndExtend___redArg___closed__1,
    );
    v___x_486_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastCpopLayer_go___redArg(
        v_inst_477_,
        v_inst_478_,
        v_aig_479_,
        v_w_481_,
        v_len_482_,
        v___x_484_,
        v_oldLayer_483_,
        v_initAcc_485_,
    );
    leanh::lean_dec(v_len_482_);
    return v___x_486_;
}
pub unsafe fn l_Std_Tactic_BVDecide_BVExpr_bitblast_blastCpopLayer(
    mut v_00_u03b1_487_: *mut leanh::LeanObject,
    mut v_inst_488_: *mut leanh::LeanObject,
    mut v_inst_489_: *mut leanh::LeanObject,
    mut v_outWidth_490_: *mut leanh::LeanObject,
    mut v_aig_491_: *mut leanh::LeanObject,
    mut v_target_492_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_493_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_493_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastCpopLayer___redArg(
        v_inst_488_,
        v_inst_489_,
        v_aig_491_,
        v_target_492_,
    );
    return v___x_493_;
}
pub unsafe fn l_Std_Tactic_BVDecide_BVExpr_bitblast_blastCpopLayer___boxed(
    mut v_00_u03b1_494_: *mut leanh::LeanObject,
    mut v_inst_495_: *mut leanh::LeanObject,
    mut v_inst_496_: *mut leanh::LeanObject,
    mut v_outWidth_497_: *mut leanh::LeanObject,
    mut v_aig_498_: *mut leanh::LeanObject,
    mut v_target_499_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_500_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_500_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastCpopLayer(
        v_00_u03b1_494_,
        v_inst_495_,
        v_inst_496_,
        v_outWidth_497_,
        v_aig_498_,
        v_target_499_,
    );
    leanh::lean_dec(v_outWidth_497_);
    return v_res_500_;
}
pub unsafe fn l_Std_Tactic_BVDecide_BVExpr_bitblast_blastCpopTree_go___redArg(
    mut v_inst_501_: *mut leanh::LeanObject,
    mut v_inst_502_: *mut leanh::LeanObject,
    mut v_w_503_: *mut leanh::LeanObject,
    mut v_aig_504_: *mut leanh::LeanObject,
    mut v_len_505_: *mut leanh::LeanObject,
    mut v_x_506_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_507_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_508_: u8 = 0;
    let mut v___x_509_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_510_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_511_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_res_512_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_aig_513_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_vec_514_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_515_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_507_ = leanh::lean_unsigned_to_nat(1);
                v___x_508_ = lean_nat_dec_lt(v___x_507_, v_len_505_);
                if v___x_508_ == 0 {
                    leanh::lean_dec(v_len_505_);
                    leanh::lean_dec(v_w_503_);
                    leanh::lean_dec_ref(v_inst_502_);
                    leanh::lean_dec_ref(v_inst_501_);
                    v___x_509_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_509_, 0, v_aig_504_);
                    leanh::lean_ctor_set(v___x_509_, 1, v_x_506_);
                    return v___x_509_;
                } else {
                    v___x_510_ = lean_nat_add(v_len_505_, v___x_507_);
                    leanh::lean_inc(v_w_503_);
                    v___x_511_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
                    leanh::lean_ctor_set(v___x_511_, 0, v_w_503_);
                    leanh::lean_ctor_set(v___x_511_, 1, v_len_505_);
                    leanh::lean_ctor_set(v___x_511_, 2, v_x_506_);
                    leanh::lean_inc_ref(v_inst_502_);
                    leanh::lean_inc_ref(v_inst_501_);
                    v_res_512_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastCpopLayer___redArg(
                        v_inst_501_,
                        v_inst_502_,
                        v_aig_504_,
                        v___x_511_,
                    );
                    v_aig_513_ = leanh::lean_ctor_get(v_res_512_, 0);
                    leanh::lean_inc_ref(v_aig_513_);
                    v_vec_514_ = leanh::lean_ctor_get(v_res_512_, 1);
                    leanh::lean_inc_ref(v_vec_514_);
                    leanh::lean_dec_ref(v_res_512_);
                    v___x_515_ = lean_nat_shiftr(v___x_510_, v___x_507_);
                    leanh::lean_dec(v___x_510_);
                    v_aig_504_ = v_aig_513_;
                    v_len_505_ = v___x_515_;
                    v_x_506_ = v_vec_514_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Tactic_BVDecide_BVExpr_bitblast_blastCpopTree_go(
    mut v_00_u03b1_517_: *mut leanh::LeanObject,
    mut v_inst_518_: *mut leanh::LeanObject,
    mut v_inst_519_: *mut leanh::LeanObject,
    mut v_w_520_: *mut leanh::LeanObject,
    mut v_aig_521_: *mut leanh::LeanObject,
    mut v_len_522_: *mut leanh::LeanObject,
    mut v_x_523_: *mut leanh::LeanObject,
    mut v_h_524_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_525_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_525_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastCpopTree_go___redArg(
        v_inst_518_,
        v_inst_519_,
        v_w_520_,
        v_aig_521_,
        v_len_522_,
        v_x_523_,
    );
    return v___x_525_;
}
pub unsafe fn l_Std_Tactic_BVDecide_BVExpr_bitblast_blastCpopTree___redArg(
    mut v_inst_526_: *mut leanh::LeanObject,
    mut v_inst_527_: *mut leanh::LeanObject,
    mut v_w_528_: *mut leanh::LeanObject,
    mut v_aig_529_: *mut leanh::LeanObject,
    mut v_target_530_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_len_531_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_x_532_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_533_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_len_531_ = leanh::lean_ctor_get(v_target_530_, 0);
    leanh::lean_inc(v_len_531_);
    v_x_532_ = leanh::lean_ctor_get(v_target_530_, 1);
    leanh::lean_inc_ref(v_x_532_);
    leanh::lean_dec_ref(v_target_530_);
    v___x_533_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastCpopTree_go___redArg(
        v_inst_526_,
        v_inst_527_,
        v_w_528_,
        v_aig_529_,
        v_len_531_,
        v_x_532_,
    );
    return v___x_533_;
}
pub unsafe fn l_Std_Tactic_BVDecide_BVExpr_bitblast_blastCpopTree(
    mut v_00_u03b1_534_: *mut leanh::LeanObject,
    mut v_inst_535_: *mut leanh::LeanObject,
    mut v_inst_536_: *mut leanh::LeanObject,
    mut v_w_537_: *mut leanh::LeanObject,
    mut v_aig_538_: *mut leanh::LeanObject,
    mut v_target_539_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_540_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_540_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastCpopTree___redArg(
        v_inst_535_,
        v_inst_536_,
        v_w_537_,
        v_aig_538_,
        v_target_539_,
    );
    return v___x_540_;
}
pub unsafe fn l_Std_Tactic_BVDecide_BVExpr_bitblast_blastCpop___redArg(
    mut v_inst_541_: *mut leanh::LeanObject,
    mut v_inst_542_: *mut leanh::LeanObject,
    mut v_w_543_: *mut leanh::LeanObject,
    mut v_aig_544_: *mut leanh::LeanObject,
    mut v_x_545_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_546_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_547_: u8 = 0;
    let mut v___x_548_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_549_: u8 = 0;
    let mut v___x_550_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_zero_551_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_552_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_553_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_554_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_res_555_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_aig_556_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_vec_557_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_559_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_560_: u8 = 0;
    let mut v___x_562_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_563_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_564_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_565_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_546_ = leanh::lean_unsigned_to_nat(1);
                v___x_547_ = lean_nat_dec_lt(v___x_546_, v_w_543_);
                if v___x_547_ == 0 {
                    leanh::lean_dec_ref(v_inst_542_);
                    leanh::lean_dec_ref(v_inst_541_);
                    v___x_548_ = leanh::lean_unsigned_to_nat(0);
                    v___x_549_ = lean_nat_dec_lt(v___x_548_, v_w_543_);
                    if v___x_549_ == 0 {
                        leanh::lean_dec_ref(v_x_545_);
                        v___x_550_ = l_BitVec_ofNat(v_w_543_, v___x_548_);
                        v_zero_551_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastConst___redArg(
                            v_w_543_, v___x_550_,
                        );
                        leanh::lean_dec(v___x_550_);
                        leanh::lean_dec(v_w_543_);
                        v___x_552_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        leanh::lean_ctor_set(v___x_552_, 0, v_aig_544_);
                        leanh::lean_ctor_set(v___x_552_, 1, v_zero_551_);
                        return v___x_552_;
                    } else {
                        leanh::lean_dec(v_w_543_);
                        v___x_553_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        leanh::lean_ctor_set(v___x_553_, 0, v_aig_544_);
                        leanh::lean_ctor_set(v___x_553_, 1, v_x_545_);
                        return v___x_553_;
                    }
                } else {
                    leanh::lean_inc(v_w_543_);
                    v___x_554_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_554_, 0, v_w_543_);
                    leanh::lean_ctor_set(v___x_554_, 1, v_x_545_);
                    v_res_555_ =
                        l_Std_Tactic_BVDecide_BVExpr_bitblast_blastExtractAndExtend___redArg(
                            v_aig_544_, v___x_554_,
                        );
                    v_aig_556_ = leanh::lean_ctor_get(v_res_555_, 0);
                    v_vec_557_ = leanh::lean_ctor_get(v_res_555_, 1);
                    v_isSharedCheck_565_ = (!leanh::lean_is_exclusive(v_res_555_)) as u8;
                    if v_isSharedCheck_565_ == 0 {
                        v___x_559_ = v_res_555_;
                        v_isShared_560_ = v_isSharedCheck_565_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_vec_557_);
                        leanh::lean_inc(v_aig_556_);
                        leanh::lean_dec(v_res_555_);
                        v___x_559_ = leanh::lean_box(0);
                        v_isShared_560_ = v_isSharedCheck_565_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                leanh::lean_inc(v_w_543_);
                if v_isShared_560_ == 0 {
                    leanh::lean_ctor_set(v___x_559_, 0, v_w_543_);
                    v___x_562_ = v___x_559_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_564_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_564_, 0, v_w_543_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_564_, 1, v_vec_557_);
                    v___x_562_ = v_reuseFailAlloc_564_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_563_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastCpopTree___redArg(
                    v_inst_541_,
                    v_inst_542_,
                    v_w_543_,
                    v_aig_556_,
                    v___x_562_,
                );
                return v___x_563_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Tactic_BVDecide_BVExpr_bitblast_blastCpop(
    mut v_00_u03b1_566_: *mut leanh::LeanObject,
    mut v_inst_567_: *mut leanh::LeanObject,
    mut v_inst_568_: *mut leanh::LeanObject,
    mut v_w_569_: *mut leanh::LeanObject,
    mut v_aig_570_: *mut leanh::LeanObject,
    mut v_x_571_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_572_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_572_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastCpop___redArg(
        v_inst_567_,
        v_inst_568_,
        v_w_569_,
        v_aig_570_,
        v_x_571_,
    );
    return v___x_572_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Operations_Cpop(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Const(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res =
        runtime_initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Operations_Sub(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Operations_Extract(
        builtin,
    );
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Operations_Append(
        builtin,
    );
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Operations_ZeroExtend(
        builtin,
    );
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Std_Sat_AIG_If(builtin);
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
pub unsafe fn meta_initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Operations_Cpop(
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
pub unsafe fn initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Operations_Cpop(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Const(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Operations_Sub(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Operations_Extract(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Operations_Append(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res =
        initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Operations_ZeroExtend(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Std_Sat_AIG_If(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_Omega(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Operations_Cpop(
        builtin,
    );
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = meta_initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Operations_Cpop(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Operations_Cpop(builtin);
}