// Lean compiler output
// Module: Std.Tactic.BVDecide.Bitblast.BVExpr.Circuit.Impl.Operations.Cpop
// Imports: Std.Tactic.BVDecide.Bitblast.BVExpr.Circuit.Impl.Const Std.Tactic.BVDecide.Bitblast.BVExpr.Circuit.Impl.Operations.Sub Std.Tactic.BVDecide.Bitblast.BVExpr.Circuit.Impl.Operations.Extract Std.Tactic.BVDecide.Bitblast.BVExpr.Circuit.Impl.Operations.Append Std.Tactic.BVDecide.Bitblast.BVExpr.Circuit.Impl.Operations.ZeroExtend Std.Sat.AIG.If Init.Omega
use crate::leanh::{LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject, LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject, LeanTaskObject, LeanThunkObject, lean_alloc_ctor, lean_box, lean_ctor_get, lean_ctor_set, lean_dec, lean_dec_ref, lean_dec_ref_known, lean_inc, lean_inc_ref, lean_inc_ref_n, lean_io_result_is_error, lean_io_result_mk_ok, lean_is_exclusive, lean_obj_once, lean_unsigned_to_nat};
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
use crate::lean_imports_rs::Init::Prelude::{lean_nat_add, lean_nat_dec_lt, lean_nat_mul, lean_nat_sub};
use crate::lean_imports_rs::Init::Data::Nat::Bitwise::Basic::lean_nat_shiftr;
static mut l_Std_Tactic_BVDecide_BVExpr_bitblast_blastExtractAndExtend___redArg___closed__0_once:
    LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_Tactic_BVDecide_BVExpr_bitblast_blastExtractAndExtend___redArg___closed__0:
    *mut LeanObject = core::ptr::null_mut();
static mut l_Std_Tactic_BVDecide_BVExpr_bitblast_blastExtractAndExtend___redArg___closed__1_once:
    LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_Tactic_BVDecide_BVExpr_bitblast_blastExtractAndExtend___redArg___closed__1:
    *mut LeanObject = core::ptr::null_mut();
pub unsafe fn l_Std_Tactic_BVDecide_BVExpr_bitblast_blastExtractAndExtendBit___redArg(
    mut v_w_287_: *mut LeanObject,
    mut v_aig_288_: *mut LeanObject,
    mut v_target_289_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_start_290_: *mut LeanObject = core::ptr::null_mut();
    let mut v_x_291_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_292_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_293_: *mut LeanObject = core::ptr::null_mut();
    let mut v_res_294_: *mut LeanObject = core::ptr::null_mut();
    let mut v_aig_295_: *mut LeanObject = core::ptr::null_mut();
    let mut v_vec_296_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_298_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_299_: u8 = 0;
    let mut v___x_301_: *mut LeanObject = core::ptr::null_mut();
    let mut v_res_302_: *mut LeanObject = core::ptr::null_mut();
    let mut v_aig_303_: *mut LeanObject = core::ptr::null_mut();
    let mut v_vec_304_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_306_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_307_: u8 = 0;
    let mut v___x_309_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_310_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_311_: u8 = 0;
    let mut v_reuseFailAlloc_312_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_313_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_start_290_ = lean_ctor_get(v_target_289_, 0);
                v_x_291_ = lean_ctor_get(v_target_289_, 1);
                v___x_292_ = lean_unsigned_to_nat(1);
                lean_inc(v_start_290_);
                lean_inc_ref(v_x_291_);
                lean_inc(v_w_287_);
                v___x_293_ = lean_alloc_ctor(0, 3, (0) as u32);
                lean_ctor_set(v___x_293_, 0, v_w_287_);
                lean_ctor_set(v___x_293_, 1, v_x_291_);
                lean_ctor_set(v___x_293_, 2, v_start_290_);
                v_res_294_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastExtract___redArg(
                    v___x_292_, v_aig_288_, v___x_293_,
                );
                lean_dec_ref_known(v___x_293_, 3);
                v_aig_295_ = lean_ctor_get(v_res_294_, 0);
                v_vec_296_ = lean_ctor_get(v_res_294_, 1);
                v_isSharedCheck_313_ = (!lean_is_exclusive(v_res_294_)) as u8;
                if v_isSharedCheck_313_ == 0 {
                    v___x_298_ = v_res_294_;
                    v_isShared_299_ = v_isSharedCheck_313_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_vec_296_);
                    lean_inc(v_aig_295_);
                    lean_dec(v_res_294_);
                    v___x_298_ = lean_box(0);
                    v_isShared_299_ = v_isSharedCheck_313_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                if v_isShared_299_ == 0 {
                    lean_ctor_set(v___x_298_, 0, v___x_292_);
                    v___x_301_ = v___x_298_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_312_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_312_, 0, v___x_292_);
                    lean_ctor_set(v_reuseFailAlloc_312_, 1, v_vec_296_);
                    v___x_301_ = v_reuseFailAlloc_312_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v_res_302_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastZeroExtend___redArg(
                    v_w_287_, v_aig_295_, v___x_301_,
                );
                lean_dec_ref(v___x_301_);
                lean_dec(v_w_287_);
                v_aig_303_ = lean_ctor_get(v_res_302_, 0);
                v_vec_304_ = lean_ctor_get(v_res_302_, 1);
                v_isSharedCheck_311_ = (!lean_is_exclusive(v_res_302_)) as u8;
                if v_isSharedCheck_311_ == 0 {
                    v___x_306_ = v_res_302_;
                    v_isShared_307_ = v_isSharedCheck_311_;
                    state = 3;
                    continue;
                } else {
                    lean_inc(v_vec_304_);
                    lean_inc(v_aig_303_);
                    lean_dec(v_res_302_);
                    v___x_306_ = lean_box(0);
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
                    v_reuseFailAlloc_310_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_310_, 0, v_aig_303_);
                    lean_ctor_set(v_reuseFailAlloc_310_, 1, v_vec_304_);
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
    mut v_w_314_: *mut LeanObject,
    mut v_aig_315_: *mut LeanObject,
    mut v_target_316_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_317_: *mut LeanObject = core::ptr::null_mut();
    v_res_317_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastExtractAndExtendBit___redArg(
        v_w_314_,
        v_aig_315_,
        v_target_316_,
    );
    lean_dec_ref(v_target_316_);
    return v_res_317_;
}
pub unsafe fn l_Std_Tactic_BVDecide_BVExpr_bitblast_blastExtractAndExtendBit(
    mut v_00_u03b1_318_: *mut LeanObject,
    mut v_inst_319_: *mut LeanObject,
    mut v_inst_320_: *mut LeanObject,
    mut v_w_321_: *mut LeanObject,
    mut v_aig_322_: *mut LeanObject,
    mut v_target_323_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_324_: *mut LeanObject = core::ptr::null_mut();
    v___x_324_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastExtractAndExtendBit___redArg(
        v_w_321_,
        v_aig_322_,
        v_target_323_,
    );
    return v___x_324_;
}
pub unsafe fn l_Std_Tactic_BVDecide_BVExpr_bitblast_blastExtractAndExtendBit___boxed(
    mut v_00_u03b1_325_: *mut LeanObject,
    mut v_inst_326_: *mut LeanObject,
    mut v_inst_327_: *mut LeanObject,
    mut v_w_328_: *mut LeanObject,
    mut v_aig_329_: *mut LeanObject,
    mut v_target_330_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_331_: *mut LeanObject = core::ptr::null_mut();
    v_res_331_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastExtractAndExtendBit(
        v_00_u03b1_325_,
        v_inst_326_,
        v_inst_327_,
        v_w_328_,
        v_aig_329_,
        v_target_330_,
    );
    lean_dec_ref(v_target_330_);
    lean_dec_ref(v_inst_327_);
    lean_dec_ref(v_inst_326_);
    return v_res_331_;
}
pub unsafe fn l_Std_Tactic_BVDecide_BVExpr_bitblast_blastExtractAndExtend_go___redArg(
    mut v_aig_332_: *mut LeanObject,
    mut v_w_333_: *mut LeanObject,
    mut v_idx_334_: *mut LeanObject,
    mut v_x_335_: *mut LeanObject,
    mut v_acc_336_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_337_: u8 = 0;
    let mut v___x_338_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_339_: *mut LeanObject = core::ptr::null_mut();
    let mut v_res_340_: *mut LeanObject = core::ptr::null_mut();
    let mut v_aig_341_: *mut LeanObject = core::ptr::null_mut();
    let mut v_vec_342_: *mut LeanObject = core::ptr::null_mut();
    let mut v_acc_343_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_344_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_345_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_337_ = lean_nat_dec_lt(v_idx_334_, v_w_333_);
                if v___x_337_ == 0 {
                    lean_dec_ref(v_x_335_);
                    lean_dec(v_idx_334_);
                    lean_dec(v_w_333_);
                    v___x_338_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v___x_338_, 0, v_aig_332_);
                    lean_ctor_set(v___x_338_, 1, v_acc_336_);
                    return v___x_338_;
                } else {
                    lean_inc_ref(v_x_335_);
                    lean_inc(v_idx_334_);
                    v___x_339_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v___x_339_, 0, v_idx_334_);
                    lean_ctor_set(v___x_339_, 1, v_x_335_);
                    lean_inc(v_w_333_);
                    v_res_340_ =
                        l_Std_Tactic_BVDecide_BVExpr_bitblast_blastExtractAndExtendBit___redArg(
                            v_w_333_, v_aig_332_, v___x_339_,
                        );
                    lean_dec_ref_known(v___x_339_, 2);
                    v_aig_341_ = lean_ctor_get(v_res_340_, 0);
                    lean_inc_ref(v_aig_341_);
                    v_vec_342_ = lean_ctor_get(v_res_340_, 1);
                    lean_inc_ref(v_vec_342_);
                    lean_dec_ref(v_res_340_);
                    v_acc_343_ = l_Array_append___redArg(v_acc_336_, v_vec_342_);
                    lean_dec_ref(v_vec_342_);
                    v___x_344_ = lean_unsigned_to_nat(1);
                    v___x_345_ = lean_nat_add(v_idx_334_, v___x_344_);
                    lean_dec(v_idx_334_);
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
    mut v_00_u03b1_347_: *mut LeanObject,
    mut v_inst_348_: *mut LeanObject,
    mut v_inst_349_: *mut LeanObject,
    mut v_outWidth_350_: *mut LeanObject,
    mut v_aig_351_: *mut LeanObject,
    mut v_w_352_: *mut LeanObject,
    mut v_idx_353_: *mut LeanObject,
    mut v_x_354_: *mut LeanObject,
    mut v_acc_355_: *mut LeanObject,
    mut v_h_356_: *mut LeanObject,
    mut v_h_x27_357_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_358_: *mut LeanObject = core::ptr::null_mut();
    v___x_358_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastExtractAndExtend_go___redArg(
        v_aig_351_, v_w_352_, v_idx_353_, v_x_354_, v_acc_355_,
    );
    return v___x_358_;
}
pub unsafe fn l_Std_Tactic_BVDecide_BVExpr_bitblast_blastExtractAndExtend_go___boxed(
    mut v_00_u03b1_359_: *mut LeanObject,
    mut v_inst_360_: *mut LeanObject,
    mut v_inst_361_: *mut LeanObject,
    mut v_outWidth_362_: *mut LeanObject,
    mut v_aig_363_: *mut LeanObject,
    mut v_w_364_: *mut LeanObject,
    mut v_idx_365_: *mut LeanObject,
    mut v_x_366_: *mut LeanObject,
    mut v_acc_367_: *mut LeanObject,
    mut v_h_368_: *mut LeanObject,
    mut v_h_x27_369_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_370_: *mut LeanObject = core::ptr::null_mut();
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
    lean_dec(v_outWidth_362_);
    lean_dec_ref(v_inst_361_);
    lean_dec_ref(v_inst_360_);
    return v_res_370_;
}
pub unsafe fn _init_l_Std_Tactic_BVDecide_BVExpr_bitblast_blastExtractAndExtend___redArg___closed__0()
-> *mut LeanObject {
    let mut v___x_371_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_372_: *mut LeanObject = core::ptr::null_mut();
    v___x_371_ = lean_unsigned_to_nat(0);
    v___x_372_ = l_BitVec_ofNat(v___x_371_, v___x_371_);
    return v___x_372_;
}
pub unsafe fn _init_l_Std_Tactic_BVDecide_BVExpr_bitblast_blastExtractAndExtend___redArg___closed__1()
-> *mut LeanObject {
    let mut v___x_373_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_374_: *mut LeanObject = core::ptr::null_mut();
    let mut v_initAcc_375_: *mut LeanObject = core::ptr::null_mut();
    v___x_373_ = lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Std_Tactic_BVDecide_BVExpr_bitblast_blastExtractAndExtend___redArg___closed__0
        ),
        core::ptr::addr_of_mut!(
            l_Std_Tactic_BVDecide_BVExpr_bitblast_blastExtractAndExtend___redArg___closed__0_once
        ),
        _init_l_Std_Tactic_BVDecide_BVExpr_bitblast_blastExtractAndExtend___redArg___closed__0,
    );
    v___x_374_ = lean_unsigned_to_nat(0);
    v_initAcc_375_ =
        l_Std_Tactic_BVDecide_BVExpr_bitblast_blastConst___redArg(v___x_374_, v___x_373_);
    return v_initAcc_375_;
}
pub unsafe fn l_Std_Tactic_BVDecide_BVExpr_bitblast_blastExtractAndExtend___redArg(
    mut v_aig_376_: *mut LeanObject,
    mut v_target_377_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_w_378_: *mut LeanObject = core::ptr::null_mut();
    let mut v_x_379_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_380_: *mut LeanObject = core::ptr::null_mut();
    let mut v_initAcc_381_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_382_: *mut LeanObject = core::ptr::null_mut();
    v_w_378_ = lean_ctor_get(v_target_377_, 0);
    lean_inc(v_w_378_);
    v_x_379_ = lean_ctor_get(v_target_377_, 1);
    lean_inc_ref(v_x_379_);
    lean_dec_ref(v_target_377_);
    v___x_380_ = lean_unsigned_to_nat(0);
    v_initAcc_381_ = lean_obj_once(
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
    mut v_00_u03b1_383_: *mut LeanObject,
    mut v_inst_384_: *mut LeanObject,
    mut v_inst_385_: *mut LeanObject,
    mut v_outWidth_386_: *mut LeanObject,
    mut v_aig_387_: *mut LeanObject,
    mut v_target_388_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_389_: *mut LeanObject = core::ptr::null_mut();
    v___x_389_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastExtractAndExtend___redArg(
        v_aig_387_,
        v_target_388_,
    );
    return v___x_389_;
}
pub unsafe fn l_Std_Tactic_BVDecide_BVExpr_bitblast_blastExtractAndExtend___boxed(
    mut v_00_u03b1_390_: *mut LeanObject,
    mut v_inst_391_: *mut LeanObject,
    mut v_inst_392_: *mut LeanObject,
    mut v_outWidth_393_: *mut LeanObject,
    mut v_aig_394_: *mut LeanObject,
    mut v_target_395_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_396_: *mut LeanObject = core::ptr::null_mut();
    v_res_396_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastExtractAndExtend(
        v_00_u03b1_390_,
        v_inst_391_,
        v_inst_392_,
        v_outWidth_393_,
        v_aig_394_,
        v_target_395_,
    );
    lean_dec(v_outWidth_393_);
    lean_dec_ref(v_inst_392_);
    lean_dec_ref(v_inst_391_);
    return v_res_396_;
}
pub unsafe fn l_Std_Tactic_BVDecide_BVExpr_bitblast_blastCpopLayer_go___redArg(
    mut v_inst_397_: *mut LeanObject,
    mut v_inst_398_: *mut LeanObject,
    mut v_aig_399_: *mut LeanObject,
    mut v_w_400_: *mut LeanObject,
    mut v_len_401_: *mut LeanObject,
    mut v_iterNum_402_: *mut LeanObject,
    mut v_oldLayer_403_: *mut LeanObject,
    mut v_newLayer_404_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_405_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_406_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_407_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_408_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_409_: u8 = 0;
    let mut v___x_410_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_411_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_412_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_413_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_414_: *mut LeanObject = core::ptr::null_mut();
    let mut v_res_415_: *mut LeanObject = core::ptr::null_mut();
    let mut v_aig_416_: *mut LeanObject = core::ptr::null_mut();
    let mut v_vec_417_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_418_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_419_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_420_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_421_: *mut LeanObject = core::ptr::null_mut();
    let mut v_res_422_: *mut LeanObject = core::ptr::null_mut();
    let mut v_aig_423_: *mut LeanObject = core::ptr::null_mut();
    let mut v_vec_424_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_426_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_427_: u8 = 0;
    let mut v___x_429_: *mut LeanObject = core::ptr::null_mut();
    let mut v_res_430_: *mut LeanObject = core::ptr::null_mut();
    let mut v_aig_431_: *mut LeanObject = core::ptr::null_mut();
    let mut v_vec_432_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_433_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_434_: *mut LeanObject = core::ptr::null_mut();
    let mut v_res_435_: *mut LeanObject = core::ptr::null_mut();
    let mut v_aig_436_: *mut LeanObject = core::ptr::null_mut();
    let mut v_vec_437_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_438_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_440_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_441_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_405_ = lean_unsigned_to_nat(0);
                v___x_406_ = lean_unsigned_to_nat(2);
                v___x_407_ = lean_nat_mul(v_iterNum_402_, v___x_406_);
                v___x_408_ = lean_nat_sub(v_len_401_, v___x_407_);
                lean_dec(v___x_407_);
                v___x_409_ = lean_nat_dec_lt(v___x_405_, v___x_408_);
                lean_dec(v___x_408_);
                if v___x_409_ == 0 {
                    lean_dec_ref(v_oldLayer_403_);
                    lean_dec(v_iterNum_402_);
                    lean_dec(v_w_400_);
                    lean_dec_ref(v_inst_398_);
                    lean_dec_ref(v_inst_397_);
                    v___x_410_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v___x_410_, 0, v_aig_399_);
                    lean_ctor_set(v___x_410_, 1, v_newLayer_404_);
                    return v___x_410_;
                } else {
                    v___x_411_ = lean_nat_mul(v_len_401_, v_w_400_);
                    v___x_412_ = lean_nat_mul(v___x_406_, v_iterNum_402_);
                    v___x_413_ = lean_nat_mul(v___x_412_, v_w_400_);
                    lean_inc_ref_n(v_oldLayer_403_, 2);
                    lean_inc(v___x_411_);
                    v___x_414_ = lean_alloc_ctor(0, 3, (0) as u32);
                    lean_ctor_set(v___x_414_, 0, v___x_411_);
                    lean_ctor_set(v___x_414_, 1, v_oldLayer_403_);
                    lean_ctor_set(v___x_414_, 2, v___x_413_);
                    v_res_415_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastExtract___redArg(
                        v_w_400_, v_aig_399_, v___x_414_,
                    );
                    lean_dec_ref_known(v___x_414_, 3);
                    v_aig_416_ = lean_ctor_get(v_res_415_, 0);
                    lean_inc_ref(v_aig_416_);
                    v_vec_417_ = lean_ctor_get(v_res_415_, 1);
                    lean_inc_ref(v_vec_417_);
                    lean_dec_ref(v_res_415_);
                    v___x_418_ = lean_unsigned_to_nat(1);
                    v___x_419_ = lean_nat_add(v___x_412_, v___x_418_);
                    lean_dec(v___x_412_);
                    v___x_420_ = lean_nat_mul(v___x_419_, v_w_400_);
                    lean_dec(v___x_419_);
                    v___x_421_ = lean_alloc_ctor(0, 3, (0) as u32);
                    lean_ctor_set(v___x_421_, 0, v___x_411_);
                    lean_ctor_set(v___x_421_, 1, v_oldLayer_403_);
                    lean_ctor_set(v___x_421_, 2, v___x_420_);
                    v_res_422_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastExtract___redArg(
                        v_w_400_, v_aig_416_, v___x_421_,
                    );
                    lean_dec_ref_known(v___x_421_, 3);
                    v_aig_423_ = lean_ctor_get(v_res_422_, 0);
                    v_vec_424_ = lean_ctor_get(v_res_422_, 1);
                    v_isSharedCheck_441_ = (!lean_is_exclusive(v_res_422_)) as u8;
                    if v_isSharedCheck_441_ == 0 {
                        v___x_426_ = v_res_422_;
                        v_isShared_427_ = v_isSharedCheck_441_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_vec_424_);
                        lean_inc(v_aig_423_);
                        lean_dec(v_res_422_);
                        v___x_426_ = lean_box(0);
                        v_isShared_427_ = v_isSharedCheck_441_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_427_ == 0 {
                    lean_ctor_set(v___x_426_, 0, v_vec_417_);
                    v___x_429_ = v___x_426_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_440_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_440_, 0, v_vec_417_);
                    lean_ctor_set(v_reuseFailAlloc_440_, 1, v_vec_424_);
                    v___x_429_ = v_reuseFailAlloc_440_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                lean_inc_ref(v_inst_398_);
                lean_inc_ref(v_inst_397_);
                v_res_430_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastAdd___redArg(
                    v_inst_397_,
                    v_inst_398_,
                    v_w_400_,
                    v_aig_423_,
                    v___x_429_,
                );
                v_aig_431_ = lean_ctor_get(v_res_430_, 0);
                lean_inc_ref(v_aig_431_);
                v_vec_432_ = lean_ctor_get(v_res_430_, 1);
                lean_inc_ref(v_vec_432_);
                lean_dec_ref(v_res_430_);
                v___x_433_ = lean_nat_mul(v_iterNum_402_, v_w_400_);
                lean_inc(v_w_400_);
                v___x_434_ = lean_alloc_ctor(0, 4, (0) as u32);
                lean_ctor_set(v___x_434_, 0, v_w_400_);
                lean_ctor_set(v___x_434_, 1, v___x_433_);
                lean_ctor_set(v___x_434_, 2, v_vec_432_);
                lean_ctor_set(v___x_434_, 3, v_newLayer_404_);
                v_res_435_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastAppend___redArg(
                    v_aig_431_, v___x_434_,
                );
                v_aig_436_ = lean_ctor_get(v_res_435_, 0);
                lean_inc_ref(v_aig_436_);
                v_vec_437_ = lean_ctor_get(v_res_435_, 1);
                lean_inc_ref(v_vec_437_);
                lean_dec_ref(v_res_435_);
                v___x_438_ = lean_nat_add(v_iterNum_402_, v___x_418_);
                lean_dec(v_iterNum_402_);
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
    mut v_inst_442_: *mut LeanObject,
    mut v_inst_443_: *mut LeanObject,
    mut v_aig_444_: *mut LeanObject,
    mut v_w_445_: *mut LeanObject,
    mut v_len_446_: *mut LeanObject,
    mut v_iterNum_447_: *mut LeanObject,
    mut v_oldLayer_448_: *mut LeanObject,
    mut v_newLayer_449_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_450_: *mut LeanObject = core::ptr::null_mut();
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
    lean_dec(v_len_446_);
    return v_res_450_;
}
pub unsafe fn l_Std_Tactic_BVDecide_BVExpr_bitblast_blastCpopLayer_go(
    mut v_00_u03b1_451_: *mut LeanObject,
    mut v_inst_452_: *mut LeanObject,
    mut v_inst_453_: *mut LeanObject,
    mut v_outWidth_454_: *mut LeanObject,
    mut v_aig_455_: *mut LeanObject,
    mut v_w_456_: *mut LeanObject,
    mut v_len_457_: *mut LeanObject,
    mut v_iterNum_458_: *mut LeanObject,
    mut v_oldLayer_459_: *mut LeanObject,
    mut v_newLayer_460_: *mut LeanObject,
    mut v_hold_461_: *mut LeanObject,
    mut v_hout_462_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_463_: *mut LeanObject = core::ptr::null_mut();
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
    mut v_00_u03b1_464_: *mut LeanObject,
    mut v_inst_465_: *mut LeanObject,
    mut v_inst_466_: *mut LeanObject,
    mut v_outWidth_467_: *mut LeanObject,
    mut v_aig_468_: *mut LeanObject,
    mut v_w_469_: *mut LeanObject,
    mut v_len_470_: *mut LeanObject,
    mut v_iterNum_471_: *mut LeanObject,
    mut v_oldLayer_472_: *mut LeanObject,
    mut v_newLayer_473_: *mut LeanObject,
    mut v_hold_474_: *mut LeanObject,
    mut v_hout_475_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_476_: *mut LeanObject = core::ptr::null_mut();
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
    lean_dec(v_len_470_);
    lean_dec(v_outWidth_467_);
    return v_res_476_;
}
pub unsafe fn l_Std_Tactic_BVDecide_BVExpr_bitblast_blastCpopLayer___redArg(
    mut v_inst_477_: *mut LeanObject,
    mut v_inst_478_: *mut LeanObject,
    mut v_aig_479_: *mut LeanObject,
    mut v_target_480_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_w_481_: *mut LeanObject = core::ptr::null_mut();
    let mut v_len_482_: *mut LeanObject = core::ptr::null_mut();
    let mut v_oldLayer_483_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_484_: *mut LeanObject = core::ptr::null_mut();
    let mut v_initAcc_485_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_486_: *mut LeanObject = core::ptr::null_mut();
    v_w_481_ = lean_ctor_get(v_target_480_, 0);
    lean_inc(v_w_481_);
    v_len_482_ = lean_ctor_get(v_target_480_, 1);
    lean_inc(v_len_482_);
    v_oldLayer_483_ = lean_ctor_get(v_target_480_, 2);
    lean_inc_ref(v_oldLayer_483_);
    lean_dec_ref(v_target_480_);
    v___x_484_ = lean_unsigned_to_nat(0);
    v_initAcc_485_ = lean_obj_once(
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
    lean_dec(v_len_482_);
    return v___x_486_;
}
pub unsafe fn l_Std_Tactic_BVDecide_BVExpr_bitblast_blastCpopLayer(
    mut v_00_u03b1_487_: *mut LeanObject,
    mut v_inst_488_: *mut LeanObject,
    mut v_inst_489_: *mut LeanObject,
    mut v_outWidth_490_: *mut LeanObject,
    mut v_aig_491_: *mut LeanObject,
    mut v_target_492_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_493_: *mut LeanObject = core::ptr::null_mut();
    v___x_493_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastCpopLayer___redArg(
        v_inst_488_,
        v_inst_489_,
        v_aig_491_,
        v_target_492_,
    );
    return v___x_493_;
}
pub unsafe fn l_Std_Tactic_BVDecide_BVExpr_bitblast_blastCpopLayer___boxed(
    mut v_00_u03b1_494_: *mut LeanObject,
    mut v_inst_495_: *mut LeanObject,
    mut v_inst_496_: *mut LeanObject,
    mut v_outWidth_497_: *mut LeanObject,
    mut v_aig_498_: *mut LeanObject,
    mut v_target_499_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_500_: *mut LeanObject = core::ptr::null_mut();
    v_res_500_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastCpopLayer(
        v_00_u03b1_494_,
        v_inst_495_,
        v_inst_496_,
        v_outWidth_497_,
        v_aig_498_,
        v_target_499_,
    );
    lean_dec(v_outWidth_497_);
    return v_res_500_;
}
pub unsafe fn l_Std_Tactic_BVDecide_BVExpr_bitblast_blastCpopTree_go___redArg(
    mut v_inst_501_: *mut LeanObject,
    mut v_inst_502_: *mut LeanObject,
    mut v_w_503_: *mut LeanObject,
    mut v_aig_504_: *mut LeanObject,
    mut v_len_505_: *mut LeanObject,
    mut v_x_506_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_507_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_508_: u8 = 0;
    let mut v___x_509_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_510_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_511_: *mut LeanObject = core::ptr::null_mut();
    let mut v_res_512_: *mut LeanObject = core::ptr::null_mut();
    let mut v_aig_513_: *mut LeanObject = core::ptr::null_mut();
    let mut v_vec_514_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_515_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_507_ = lean_unsigned_to_nat(1);
                v___x_508_ = lean_nat_dec_lt(v___x_507_, v_len_505_);
                if v___x_508_ == 0 {
                    lean_dec(v_len_505_);
                    lean_dec(v_w_503_);
                    lean_dec_ref(v_inst_502_);
                    lean_dec_ref(v_inst_501_);
                    v___x_509_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v___x_509_, 0, v_aig_504_);
                    lean_ctor_set(v___x_509_, 1, v_x_506_);
                    return v___x_509_;
                } else {
                    v___x_510_ = lean_nat_add(v_len_505_, v___x_507_);
                    lean_inc(v_w_503_);
                    v___x_511_ = lean_alloc_ctor(0, 3, (0) as u32);
                    lean_ctor_set(v___x_511_, 0, v_w_503_);
                    lean_ctor_set(v___x_511_, 1, v_len_505_);
                    lean_ctor_set(v___x_511_, 2, v_x_506_);
                    lean_inc_ref(v_inst_502_);
                    lean_inc_ref(v_inst_501_);
                    v_res_512_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastCpopLayer___redArg(
                        v_inst_501_,
                        v_inst_502_,
                        v_aig_504_,
                        v___x_511_,
                    );
                    v_aig_513_ = lean_ctor_get(v_res_512_, 0);
                    lean_inc_ref(v_aig_513_);
                    v_vec_514_ = lean_ctor_get(v_res_512_, 1);
                    lean_inc_ref(v_vec_514_);
                    lean_dec_ref(v_res_512_);
                    v___x_515_ = lean_nat_shiftr(v___x_510_, v___x_507_);
                    lean_dec(v___x_510_);
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
    mut v_00_u03b1_517_: *mut LeanObject,
    mut v_inst_518_: *mut LeanObject,
    mut v_inst_519_: *mut LeanObject,
    mut v_w_520_: *mut LeanObject,
    mut v_aig_521_: *mut LeanObject,
    mut v_len_522_: *mut LeanObject,
    mut v_x_523_: *mut LeanObject,
    mut v_h_524_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_525_: *mut LeanObject = core::ptr::null_mut();
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
    mut v_inst_526_: *mut LeanObject,
    mut v_inst_527_: *mut LeanObject,
    mut v_w_528_: *mut LeanObject,
    mut v_aig_529_: *mut LeanObject,
    mut v_target_530_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_len_531_: *mut LeanObject = core::ptr::null_mut();
    let mut v_x_532_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_533_: *mut LeanObject = core::ptr::null_mut();
    v_len_531_ = lean_ctor_get(v_target_530_, 0);
    lean_inc(v_len_531_);
    v_x_532_ = lean_ctor_get(v_target_530_, 1);
    lean_inc_ref(v_x_532_);
    lean_dec_ref(v_target_530_);
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
    mut v_00_u03b1_534_: *mut LeanObject,
    mut v_inst_535_: *mut LeanObject,
    mut v_inst_536_: *mut LeanObject,
    mut v_w_537_: *mut LeanObject,
    mut v_aig_538_: *mut LeanObject,
    mut v_target_539_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_540_: *mut LeanObject = core::ptr::null_mut();
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
    mut v_inst_541_: *mut LeanObject,
    mut v_inst_542_: *mut LeanObject,
    mut v_w_543_: *mut LeanObject,
    mut v_aig_544_: *mut LeanObject,
    mut v_x_545_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_546_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_547_: u8 = 0;
    let mut v___x_548_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_549_: u8 = 0;
    let mut v___x_550_: *mut LeanObject = core::ptr::null_mut();
    let mut v_zero_551_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_552_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_553_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_554_: *mut LeanObject = core::ptr::null_mut();
    let mut v_res_555_: *mut LeanObject = core::ptr::null_mut();
    let mut v_aig_556_: *mut LeanObject = core::ptr::null_mut();
    let mut v_vec_557_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_559_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_560_: u8 = 0;
    let mut v___x_562_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_563_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_564_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_565_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_546_ = lean_unsigned_to_nat(1);
                v___x_547_ = lean_nat_dec_lt(v___x_546_, v_w_543_);
                if v___x_547_ == 0 {
                    lean_dec_ref(v_inst_542_);
                    lean_dec_ref(v_inst_541_);
                    v___x_548_ = lean_unsigned_to_nat(0);
                    v___x_549_ = lean_nat_dec_lt(v___x_548_, v_w_543_);
                    if v___x_549_ == 0 {
                        lean_dec_ref(v_x_545_);
                        v___x_550_ = l_BitVec_ofNat(v_w_543_, v___x_548_);
                        v_zero_551_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastConst___redArg(
                            v_w_543_, v___x_550_,
                        );
                        lean_dec(v___x_550_);
                        lean_dec(v_w_543_);
                        v___x_552_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v___x_552_, 0, v_aig_544_);
                        lean_ctor_set(v___x_552_, 1, v_zero_551_);
                        return v___x_552_;
                    } else {
                        lean_dec(v_w_543_);
                        v___x_553_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v___x_553_, 0, v_aig_544_);
                        lean_ctor_set(v___x_553_, 1, v_x_545_);
                        return v___x_553_;
                    }
                } else {
                    lean_inc(v_w_543_);
                    v___x_554_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v___x_554_, 0, v_w_543_);
                    lean_ctor_set(v___x_554_, 1, v_x_545_);
                    v_res_555_ =
                        l_Std_Tactic_BVDecide_BVExpr_bitblast_blastExtractAndExtend___redArg(
                            v_aig_544_, v___x_554_,
                        );
                    v_aig_556_ = lean_ctor_get(v_res_555_, 0);
                    v_vec_557_ = lean_ctor_get(v_res_555_, 1);
                    v_isSharedCheck_565_ = (!lean_is_exclusive(v_res_555_)) as u8;
                    if v_isSharedCheck_565_ == 0 {
                        v___x_559_ = v_res_555_;
                        v_isShared_560_ = v_isSharedCheck_565_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_vec_557_);
                        lean_inc(v_aig_556_);
                        lean_dec(v_res_555_);
                        v___x_559_ = lean_box(0);
                        v_isShared_560_ = v_isSharedCheck_565_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                lean_inc(v_w_543_);
                if v_isShared_560_ == 0 {
                    lean_ctor_set(v___x_559_, 0, v_w_543_);
                    v___x_562_ = v___x_559_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_564_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_564_, 0, v_w_543_);
                    lean_ctor_set(v_reuseFailAlloc_564_, 1, v_vec_557_);
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
    mut v_00_u03b1_566_: *mut LeanObject,
    mut v_inst_567_: *mut LeanObject,
    mut v_inst_568_: *mut LeanObject,
    mut v_w_569_: *mut LeanObject,
    mut v_aig_570_: *mut LeanObject,
    mut v_x_571_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_572_: *mut LeanObject = core::ptr::null_mut();
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
) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Const(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res =
        runtime_initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Operations_Sub(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Operations_Extract(
        builtin,
    );
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Operations_Append(
        builtin,
    );
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Operations_ZeroExtend(
        builtin,
    );
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Std_Sat_AIG_If(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Omega(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Operations_Cpop(
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
pub unsafe fn initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Operations_Cpop(
    builtin: u8,
) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Const(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Operations_Sub(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Operations_Extract(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Operations_Append(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res =
        initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Operations_ZeroExtend(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Std_Sat_AIG_If(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Omega(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Operations_Cpop(
        builtin,
    );
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Operations_Cpop(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Operations_Cpop(builtin);
}
