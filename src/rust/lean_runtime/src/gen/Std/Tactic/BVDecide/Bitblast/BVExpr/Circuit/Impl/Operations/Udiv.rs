// Lean compiler output
// Module: Std.Tactic.BVDecide.Bitblast.BVExpr.Circuit.Impl.Operations.Udiv
// Imports: Std.Tactic.BVDecide.Bitblast.BVExpr.Circuit.Impl.Operations.Sub Std.Tactic.BVDecide.Bitblast.BVExpr.Circuit.Impl.Operations.Eq Std.Tactic.BVDecide.Bitblast.BVExpr.Circuit.Impl.Operations.Ult Std.Tactic.BVDecide.Bitblast.BVExpr.Circuit.Impl.Operations.ZeroExtend Std.Sat.AIG.If Init.Omega
use crate::leanh::{LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject, LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject, LeanTaskObject, LeanThunkObject, lean_alloc_ctor, lean_apply_1, lean_box, lean_ctor_get, lean_ctor_get_uint8, lean_ctor_set, lean_ctor_set_uint8, lean_dec, lean_dec_ref, lean_inc, lean_inc_ref, lean_inc_ref_n, lean_io_result_is_error, lean_io_result_mk_ok, lean_is_exclusive, lean_unsigned_to_nat};
use crate::r#gen::Std::Tactic::BVDecide::Bitblast::BVExpr::Circuit::Impl::Operations::Sub::{initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Operations_Sub, l_Std_Tactic_BVDecide_BVExpr_bitblast_blastSub___redArg, runtime_initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Operations_Sub};
use crate::r#gen::Std::Tactic::BVDecide::Bitblast::BVExpr::Circuit::Impl::Operations::Eq::{initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Operations_Eq, l_Std_Tactic_BVDecide_BVPred_mkEq___redArg, runtime_initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Operations_Eq};
use crate::r#gen::Std::Tactic::BVDecide::Bitblast::BVExpr::Circuit::Impl::Operations::Ult::{initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Operations_Ult, l_Std_Tactic_BVDecide_BVPred_mkUlt___redArg, runtime_initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Operations_Ult};
use crate::r#gen::Std::Tactic::BVDecide::Bitblast::BVExpr::Circuit::Impl::Operations::ZeroExtend::{initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Operations_ZeroExtend, l_Std_Tactic_BVDecide_BVExpr_bitblast_blastZeroExtend___redArg, runtime_initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Operations_ZeroExtend};
use crate::r#gen::Std::Sat::AIG::If::{initialize_Std_Sat_AIG_If, l_Std_Sat_AIG_RefVec_ite___redArg, runtime_initialize_Std_Sat_AIG_If};
use crate::r#gen::Init::Omega::{initialize_Init_Omega, runtime_initialize_Init_Omega};
use crate::r#gen::Init::Prelude::l_BitVec_ofNat;
use crate::r#gen::Std::Tactic::BVDecide::Bitblast::BVExpr::Circuit::Impl::Const::l_Std_Tactic_BVDecide_BVExpr_bitblast_blastConst___redArg;
use crate::r#gen::Init::Data::Bool::l_Bool_toNat;
use crate::r#gen::Init::Data::Array::Basic::l_Array_append___redArg;
use crate::lean_imports_rs::Init::Prelude::{lean_array_fget_borrowed, lean_array_push, lean_mk_empty_array_with_capacity, lean_nat_add, lean_nat_dec_eq, lean_nat_dec_lt, lean_nat_mul, lean_nat_sub};
use crate::lean_imports_rs::Init::Data::Nat::Bitwise::Basic::{lean_nat_land, lean_nat_lor, lean_nat_shiftr};
pub static l_Std_Tactic_BVDecide_BVExpr_bitblast_blastUdiv_blastDivSubtractShift___redArg___closed__0_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*1 + 8) as u16, other: 1, tag: 0 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,0 as *mut LeanObject] };
static mut l_Std_Tactic_BVDecide_BVExpr_bitblast_blastUdiv_blastDivSubtractShift___redArg___closed__0: *mut LeanObject = core::ptr::addr_of!(l_Std_Tactic_BVDecide_BVExpr_bitblast_blastUdiv_blastDivSubtractShift___redArg___closed__0_value) as *mut LeanObject;
pub static l_Std_Tactic_BVDecide_BVExpr_bitblast_blastUdiv_blastDivSubtractShift___redArg___closed__1_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*1 + 8) as u16, other: 1, tag: 0 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,1 as *mut LeanObject] };
static mut l_Std_Tactic_BVDecide_BVExpr_bitblast_blastUdiv_blastDivSubtractShift___redArg___closed__1: *mut LeanObject = core::ptr::addr_of!(l_Std_Tactic_BVDecide_BVExpr_bitblast_blastUdiv_blastDivSubtractShift___redArg___closed__1_value) as *mut LeanObject;
pub unsafe fn l_Std_Tactic_BVDecide_BVExpr_bitblast_blastUdiv_blastShiftConcat___redArg(
    mut v_w_316_: *mut LeanObject,
    mut v_aig_317_: *mut LeanObject,
    mut v_input_318_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_bit_319_: *mut LeanObject = core::ptr::null_mut();
    let mut v_lhs_320_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_322_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_323_: u8 = 0;
    let mut v_gate_324_: *mut LeanObject = core::ptr::null_mut();
    let mut v_invert_325_: u8 = 0;
    let mut v___x_326_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_327_: *mut LeanObject = core::ptr::null_mut();
    let mut v_refs_328_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_329_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_330_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_331_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_332_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_333_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_334_: *mut LeanObject = core::ptr::null_mut();
    let mut v_new_335_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_337_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_338_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_339_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_340_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_bit_319_ = lean_ctor_get(v_input_318_, 1);
                v_lhs_320_ = lean_ctor_get(v_input_318_, 0);
                v_isSharedCheck_340_ = (!lean_is_exclusive(v_input_318_)) as u8;
                if v_isSharedCheck_340_ == 0 {
                    v___x_322_ = v_input_318_;
                    v_isShared_323_ = v_isSharedCheck_340_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_bit_319_);
                    lean_inc(v_lhs_320_);
                    lean_dec(v_input_318_);
                    v___x_322_ = lean_box(0);
                    v_isShared_323_ = v_isSharedCheck_340_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_gate_324_ = lean_ctor_get(v_bit_319_, 0);
                lean_inc(v_gate_324_);
                v_invert_325_ = lean_ctor_get_uint8(
                    v_bit_319_,
                    (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                );
                lean_dec_ref(v_bit_319_);
                v___x_326_ = lean_unsigned_to_nat(1);
                v___x_327_ = lean_nat_add(v_w_316_, v___x_326_);
                v_refs_328_ = lean_mk_empty_array_with_capacity(v___x_327_);
                lean_dec(v___x_327_);
                v___x_329_ = lean_unsigned_to_nat(2);
                v___x_330_ = lean_nat_mul(v_gate_324_, v___x_329_);
                lean_dec(v_gate_324_);
                v___x_331_ = l_Bool_toNat(v_invert_325_);
                v___x_332_ = lean_nat_lor(v___x_330_, v___x_331_);
                lean_dec(v___x_331_);
                lean_dec(v___x_330_);
                v___x_333_ = lean_array_push(v_refs_328_, v___x_332_);
                v___x_334_ = lean_nat_add(v___x_326_, v_w_316_);
                v_new_335_ = l_Array_append___redArg(v___x_333_, v_lhs_320_);
                lean_dec_ref(v_lhs_320_);
                if v_isShared_323_ == 0 {
                    lean_ctor_set(v___x_322_, 1, v_new_335_);
                    lean_ctor_set(v___x_322_, 0, v___x_334_);
                    v___x_337_ = v___x_322_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_339_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_339_, 0, v___x_334_);
                    lean_ctor_set(v_reuseFailAlloc_339_, 1, v_new_335_);
                    v___x_337_ = v_reuseFailAlloc_339_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_338_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastZeroExtend___redArg(
                    v_w_316_, v_aig_317_, v___x_337_,
                );
                lean_dec_ref(v___x_337_);
                return v___x_338_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Tactic_BVDecide_BVExpr_bitblast_blastUdiv_blastShiftConcat___redArg___boxed(
    mut v_w_341_: *mut LeanObject,
    mut v_aig_342_: *mut LeanObject,
    mut v_input_343_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_344_: *mut LeanObject = core::ptr::null_mut();
    v_res_344_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastUdiv_blastShiftConcat___redArg(
        v_w_341_,
        v_aig_342_,
        v_input_343_,
    );
    lean_dec(v_w_341_);
    return v_res_344_;
}
pub unsafe fn l_Std_Tactic_BVDecide_BVExpr_bitblast_blastUdiv_blastShiftConcat(
    mut v_00_u03b1_345_: *mut LeanObject,
    mut v_inst_346_: *mut LeanObject,
    mut v_inst_347_: *mut LeanObject,
    mut v_w_348_: *mut LeanObject,
    mut v_aig_349_: *mut LeanObject,
    mut v_input_350_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_351_: *mut LeanObject = core::ptr::null_mut();
    v___x_351_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastUdiv_blastShiftConcat___redArg(
        v_w_348_,
        v_aig_349_,
        v_input_350_,
    );
    return v___x_351_;
}
pub unsafe fn l_Std_Tactic_BVDecide_BVExpr_bitblast_blastUdiv_blastShiftConcat___boxed(
    mut v_00_u03b1_352_: *mut LeanObject,
    mut v_inst_353_: *mut LeanObject,
    mut v_inst_354_: *mut LeanObject,
    mut v_w_355_: *mut LeanObject,
    mut v_aig_356_: *mut LeanObject,
    mut v_input_357_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_358_: *mut LeanObject = core::ptr::null_mut();
    v_res_358_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastUdiv_blastShiftConcat(
        v_00_u03b1_352_,
        v_inst_353_,
        v_inst_354_,
        v_w_355_,
        v_aig_356_,
        v_input_357_,
    );
    lean_dec(v_w_355_);
    lean_dec_ref(v_inst_354_);
    lean_dec_ref(v_inst_353_);
    return v_res_358_;
}
pub unsafe fn l_Std_Tactic_BVDecide_BVExpr_bitblast_blastUdiv_blastDivSubtractShift___redArg(
    mut v_inst_365_: *mut LeanObject,
    mut v_inst_366_: *mut LeanObject,
    mut v_w_367_: *mut LeanObject,
    mut v_aig_368_: *mut LeanObject,
    mut v_n_369_: *mut LeanObject,
    mut v_d_370_: *mut LeanObject,
    mut v_wn_371_: *mut LeanObject,
    mut v_wr_372_: *mut LeanObject,
    mut v_q_373_: *mut LeanObject,
    mut v_r_374_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_375_: *mut LeanObject = core::ptr::null_mut();
    let mut v_wn_376_: *mut LeanObject = core::ptr::null_mut();
    let mut v_wr_377_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_378_: u8 = 0;
    let mut v___y_380_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_381_: *mut LeanObject = core::ptr::null_mut();
    let mut v_res_382_: *mut LeanObject = core::ptr::null_mut();
    let mut v_aig_383_: *mut LeanObject = core::ptr::null_mut();
    let mut v_vec_384_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_386_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_387_: u8 = 0;
    let mut v_falseRef_388_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_390_: *mut LeanObject = core::ptr::null_mut();
    let mut v_res_391_: *mut LeanObject = core::ptr::null_mut();
    let mut v_aig_392_: *mut LeanObject = core::ptr::null_mut();
    let mut v_vec_393_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_395_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_396_: u8 = 0;
    let mut v_trueRef_397_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_399_: *mut LeanObject = core::ptr::null_mut();
    let mut v_res_400_: *mut LeanObject = core::ptr::null_mut();
    let mut v_aig_401_: *mut LeanObject = core::ptr::null_mut();
    let mut v_vec_402_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_404_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_405_: u8 = 0;
    let mut v___x_407_: *mut LeanObject = core::ptr::null_mut();
    let mut v_res_408_: *mut LeanObject = core::ptr::null_mut();
    let mut v_aig_409_: *mut LeanObject = core::ptr::null_mut();
    let mut v_vec_410_: *mut LeanObject = core::ptr::null_mut();
    let mut v_res_411_: *mut LeanObject = core::ptr::null_mut();
    let mut v_aig_412_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ref_413_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_414_: *mut LeanObject = core::ptr::null_mut();
    let mut v_res_415_: *mut LeanObject = core::ptr::null_mut();
    let mut v_aig_416_: *mut LeanObject = core::ptr::null_mut();
    let mut v_vec_417_: *mut LeanObject = core::ptr::null_mut();
    let mut v_gate_418_: *mut LeanObject = core::ptr::null_mut();
    let mut v_invert_419_: u8 = 0;
    let mut v___x_421_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_422_: u8 = 0;
    let mut v_discr_424_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_425_: *mut LeanObject = core::ptr::null_mut();
    let mut v_res_426_: *mut LeanObject = core::ptr::null_mut();
    let mut v_aig_427_: *mut LeanObject = core::ptr::null_mut();
    let mut v_vec_428_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_429_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_430_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_431_: u8 = 0;
    let mut v_reuseFailAlloc_432_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_433_: u8 = 0;
    let mut v_reuseFailAlloc_434_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_435_: u8 = 0;
    let mut v_reuseFailAlloc_436_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_437_: u8 = 0;
    let mut v___x_438_: u8 = 0;
    let mut v_falseRef_439_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ref_440_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_441_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_442_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_443_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_444_: u8 = 0;
    let mut v___x_445_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_446_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_375_ = lean_unsigned_to_nat(1);
                v_wn_376_ = lean_nat_sub(v_wn_371_, v___x_375_);
                v_wr_377_ = lean_nat_add(v_wr_372_, v___x_375_);
                v___x_378_ = 0;
                v___x_438_ = lean_nat_dec_lt(v_wn_376_, v_w_367_);
                if v___x_438_ == 0 {
                    v_falseRef_439_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastUdiv_blastDivSubtractShift___redArg___closed__0;
                    v___y_380_ = v_falseRef_439_;
                    state = 1;
                    continue;
                } else {
                    v_ref_440_ = lean_array_fget_borrowed(v_n_369_, v_wn_376_);
                    v___x_441_ = lean_nat_shiftr(v_ref_440_, v___x_375_);
                    v___x_442_ = lean_nat_land(v___x_375_, v_ref_440_);
                    v___x_443_ = lean_unsigned_to_nat(0);
                    v___x_444_ = lean_nat_dec_eq(v___x_442_, v___x_443_);
                    lean_dec(v___x_442_);
                    if v___x_444_ == 0 {
                        v___x_445_ = lean_alloc_ctor(0, 1, (1) as u32);
                        lean_ctor_set(v___x_445_, 0, v___x_441_);
                        lean_ctor_set_uint8(
                            v___x_445_,
                            (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                            v___x_438_,
                        );
                        v___y_380_ = v___x_445_;
                        state = 1;
                        continue;
                    } else {
                        v___x_446_ = lean_alloc_ctor(0, 1, (1) as u32);
                        lean_ctor_set(v___x_446_, 0, v___x_441_);
                        lean_ctor_set_uint8(
                            v___x_446_,
                            (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                            v___x_378_,
                        );
                        v___y_380_ = v___x_446_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_381_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_381_, 0, v_r_374_);
                lean_ctor_set(v___x_381_, 1, v___y_380_);
                v_res_382_ =
                    l_Std_Tactic_BVDecide_BVExpr_bitblast_blastUdiv_blastShiftConcat___redArg(
                        v_w_367_, v_aig_368_, v___x_381_,
                    );
                v_aig_383_ = lean_ctor_get(v_res_382_, 0);
                v_vec_384_ = lean_ctor_get(v_res_382_, 1);
                v_isSharedCheck_437_ = (!lean_is_exclusive(v_res_382_)) as u8;
                if v_isSharedCheck_437_ == 0 {
                    v___x_386_ = v_res_382_;
                    v_isShared_387_ = v_isSharedCheck_437_;
                    state = 2;
                    continue;
                } else {
                    lean_inc(v_vec_384_);
                    lean_inc(v_aig_383_);
                    lean_dec(v_res_382_);
                    v___x_386_ = lean_box(0);
                    v_isShared_387_ = v_isSharedCheck_437_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v_falseRef_388_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastUdiv_blastDivSubtractShift___redArg___closed__0;
                lean_inc_ref(v_q_373_);
                if v_isShared_387_ == 0 {
                    lean_ctor_set(v___x_386_, 1, v_falseRef_388_);
                    lean_ctor_set(v___x_386_, 0, v_q_373_);
                    v___x_390_ = v___x_386_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_436_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_436_, 0, v_q_373_);
                    lean_ctor_set(v_reuseFailAlloc_436_, 1, v_falseRef_388_);
                    v___x_390_ = v_reuseFailAlloc_436_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v_res_391_ =
                    l_Std_Tactic_BVDecide_BVExpr_bitblast_blastUdiv_blastShiftConcat___redArg(
                        v_w_367_, v_aig_383_, v___x_390_,
                    );
                v_aig_392_ = lean_ctor_get(v_res_391_, 0);
                v_vec_393_ = lean_ctor_get(v_res_391_, 1);
                v_isSharedCheck_435_ = (!lean_is_exclusive(v_res_391_)) as u8;
                if v_isSharedCheck_435_ == 0 {
                    v___x_395_ = v_res_391_;
                    v_isShared_396_ = v_isSharedCheck_435_;
                    state = 4;
                    continue;
                } else {
                    lean_inc(v_vec_393_);
                    lean_inc(v_aig_392_);
                    lean_dec(v_res_391_);
                    v___x_395_ = lean_box(0);
                    v_isShared_396_ = v_isSharedCheck_435_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v_trueRef_397_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastUdiv_blastDivSubtractShift___redArg___closed__1;
                if v_isShared_396_ == 0 {
                    lean_ctor_set(v___x_395_, 1, v_trueRef_397_);
                    lean_ctor_set(v___x_395_, 0, v_q_373_);
                    v___x_399_ = v___x_395_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_434_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_434_, 0, v_q_373_);
                    lean_ctor_set(v_reuseFailAlloc_434_, 1, v_trueRef_397_);
                    v___x_399_ = v_reuseFailAlloc_434_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v_res_400_ =
                    l_Std_Tactic_BVDecide_BVExpr_bitblast_blastUdiv_blastShiftConcat___redArg(
                        v_w_367_, v_aig_392_, v___x_399_,
                    );
                v_aig_401_ = lean_ctor_get(v_res_400_, 0);
                v_vec_402_ = lean_ctor_get(v_res_400_, 1);
                v_isSharedCheck_433_ = (!lean_is_exclusive(v_res_400_)) as u8;
                if v_isSharedCheck_433_ == 0 {
                    v___x_404_ = v_res_400_;
                    v_isShared_405_ = v_isSharedCheck_433_;
                    state = 6;
                    continue;
                } else {
                    lean_inc(v_vec_402_);
                    lean_inc(v_aig_401_);
                    lean_dec(v_res_400_);
                    v___x_404_ = lean_box(0);
                    v_isShared_405_ = v_isSharedCheck_433_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                lean_inc_ref(v_vec_384_);
                if v_isShared_405_ == 0 {
                    lean_ctor_set(v___x_404_, 1, v_d_370_);
                    lean_ctor_set(v___x_404_, 0, v_vec_384_);
                    v___x_407_ = v___x_404_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_432_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_432_, 0, v_vec_384_);
                    lean_ctor_set(v_reuseFailAlloc_432_, 1, v_d_370_);
                    v___x_407_ = v_reuseFailAlloc_432_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                lean_inc_ref(v___x_407_);
                lean_inc_ref_n(v_inst_366_, 3);
                lean_inc_ref_n(v_inst_365_, 3);
                v_res_408_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastSub___redArg(
                    v_inst_365_,
                    v_inst_366_,
                    v_w_367_,
                    v_aig_401_,
                    v___x_407_,
                );
                v_aig_409_ = lean_ctor_get(v_res_408_, 0);
                lean_inc_ref(v_aig_409_);
                v_vec_410_ = lean_ctor_get(v_res_408_, 1);
                lean_inc_ref(v_vec_410_);
                lean_dec_ref(v_res_408_);
                lean_inc(v_w_367_);
                v_res_411_ = l_Std_Tactic_BVDecide_BVPred_mkUlt___redArg(
                    v_inst_365_,
                    v_inst_366_,
                    v_w_367_,
                    v_aig_409_,
                    v___x_407_,
                );
                v_aig_412_ = lean_ctor_get(v_res_411_, 0);
                lean_inc_ref(v_aig_412_);
                v_ref_413_ = lean_ctor_get(v_res_411_, 1);
                lean_inc_ref_n(v_ref_413_, 2);
                lean_dec_ref(v_res_411_);
                v___x_414_ = lean_alloc_ctor(0, 3, (0) as u32);
                lean_ctor_set(v___x_414_, 0, v_ref_413_);
                lean_ctor_set(v___x_414_, 1, v_vec_393_);
                lean_ctor_set(v___x_414_, 2, v_vec_402_);
                v_res_415_ = l_Std_Sat_AIG_RefVec_ite___redArg(
                    v_inst_365_,
                    v_inst_366_,
                    v_w_367_,
                    v_aig_412_,
                    v___x_414_,
                );
                v_aig_416_ = lean_ctor_get(v_res_415_, 0);
                lean_inc_ref(v_aig_416_);
                v_vec_417_ = lean_ctor_get(v_res_415_, 1);
                lean_inc_ref(v_vec_417_);
                lean_dec_ref(v_res_415_);
                v_gate_418_ = lean_ctor_get(v_ref_413_, 0);
                v_invert_419_ = lean_ctor_get_uint8(
                    v_ref_413_,
                    (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                );
                v_isSharedCheck_431_ = (!lean_is_exclusive(v_ref_413_)) as u8;
                if v_isSharedCheck_431_ == 0 {
                    v___x_421_ = v_ref_413_;
                    v_isShared_422_ = v_isSharedCheck_431_;
                    state = 8;
                    continue;
                } else {
                    lean_inc(v_gate_418_);
                    lean_dec(v_ref_413_);
                    v___x_421_ = lean_box(0);
                    v_isShared_422_ = v_isSharedCheck_431_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                if v_isShared_422_ == 0 {
                    v_discr_424_ = v___x_421_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_430_ = lean_alloc_ctor(0, 1, (1) as u32);
                    lean_ctor_set(v_reuseFailAlloc_430_, 0, v_gate_418_);
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_430_,
                        (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                        v_invert_419_,
                    );
                    v_discr_424_ = v_reuseFailAlloc_430_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                v___x_425_ = lean_alloc_ctor(0, 3, (0) as u32);
                lean_ctor_set(v___x_425_, 0, v_discr_424_);
                lean_ctor_set(v___x_425_, 1, v_vec_384_);
                lean_ctor_set(v___x_425_, 2, v_vec_410_);
                v_res_426_ = l_Std_Sat_AIG_RefVec_ite___redArg(
                    v_inst_365_,
                    v_inst_366_,
                    v_w_367_,
                    v_aig_416_,
                    v___x_425_,
                );
                lean_dec(v_w_367_);
                v_aig_427_ = lean_ctor_get(v_res_426_, 0);
                lean_inc_ref(v_aig_427_);
                v_vec_428_ = lean_ctor_get(v_res_426_, 1);
                lean_inc_ref(v_vec_428_);
                lean_dec_ref(v_res_426_);
                v___x_429_ = lean_alloc_ctor(0, 5, (0) as u32);
                lean_ctor_set(v___x_429_, 0, v_aig_427_);
                lean_ctor_set(v___x_429_, 1, v_wn_376_);
                lean_ctor_set(v___x_429_, 2, v_wr_377_);
                lean_ctor_set(v___x_429_, 3, v_vec_417_);
                lean_ctor_set(v___x_429_, 4, v_vec_428_);
                return v___x_429_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Tactic_BVDecide_BVExpr_bitblast_blastUdiv_blastDivSubtractShift___redArg___boxed(
    mut v_inst_447_: *mut LeanObject,
    mut v_inst_448_: *mut LeanObject,
    mut v_w_449_: *mut LeanObject,
    mut v_aig_450_: *mut LeanObject,
    mut v_n_451_: *mut LeanObject,
    mut v_d_452_: *mut LeanObject,
    mut v_wn_453_: *mut LeanObject,
    mut v_wr_454_: *mut LeanObject,
    mut v_q_455_: *mut LeanObject,
    mut v_r_456_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_457_: *mut LeanObject = core::ptr::null_mut();
    v_res_457_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastUdiv_blastDivSubtractShift___redArg(
        v_inst_447_,
        v_inst_448_,
        v_w_449_,
        v_aig_450_,
        v_n_451_,
        v_d_452_,
        v_wn_453_,
        v_wr_454_,
        v_q_455_,
        v_r_456_,
    );
    lean_dec(v_wr_454_);
    lean_dec(v_wn_453_);
    lean_dec_ref(v_n_451_);
    return v_res_457_;
}
pub unsafe fn l_Std_Tactic_BVDecide_BVExpr_bitblast_blastUdiv_blastDivSubtractShift(
    mut v_00_u03b1_458_: *mut LeanObject,
    mut v_inst_459_: *mut LeanObject,
    mut v_inst_460_: *mut LeanObject,
    mut v_w_461_: *mut LeanObject,
    mut v_aig_462_: *mut LeanObject,
    mut v_n_463_: *mut LeanObject,
    mut v_d_464_: *mut LeanObject,
    mut v_wn_465_: *mut LeanObject,
    mut v_wr_466_: *mut LeanObject,
    mut v_q_467_: *mut LeanObject,
    mut v_r_468_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_469_: *mut LeanObject = core::ptr::null_mut();
    v___x_469_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastUdiv_blastDivSubtractShift___redArg(
        v_inst_459_,
        v_inst_460_,
        v_w_461_,
        v_aig_462_,
        v_n_463_,
        v_d_464_,
        v_wn_465_,
        v_wr_466_,
        v_q_467_,
        v_r_468_,
    );
    return v___x_469_;
}
pub unsafe fn l_Std_Tactic_BVDecide_BVExpr_bitblast_blastUdiv_blastDivSubtractShift___boxed(
    mut v_00_u03b1_470_: *mut LeanObject,
    mut v_inst_471_: *mut LeanObject,
    mut v_inst_472_: *mut LeanObject,
    mut v_w_473_: *mut LeanObject,
    mut v_aig_474_: *mut LeanObject,
    mut v_n_475_: *mut LeanObject,
    mut v_d_476_: *mut LeanObject,
    mut v_wn_477_: *mut LeanObject,
    mut v_wr_478_: *mut LeanObject,
    mut v_q_479_: *mut LeanObject,
    mut v_r_480_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_481_: *mut LeanObject = core::ptr::null_mut();
    v_res_481_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastUdiv_blastDivSubtractShift(
        v_00_u03b1_470_,
        v_inst_471_,
        v_inst_472_,
        v_w_473_,
        v_aig_474_,
        v_n_475_,
        v_d_476_,
        v_wn_477_,
        v_wr_478_,
        v_q_479_,
        v_r_480_,
    );
    lean_dec(v_wr_478_);
    lean_dec(v_wn_477_);
    lean_dec_ref(v_n_475_);
    return v_res_481_;
}
pub unsafe fn l_Std_Tactic_BVDecide_BVExpr_bitblast_blastUdiv_go___redArg(
    mut v_inst_482_: *mut LeanObject,
    mut v_inst_483_: *mut LeanObject,
    mut v_w_484_: *mut LeanObject,
    mut v_aig_485_: *mut LeanObject,
    mut v_curr_486_: *mut LeanObject,
    mut v_n_487_: *mut LeanObject,
    mut v_d_488_: *mut LeanObject,
    mut v_wn_489_: *mut LeanObject,
    mut v_wr_490_: *mut LeanObject,
    mut v_q_491_: *mut LeanObject,
    mut v_r_492_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_zero_493_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isZero_494_: u8 = 0;
    let mut v___x_495_: *mut LeanObject = core::ptr::null_mut();
    let mut v_res_496_: *mut LeanObject = core::ptr::null_mut();
    let mut v_aig_497_: *mut LeanObject = core::ptr::null_mut();
    let mut v_wn_498_: *mut LeanObject = core::ptr::null_mut();
    let mut v_wr_499_: *mut LeanObject = core::ptr::null_mut();
    let mut v_q_500_: *mut LeanObject = core::ptr::null_mut();
    let mut v_r_501_: *mut LeanObject = core::ptr::null_mut();
    let mut v_one_502_: *mut LeanObject = core::ptr::null_mut();
    let mut v_n_503_: *mut LeanObject = core::ptr::null_mut();
    let mut v_res_504_: *mut LeanObject = core::ptr::null_mut();
    let mut v_aig_505_: *mut LeanObject = core::ptr::null_mut();
    let mut v_q_506_: *mut LeanObject = core::ptr::null_mut();
    let mut v_r_507_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_509_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_510_: u8 = 0;
    let mut v___x_512_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_513_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_514_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_zero_493_ = lean_unsigned_to_nat(0);
                v_isZero_494_ = lean_nat_dec_eq(v_curr_486_, v_zero_493_);
                if v_isZero_494_ == 1 {
                    lean_dec_ref(v_d_488_);
                    lean_dec(v_w_484_);
                    lean_dec_ref(v_inst_483_);
                    lean_dec_ref(v_inst_482_);
                    v___x_495_ = lean_alloc_ctor(0, 3, (0) as u32);
                    lean_ctor_set(v___x_495_, 0, v_aig_485_);
                    lean_ctor_set(v___x_495_, 1, v_q_491_);
                    lean_ctor_set(v___x_495_, 2, v_r_492_);
                    return v___x_495_;
                } else {
                    lean_inc_ref(v_d_488_);
                    lean_inc(v_w_484_);
                    lean_inc_ref(v_inst_483_);
                    lean_inc_ref(v_inst_482_);
                    v_res_496_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastUdiv_blastDivSubtractShift___redArg(v_inst_482_, v_inst_483_, v_w_484_, v_aig_485_, v_n_487_, v_d_488_, v_wn_489_, v_wr_490_, v_q_491_, v_r_492_);
                    v_aig_497_ = lean_ctor_get(v_res_496_, 0);
                    lean_inc_ref(v_aig_497_);
                    v_wn_498_ = lean_ctor_get(v_res_496_, 1);
                    lean_inc(v_wn_498_);
                    v_wr_499_ = lean_ctor_get(v_res_496_, 2);
                    lean_inc(v_wr_499_);
                    v_q_500_ = lean_ctor_get(v_res_496_, 3);
                    lean_inc_ref(v_q_500_);
                    v_r_501_ = lean_ctor_get(v_res_496_, 4);
                    lean_inc_ref(v_r_501_);
                    lean_dec_ref(v_res_496_);
                    v_one_502_ = lean_unsigned_to_nat(1);
                    v_n_503_ = lean_nat_sub(v_curr_486_, v_one_502_);
                    v_res_504_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastUdiv_go___redArg(
                        v_inst_482_,
                        v_inst_483_,
                        v_w_484_,
                        v_aig_497_,
                        v_n_503_,
                        v_n_487_,
                        v_d_488_,
                        v_wn_498_,
                        v_wr_499_,
                        v_q_500_,
                        v_r_501_,
                    );
                    lean_dec(v_wr_499_);
                    lean_dec(v_wn_498_);
                    lean_dec(v_n_503_);
                    v_aig_505_ = lean_ctor_get(v_res_504_, 0);
                    v_q_506_ = lean_ctor_get(v_res_504_, 1);
                    v_r_507_ = lean_ctor_get(v_res_504_, 2);
                    v_isSharedCheck_514_ = (!lean_is_exclusive(v_res_504_)) as u8;
                    if v_isSharedCheck_514_ == 0 {
                        v___x_509_ = v_res_504_;
                        v_isShared_510_ = v_isSharedCheck_514_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_r_507_);
                        lean_inc(v_q_506_);
                        lean_inc(v_aig_505_);
                        lean_dec(v_res_504_);
                        v___x_509_ = lean_box(0);
                        v_isShared_510_ = v_isSharedCheck_514_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_510_ == 0 {
                    v___x_512_ = v___x_509_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_513_ = lean_alloc_ctor(0, 3, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_513_, 0, v_aig_505_);
                    lean_ctor_set(v_reuseFailAlloc_513_, 1, v_q_506_);
                    lean_ctor_set(v_reuseFailAlloc_513_, 2, v_r_507_);
                    v___x_512_ = v_reuseFailAlloc_513_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_512_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Tactic_BVDecide_BVExpr_bitblast_blastUdiv_go___redArg___boxed(
    mut v_inst_515_: *mut LeanObject,
    mut v_inst_516_: *mut LeanObject,
    mut v_w_517_: *mut LeanObject,
    mut v_aig_518_: *mut LeanObject,
    mut v_curr_519_: *mut LeanObject,
    mut v_n_520_: *mut LeanObject,
    mut v_d_521_: *mut LeanObject,
    mut v_wn_522_: *mut LeanObject,
    mut v_wr_523_: *mut LeanObject,
    mut v_q_524_: *mut LeanObject,
    mut v_r_525_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_526_: *mut LeanObject = core::ptr::null_mut();
    v_res_526_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastUdiv_go___redArg(
        v_inst_515_,
        v_inst_516_,
        v_w_517_,
        v_aig_518_,
        v_curr_519_,
        v_n_520_,
        v_d_521_,
        v_wn_522_,
        v_wr_523_,
        v_q_524_,
        v_r_525_,
    );
    lean_dec(v_wr_523_);
    lean_dec(v_wn_522_);
    lean_dec_ref(v_n_520_);
    lean_dec(v_curr_519_);
    return v_res_526_;
}
pub unsafe fn l_Std_Tactic_BVDecide_BVExpr_bitblast_blastUdiv_go(
    mut v_00_u03b1_527_: *mut LeanObject,
    mut v_inst_528_: *mut LeanObject,
    mut v_inst_529_: *mut LeanObject,
    mut v_w_530_: *mut LeanObject,
    mut v_aig_531_: *mut LeanObject,
    mut v_curr_532_: *mut LeanObject,
    mut v_n_533_: *mut LeanObject,
    mut v_d_534_: *mut LeanObject,
    mut v_wn_535_: *mut LeanObject,
    mut v_wr_536_: *mut LeanObject,
    mut v_q_537_: *mut LeanObject,
    mut v_r_538_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_539_: *mut LeanObject = core::ptr::null_mut();
    v___x_539_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastUdiv_go___redArg(
        v_inst_528_,
        v_inst_529_,
        v_w_530_,
        v_aig_531_,
        v_curr_532_,
        v_n_533_,
        v_d_534_,
        v_wn_535_,
        v_wr_536_,
        v_q_537_,
        v_r_538_,
    );
    return v___x_539_;
}
pub unsafe fn l_Std_Tactic_BVDecide_BVExpr_bitblast_blastUdiv_go___boxed(
    mut v_00_u03b1_540_: *mut LeanObject,
    mut v_inst_541_: *mut LeanObject,
    mut v_inst_542_: *mut LeanObject,
    mut v_w_543_: *mut LeanObject,
    mut v_aig_544_: *mut LeanObject,
    mut v_curr_545_: *mut LeanObject,
    mut v_n_546_: *mut LeanObject,
    mut v_d_547_: *mut LeanObject,
    mut v_wn_548_: *mut LeanObject,
    mut v_wr_549_: *mut LeanObject,
    mut v_q_550_: *mut LeanObject,
    mut v_r_551_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_552_: *mut LeanObject = core::ptr::null_mut();
    v_res_552_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastUdiv_go(
        v_00_u03b1_540_,
        v_inst_541_,
        v_inst_542_,
        v_w_543_,
        v_aig_544_,
        v_curr_545_,
        v_n_546_,
        v_d_547_,
        v_wn_548_,
        v_wr_549_,
        v_q_550_,
        v_r_551_,
    );
    lean_dec(v_wr_549_);
    lean_dec(v_wn_548_);
    lean_dec_ref(v_n_546_);
    lean_dec(v_curr_545_);
    return v_res_552_;
}
pub unsafe fn l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Operations_Udiv_0__Std_Tactic_BVDecide_BVExpr_bitblast_blastUdiv_go_match__1_splitter___redArg(
    mut v_curr_553_: *mut LeanObject,
    mut v_h__1_554_: *mut LeanObject,
    mut v_h__2_555_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_zero_556_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isZero_557_: u8 = 0;
    v_zero_556_ = lean_unsigned_to_nat(0);
    v_isZero_557_ = lean_nat_dec_eq(v_curr_553_, v_zero_556_);
    if v_isZero_557_ == 1 {
        let mut v___x_558_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_559_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_555_);
        v___x_558_ = lean_box(0);
        v___x_559_ = lean_apply_1(v_h__1_554_, v___x_558_);
        return v___x_559_;
    } else {
        let mut v_one_560_: *mut LeanObject = core::ptr::null_mut();
        let mut v_n_561_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_562_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_554_);
        v_one_560_ = lean_unsigned_to_nat(1);
        v_n_561_ = lean_nat_sub(v_curr_553_, v_one_560_);
        v___x_562_ = lean_apply_1(v_h__2_555_, v_n_561_);
        return v___x_562_;
    }
}
pub unsafe fn l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Operations_Udiv_0__Std_Tactic_BVDecide_BVExpr_bitblast_blastUdiv_go_match__1_splitter___redArg___boxed(
    mut v_curr_563_: *mut LeanObject,
    mut v_h__1_564_: *mut LeanObject,
    mut v_h__2_565_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_566_: *mut LeanObject = core::ptr::null_mut();
    v_res_566_ = l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Operations_Udiv_0__Std_Tactic_BVDecide_BVExpr_bitblast_blastUdiv_go_match__1_splitter___redArg(v_curr_563_, v_h__1_564_, v_h__2_565_);
    lean_dec(v_curr_563_);
    return v_res_566_;
}
pub unsafe fn l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Operations_Udiv_0__Std_Tactic_BVDecide_BVExpr_bitblast_blastUdiv_go_match__1_splitter(
    mut v_motive_567_: *mut LeanObject,
    mut v_curr_568_: *mut LeanObject,
    mut v_h__1_569_: *mut LeanObject,
    mut v_h__2_570_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_zero_571_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isZero_572_: u8 = 0;
    v_zero_571_ = lean_unsigned_to_nat(0);
    v_isZero_572_ = lean_nat_dec_eq(v_curr_568_, v_zero_571_);
    if v_isZero_572_ == 1 {
        let mut v___x_573_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_574_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_570_);
        v___x_573_ = lean_box(0);
        v___x_574_ = lean_apply_1(v_h__1_569_, v___x_573_);
        return v___x_574_;
    } else {
        let mut v_one_575_: *mut LeanObject = core::ptr::null_mut();
        let mut v_n_576_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_577_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_569_);
        v_one_575_ = lean_unsigned_to_nat(1);
        v_n_576_ = lean_nat_sub(v_curr_568_, v_one_575_);
        v___x_577_ = lean_apply_1(v_h__2_570_, v_n_576_);
        return v___x_577_;
    }
}
pub unsafe fn l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Operations_Udiv_0__Std_Tactic_BVDecide_BVExpr_bitblast_blastUdiv_go_match__1_splitter___boxed(
    mut v_motive_578_: *mut LeanObject,
    mut v_curr_579_: *mut LeanObject,
    mut v_h__1_580_: *mut LeanObject,
    mut v_h__2_581_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_582_: *mut LeanObject = core::ptr::null_mut();
    v_res_582_ = l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Operations_Udiv_0__Std_Tactic_BVDecide_BVExpr_bitblast_blastUdiv_go_match__1_splitter(v_motive_578_, v_curr_579_, v_h__1_580_, v_h__2_581_);
    lean_dec(v_curr_579_);
    return v_res_582_;
}
pub unsafe fn l_Std_Tactic_BVDecide_BVExpr_bitblast_blastUdiv___redArg(
    mut v_inst_583_: *mut LeanObject,
    mut v_inst_584_: *mut LeanObject,
    mut v_w_585_: *mut LeanObject,
    mut v_aig_586_: *mut LeanObject,
    mut v_input_587_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_lhs_588_: *mut LeanObject = core::ptr::null_mut();
    let mut v_rhs_589_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_591_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_592_: u8 = 0;
    let mut v___x_593_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_594_: *mut LeanObject = core::ptr::null_mut();
    let mut v_zero_595_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_597_: *mut LeanObject = core::ptr::null_mut();
    let mut v_res_598_: *mut LeanObject = core::ptr::null_mut();
    let mut v_aig_599_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ref_600_: *mut LeanObject = core::ptr::null_mut();
    let mut v_res_601_: *mut LeanObject = core::ptr::null_mut();
    let mut v_aig_602_: *mut LeanObject = core::ptr::null_mut();
    let mut v_q_603_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_605_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_606_: u8 = 0;
    let mut v_gate_607_: *mut LeanObject = core::ptr::null_mut();
    let mut v_invert_608_: u8 = 0;
    let mut v___x_610_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_611_: u8 = 0;
    let mut v_discr_613_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_615_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_616_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_617_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_618_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_619_: u8 = 0;
    let mut v_isSharedCheck_620_: u8 = 0;
    let mut v_unused_621_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_622_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_623_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_lhs_588_ = lean_ctor_get(v_input_587_, 0);
                v_rhs_589_ = lean_ctor_get(v_input_587_, 1);
                v_isSharedCheck_623_ = (!lean_is_exclusive(v_input_587_)) as u8;
                if v_isSharedCheck_623_ == 0 {
                    v___x_591_ = v_input_587_;
                    v_isShared_592_ = v_isSharedCheck_623_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_rhs_589_);
                    lean_inc(v_lhs_588_);
                    lean_dec(v_input_587_);
                    v___x_591_ = lean_box(0);
                    v_isShared_592_ = v_isSharedCheck_623_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_593_ = lean_unsigned_to_nat(0);
                v___x_594_ = l_BitVec_ofNat(v_w_585_, v___x_593_);
                v_zero_595_ =
                    l_Std_Tactic_BVDecide_BVExpr_bitblast_blastConst___redArg(v_w_585_, v___x_594_);
                lean_dec(v___x_594_);
                lean_inc_ref(v_zero_595_);
                lean_inc_ref(v_rhs_589_);
                if v_isShared_592_ == 0 {
                    lean_ctor_set(v___x_591_, 1, v_zero_595_);
                    lean_ctor_set(v___x_591_, 0, v_rhs_589_);
                    v___x_597_ = v___x_591_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_622_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_622_, 0, v_rhs_589_);
                    lean_ctor_set(v_reuseFailAlloc_622_, 1, v_zero_595_);
                    v___x_597_ = v_reuseFailAlloc_622_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                lean_inc_ref_n(v_inst_584_, 2);
                lean_inc_ref_n(v_inst_583_, 2);
                v_res_598_ = l_Std_Tactic_BVDecide_BVPred_mkEq___redArg(
                    v_inst_583_,
                    v_inst_584_,
                    v_w_585_,
                    v_aig_586_,
                    v___x_597_,
                );
                lean_dec_ref(v___x_597_);
                v_aig_599_ = lean_ctor_get(v_res_598_, 0);
                lean_inc_ref(v_aig_599_);
                v_ref_600_ = lean_ctor_get(v_res_598_, 1);
                lean_inc_ref(v_ref_600_);
                lean_dec_ref(v_res_598_);
                lean_inc_ref_n(v_zero_595_, 2);
                lean_inc(v_w_585_);
                v_res_601_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastUdiv_go___redArg(
                    v_inst_583_,
                    v_inst_584_,
                    v_w_585_,
                    v_aig_599_,
                    v_w_585_,
                    v_lhs_588_,
                    v_rhs_589_,
                    v_w_585_,
                    v___x_593_,
                    v_zero_595_,
                    v_zero_595_,
                );
                lean_dec_ref(v_lhs_588_);
                v_aig_602_ = lean_ctor_get(v_res_601_, 0);
                v_q_603_ = lean_ctor_get(v_res_601_, 1);
                v_isSharedCheck_620_ = (!lean_is_exclusive(v_res_601_)) as u8;
                if v_isSharedCheck_620_ == 0 {
                    v_unused_621_ = lean_ctor_get(v_res_601_, 2);
                    lean_dec(v_unused_621_);
                    v___x_605_ = v_res_601_;
                    v_isShared_606_ = v_isSharedCheck_620_;
                    state = 3;
                    continue;
                } else {
                    lean_inc(v_q_603_);
                    lean_inc(v_aig_602_);
                    lean_dec(v_res_601_);
                    v___x_605_ = lean_box(0);
                    v_isShared_606_ = v_isSharedCheck_620_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v_gate_607_ = lean_ctor_get(v_ref_600_, 0);
                v_invert_608_ = lean_ctor_get_uint8(
                    v_ref_600_,
                    (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                );
                v_isSharedCheck_619_ = (!lean_is_exclusive(v_ref_600_)) as u8;
                if v_isSharedCheck_619_ == 0 {
                    v___x_610_ = v_ref_600_;
                    v_isShared_611_ = v_isSharedCheck_619_;
                    state = 4;
                    continue;
                } else {
                    lean_inc(v_gate_607_);
                    lean_dec(v_ref_600_);
                    v___x_610_ = lean_box(0);
                    v_isShared_611_ = v_isSharedCheck_619_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                if v_isShared_611_ == 0 {
                    v_discr_613_ = v___x_610_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_618_ = lean_alloc_ctor(0, 1, (1) as u32);
                    lean_ctor_set(v_reuseFailAlloc_618_, 0, v_gate_607_);
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_618_,
                        (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                        v_invert_608_,
                    );
                    v_discr_613_ = v_reuseFailAlloc_618_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                if v_isShared_606_ == 0 {
                    lean_ctor_set(v___x_605_, 2, v_q_603_);
                    lean_ctor_set(v___x_605_, 1, v_zero_595_);
                    lean_ctor_set(v___x_605_, 0, v_discr_613_);
                    v___x_615_ = v___x_605_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_617_ = lean_alloc_ctor(0, 3, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_617_, 0, v_discr_613_);
                    lean_ctor_set(v_reuseFailAlloc_617_, 1, v_zero_595_);
                    lean_ctor_set(v_reuseFailAlloc_617_, 2, v_q_603_);
                    v___x_615_ = v_reuseFailAlloc_617_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                v___x_616_ = l_Std_Sat_AIG_RefVec_ite___redArg(
                    v_inst_583_,
                    v_inst_584_,
                    v_w_585_,
                    v_aig_602_,
                    v___x_615_,
                );
                lean_dec(v_w_585_);
                return v___x_616_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Tactic_BVDecide_BVExpr_bitblast_blastUdiv(
    mut v_00_u03b1_624_: *mut LeanObject,
    mut v_inst_625_: *mut LeanObject,
    mut v_inst_626_: *mut LeanObject,
    mut v_w_627_: *mut LeanObject,
    mut v_aig_628_: *mut LeanObject,
    mut v_input_629_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_630_: *mut LeanObject = core::ptr::null_mut();
    v___x_630_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastUdiv___redArg(
        v_inst_625_,
        v_inst_626_,
        v_w_627_,
        v_aig_628_,
        v_input_629_,
    );
    return v___x_630_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Operations_Udiv(
    builtin: u8,
) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res =
        runtime_initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Operations_Sub(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res =
        runtime_initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Operations_Eq(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res =
        runtime_initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Operations_Ult(builtin);
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
pub unsafe fn meta_initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Operations_Udiv(
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
pub unsafe fn initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Operations_Udiv(
    builtin: u8,
) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Operations_Sub(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Operations_Eq(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Operations_Ult(builtin);
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
    res = runtime_initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Operations_Udiv(
        builtin,
    );
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Operations_Udiv(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Operations_Udiv(builtin);
}
