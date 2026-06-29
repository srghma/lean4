// Lean compiler output
// Module: Std.Tactic.BVDecide.Bitblast.BVExpr.Circuit.Impl.Operations.ShiftRight
// Imports: Std.Tactic.BVDecide.Bitblast.BVExpr.Basic Std.Sat.AIG.If Init.Omega
use crate::ffi::{
    lean_array_fget_borrowed, lean_array_push, lean_mk_empty_array_with_capacity, lean_nat_add,
    lean_nat_dec_eq, lean_nat_dec_lt, lean_nat_land, lean_nat_lor, lean_nat_mul, lean_nat_pow,
    lean_nat_shiftr, lean_nat_sub,
};
use crate::r#gen::Init::Data::Bool::l_Bool_toNat;
use crate::r#gen::Init::Omega::{initialize_Init_Omega, runtime_initialize_Init_Omega};
use crate::r#gen::Std::Sat::AIG::If::{
    initialize_Std_Sat_AIG_If, l_Std_Sat_AIG_RefVec_ite___redArg, runtime_initialize_Std_Sat_AIG_If,
};
use crate::r#gen::Std::Tactic::BVDecide::Bitblast::BVExpr::Basic::{
    initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Basic,
    runtime_initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Basic,
};
pub unsafe fn l_Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftRightConst_go___redArg(
    mut v_w_461_: *mut crate::leanh::LeanObject,
    mut v_aig_462_: *mut crate::leanh::LeanObject,
    mut v_input_463_: *mut crate::leanh::LeanObject,
    mut v_distance_464_: *mut crate::leanh::LeanObject,
    mut v_curr_465_: *mut crate::leanh::LeanObject,
    mut v_s_466_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_gate_468_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_invert_469_: u8 = 0;
    let mut v___x_470_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_471_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_472_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_473_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_474_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_475_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_s_476_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_478_: u8 = 0;
    let mut v___x_479_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_480_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_481_: u8 = 0;
    let mut v___x_482_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_483_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_484_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_485_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_486_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_s_487_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_489_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_490_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_491_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_492_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_493_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_494_: u8 = 0;
    let mut v___x_495_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_478_ = lean_nat_dec_lt(v_curr_465_, v_w_461_);
                if v___x_478_ == 0 {
                    crate::leanh::lean_dec(v_curr_465_);
                    v___x_479_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_479_, 0, v_aig_462_);
                    crate::leanh::lean_ctor_set(v___x_479_, 1, v_s_466_);
                    return v___x_479_;
                } else {
                    v___x_480_ = lean_nat_add(v_distance_464_, v_curr_465_);
                    v___x_481_ = lean_nat_dec_lt(v___x_480_, v_w_461_);
                    if v___x_481_ == 0 {
                        crate::leanh::lean_dec(v___x_480_);
                        v___x_482_ = crate::leanh::lean_unsigned_to_nat(1);
                        v___x_483_ = lean_nat_add(v_curr_465_, v___x_482_);
                        crate::leanh::lean_dec(v_curr_465_);
                        v___x_484_ = crate::leanh::lean_unsigned_to_nat(0);
                        v___x_485_ = l_Bool_toNat(v___x_481_);
                        v___x_486_ = lean_nat_lor(v___x_484_, v___x_485_);
                        crate::leanh::lean_dec(v___x_485_);
                        v_s_487_ = lean_array_push(v_s_466_, v___x_486_);
                        v_curr_465_ = v___x_483_;
                        v_s_466_ = v_s_487_;
                        state = 0;
                        continue;
                    } else {
                        v_ref_489_ = lean_array_fget_borrowed(v_input_463_, v___x_480_);
                        crate::leanh::lean_dec(v___x_480_);
                        v___x_490_ = crate::leanh::lean_unsigned_to_nat(1);
                        v___x_491_ = lean_nat_shiftr(v_ref_489_, v___x_490_);
                        v___x_492_ = lean_nat_land(v___x_490_, v_ref_489_);
                        v___x_493_ = crate::leanh::lean_unsigned_to_nat(0);
                        v___x_494_ = lean_nat_dec_eq(v___x_492_, v___x_493_);
                        crate::leanh::lean_dec(v___x_492_);
                        if v___x_494_ == 0 {
                            v_gate_468_ = v___x_491_;
                            v_invert_469_ = v___x_481_;
                            state = 1;
                            continue;
                        } else {
                            v___x_495_ = 0;
                            v_gate_468_ = v___x_491_;
                            v_invert_469_ = v___x_495_;
                            state = 1;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v___x_470_ = crate::leanh::lean_unsigned_to_nat(1);
                v___x_471_ = lean_nat_add(v_curr_465_, v___x_470_);
                crate::leanh::lean_dec(v_curr_465_);
                v___x_472_ = crate::leanh::lean_unsigned_to_nat(2);
                v___x_473_ = lean_nat_mul(v_gate_468_, v___x_472_);
                crate::leanh::lean_dec(v_gate_468_);
                v___x_474_ = l_Bool_toNat(v_invert_469_);
                v___x_475_ = lean_nat_lor(v___x_473_, v___x_474_);
                crate::leanh::lean_dec(v___x_474_);
                crate::leanh::lean_dec(v___x_473_);
                v_s_476_ = lean_array_push(v_s_466_, v___x_475_);
                v_curr_465_ = v___x_471_;
                v_s_466_ = v_s_476_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftRightConst_go___redArg___boxed(
    mut v_w_496_: *mut crate::leanh::LeanObject,
    mut v_aig_497_: *mut crate::leanh::LeanObject,
    mut v_input_498_: *mut crate::leanh::LeanObject,
    mut v_distance_499_: *mut crate::leanh::LeanObject,
    mut v_curr_500_: *mut crate::leanh::LeanObject,
    mut v_s_501_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_502_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_502_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftRightConst_go___redArg(
        v_w_496_,
        v_aig_497_,
        v_input_498_,
        v_distance_499_,
        v_curr_500_,
        v_s_501_,
    );
    crate::leanh::lean_dec(v_distance_499_);
    crate::leanh::lean_dec_ref(v_input_498_);
    crate::leanh::lean_dec(v_w_496_);
    return v_res_502_;
}
pub unsafe fn l_Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftRightConst_go(
    mut v_00_u03b1_503_: *mut crate::leanh::LeanObject,
    mut v_inst_504_: *mut crate::leanh::LeanObject,
    mut v_inst_505_: *mut crate::leanh::LeanObject,
    mut v_w_506_: *mut crate::leanh::LeanObject,
    mut v_aig_507_: *mut crate::leanh::LeanObject,
    mut v_input_508_: *mut crate::leanh::LeanObject,
    mut v_distance_509_: *mut crate::leanh::LeanObject,
    mut v_curr_510_: *mut crate::leanh::LeanObject,
    mut v_hcurr_511_: *mut crate::leanh::LeanObject,
    mut v_s_512_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_513_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_513_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftRightConst_go___redArg(
        v_w_506_,
        v_aig_507_,
        v_input_508_,
        v_distance_509_,
        v_curr_510_,
        v_s_512_,
    );
    return v___x_513_;
}
pub unsafe fn l_Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftRightConst_go___boxed(
    mut v_00_u03b1_514_: *mut crate::leanh::LeanObject,
    mut v_inst_515_: *mut crate::leanh::LeanObject,
    mut v_inst_516_: *mut crate::leanh::LeanObject,
    mut v_w_517_: *mut crate::leanh::LeanObject,
    mut v_aig_518_: *mut crate::leanh::LeanObject,
    mut v_input_519_: *mut crate::leanh::LeanObject,
    mut v_distance_520_: *mut crate::leanh::LeanObject,
    mut v_curr_521_: *mut crate::leanh::LeanObject,
    mut v_hcurr_522_: *mut crate::leanh::LeanObject,
    mut v_s_523_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_524_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_524_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftRightConst_go(
        v_00_u03b1_514_,
        v_inst_515_,
        v_inst_516_,
        v_w_517_,
        v_aig_518_,
        v_input_519_,
        v_distance_520_,
        v_curr_521_,
        v_hcurr_522_,
        v_s_523_,
    );
    crate::leanh::lean_dec(v_distance_520_);
    crate::leanh::lean_dec_ref(v_input_519_);
    crate::leanh::lean_dec(v_w_517_);
    crate::leanh::lean_dec_ref(v_inst_516_);
    crate::leanh::lean_dec_ref(v_inst_515_);
    return v_res_524_;
}
pub unsafe fn l_Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftRightConst___redArg(
    mut v_w_525_: *mut crate::leanh::LeanObject,
    mut v_aig_526_: *mut crate::leanh::LeanObject,
    mut v_target_527_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_vec_528_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_distance_529_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_530_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_531_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_532_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_vec_528_ = crate::leanh::lean_ctor_get(v_target_527_, 0);
    v_distance_529_ = crate::leanh::lean_ctor_get(v_target_527_, 1);
    v___x_530_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_531_ = lean_mk_empty_array_with_capacity(v_w_525_);
    v___x_532_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftRightConst_go___redArg(
        v_w_525_,
        v_aig_526_,
        v_vec_528_,
        v_distance_529_,
        v___x_530_,
        v___x_531_,
    );
    return v___x_532_;
}
pub unsafe fn l_Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftRightConst___redArg___boxed(
    mut v_w_533_: *mut crate::leanh::LeanObject,
    mut v_aig_534_: *mut crate::leanh::LeanObject,
    mut v_target_535_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_536_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_536_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftRightConst___redArg(
        v_w_533_,
        v_aig_534_,
        v_target_535_,
    );
    crate::leanh::lean_dec_ref(v_target_535_);
    crate::leanh::lean_dec(v_w_533_);
    return v_res_536_;
}
pub unsafe fn l_Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftRightConst(
    mut v_00_u03b1_537_: *mut crate::leanh::LeanObject,
    mut v_inst_538_: *mut crate::leanh::LeanObject,
    mut v_inst_539_: *mut crate::leanh::LeanObject,
    mut v_w_540_: *mut crate::leanh::LeanObject,
    mut v_aig_541_: *mut crate::leanh::LeanObject,
    mut v_target_542_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_543_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_543_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftRightConst___redArg(
        v_w_540_,
        v_aig_541_,
        v_target_542_,
    );
    return v___x_543_;
}
pub unsafe fn l_Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftRightConst___boxed(
    mut v_00_u03b1_544_: *mut crate::leanh::LeanObject,
    mut v_inst_545_: *mut crate::leanh::LeanObject,
    mut v_inst_546_: *mut crate::leanh::LeanObject,
    mut v_w_547_: *mut crate::leanh::LeanObject,
    mut v_aig_548_: *mut crate::leanh::LeanObject,
    mut v_target_549_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_550_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_550_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftRightConst(
        v_00_u03b1_544_,
        v_inst_545_,
        v_inst_546_,
        v_w_547_,
        v_aig_548_,
        v_target_549_,
    );
    crate::leanh::lean_dec_ref(v_target_549_);
    crate::leanh::lean_dec(v_w_547_);
    crate::leanh::lean_dec_ref(v_inst_546_);
    crate::leanh::lean_dec_ref(v_inst_545_);
    return v_res_550_;
}
pub unsafe fn l_Std_Tactic_BVDecide_BVExpr_bitblast_blastArithShiftRightConst_go___redArg(
    mut v_w_551_: *mut crate::leanh::LeanObject,
    mut v_input_552_: *mut crate::leanh::LeanObject,
    mut v_distance_553_: *mut crate::leanh::LeanObject,
    mut v_curr_554_: *mut crate::leanh::LeanObject,
    mut v_s_555_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_gate_557_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_invert_558_: u8 = 0;
    let mut v___x_559_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_560_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_561_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_562_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_563_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_564_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_s_565_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_567_: u8 = 0;
    let mut v___x_568_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_569_: u8 = 0;
    let mut v___x_570_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_gate_572_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_invert_573_: u8 = 0;
    let mut v___x_574_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_575_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_576_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_577_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_578_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_s_579_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_581_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_582_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_583_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_584_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_585_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_586_: u8 = 0;
    let mut v_ref_587_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_588_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_589_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_590_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_591_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_592_: u8 = 0;
    let mut v___x_593_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_567_ = lean_nat_dec_lt(v_curr_554_, v_w_551_);
                if v___x_567_ == 0 {
                    crate::leanh::lean_dec(v_curr_554_);
                    return v_s_555_;
                } else {
                    v___x_568_ = lean_nat_add(v_distance_553_, v_curr_554_);
                    v___x_569_ = lean_nat_dec_lt(v___x_568_, v_w_551_);
                    if v___x_569_ == 0 {
                        crate::leanh::lean_dec(v___x_568_);
                        v___x_570_ = crate::leanh::lean_unsigned_to_nat(1);
                        v___x_581_ = lean_nat_sub(v_w_551_, v___x_570_);
                        v_ref_582_ = lean_array_fget_borrowed(v_input_552_, v___x_581_);
                        crate::leanh::lean_dec(v___x_581_);
                        v___x_583_ = lean_nat_shiftr(v_ref_582_, v___x_570_);
                        v___x_584_ = lean_nat_land(v___x_570_, v_ref_582_);
                        v___x_585_ = crate::leanh::lean_unsigned_to_nat(0);
                        v___x_586_ = lean_nat_dec_eq(v___x_584_, v___x_585_);
                        crate::leanh::lean_dec(v___x_584_);
                        if v___x_586_ == 0 {
                            v_gate_572_ = v___x_583_;
                            v_invert_573_ = v___x_567_;
                            state = 2;
                            continue;
                        } else {
                            v_gate_572_ = v___x_583_;
                            v_invert_573_ = v___x_569_;
                            state = 2;
                            continue;
                        }
                    } else {
                        v_ref_587_ = lean_array_fget_borrowed(v_input_552_, v___x_568_);
                        crate::leanh::lean_dec(v___x_568_);
                        v___x_588_ = crate::leanh::lean_unsigned_to_nat(1);
                        v___x_589_ = lean_nat_shiftr(v_ref_587_, v___x_588_);
                        v___x_590_ = lean_nat_land(v___x_588_, v_ref_587_);
                        v___x_591_ = crate::leanh::lean_unsigned_to_nat(0);
                        v___x_592_ = lean_nat_dec_eq(v___x_590_, v___x_591_);
                        crate::leanh::lean_dec(v___x_590_);
                        if v___x_592_ == 0 {
                            v_gate_557_ = v___x_589_;
                            v_invert_558_ = v___x_569_;
                            state = 1;
                            continue;
                        } else {
                            v___x_593_ = 0;
                            v_gate_557_ = v___x_589_;
                            v_invert_558_ = v___x_593_;
                            state = 1;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v___x_559_ = crate::leanh::lean_unsigned_to_nat(1);
                v___x_560_ = lean_nat_add(v_curr_554_, v___x_559_);
                crate::leanh::lean_dec(v_curr_554_);
                v___x_561_ = crate::leanh::lean_unsigned_to_nat(2);
                v___x_562_ = lean_nat_mul(v_gate_557_, v___x_561_);
                crate::leanh::lean_dec(v_gate_557_);
                v___x_563_ = l_Bool_toNat(v_invert_558_);
                v___x_564_ = lean_nat_lor(v___x_562_, v___x_563_);
                crate::leanh::lean_dec(v___x_563_);
                crate::leanh::lean_dec(v___x_562_);
                v_s_565_ = lean_array_push(v_s_555_, v___x_564_);
                v_curr_554_ = v___x_560_;
                v_s_555_ = v_s_565_;
                state = 0;
                continue;
            }
            2 => {
                v___x_574_ = lean_nat_add(v_curr_554_, v___x_570_);
                crate::leanh::lean_dec(v_curr_554_);
                v___x_575_ = crate::leanh::lean_unsigned_to_nat(2);
                v___x_576_ = lean_nat_mul(v_gate_572_, v___x_575_);
                crate::leanh::lean_dec(v_gate_572_);
                v___x_577_ = l_Bool_toNat(v_invert_573_);
                v___x_578_ = lean_nat_lor(v___x_576_, v___x_577_);
                crate::leanh::lean_dec(v___x_577_);
                crate::leanh::lean_dec(v___x_576_);
                v_s_579_ = lean_array_push(v_s_555_, v___x_578_);
                v_curr_554_ = v___x_574_;
                v_s_555_ = v_s_579_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Tactic_BVDecide_BVExpr_bitblast_blastArithShiftRightConst_go___redArg___boxed(
    mut v_w_594_: *mut crate::leanh::LeanObject,
    mut v_input_595_: *mut crate::leanh::LeanObject,
    mut v_distance_596_: *mut crate::leanh::LeanObject,
    mut v_curr_597_: *mut crate::leanh::LeanObject,
    mut v_s_598_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_599_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_599_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastArithShiftRightConst_go___redArg(
        v_w_594_,
        v_input_595_,
        v_distance_596_,
        v_curr_597_,
        v_s_598_,
    );
    crate::leanh::lean_dec(v_distance_596_);
    crate::leanh::lean_dec_ref(v_input_595_);
    crate::leanh::lean_dec(v_w_594_);
    return v_res_599_;
}
pub unsafe fn l_Std_Tactic_BVDecide_BVExpr_bitblast_blastArithShiftRightConst_go(
    mut v_00_u03b1_600_: *mut crate::leanh::LeanObject,
    mut v_inst_601_: *mut crate::leanh::LeanObject,
    mut v_inst_602_: *mut crate::leanh::LeanObject,
    mut v_w_603_: *mut crate::leanh::LeanObject,
    mut v_aig_604_: *mut crate::leanh::LeanObject,
    mut v_input_605_: *mut crate::leanh::LeanObject,
    mut v_distance_606_: *mut crate::leanh::LeanObject,
    mut v_curr_607_: *mut crate::leanh::LeanObject,
    mut v_hcurr_608_: *mut crate::leanh::LeanObject,
    mut v_s_609_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_610_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_610_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastArithShiftRightConst_go___redArg(
        v_w_603_,
        v_input_605_,
        v_distance_606_,
        v_curr_607_,
        v_s_609_,
    );
    return v___x_610_;
}
pub unsafe fn l_Std_Tactic_BVDecide_BVExpr_bitblast_blastArithShiftRightConst_go___boxed(
    mut v_00_u03b1_611_: *mut crate::leanh::LeanObject,
    mut v_inst_612_: *mut crate::leanh::LeanObject,
    mut v_inst_613_: *mut crate::leanh::LeanObject,
    mut v_w_614_: *mut crate::leanh::LeanObject,
    mut v_aig_615_: *mut crate::leanh::LeanObject,
    mut v_input_616_: *mut crate::leanh::LeanObject,
    mut v_distance_617_: *mut crate::leanh::LeanObject,
    mut v_curr_618_: *mut crate::leanh::LeanObject,
    mut v_hcurr_619_: *mut crate::leanh::LeanObject,
    mut v_s_620_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_621_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_621_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastArithShiftRightConst_go(
        v_00_u03b1_611_,
        v_inst_612_,
        v_inst_613_,
        v_w_614_,
        v_aig_615_,
        v_input_616_,
        v_distance_617_,
        v_curr_618_,
        v_hcurr_619_,
        v_s_620_,
    );
    crate::leanh::lean_dec(v_distance_617_);
    crate::leanh::lean_dec_ref(v_input_616_);
    crate::leanh::lean_dec_ref(v_aig_615_);
    crate::leanh::lean_dec(v_w_614_);
    crate::leanh::lean_dec_ref(v_inst_613_);
    crate::leanh::lean_dec_ref(v_inst_612_);
    return v_res_621_;
}
pub unsafe fn l_Std_Tactic_BVDecide_BVExpr_bitblast_blastArithShiftRightConst___redArg(
    mut v_w_622_: *mut crate::leanh::LeanObject,
    mut v_aig_623_: *mut crate::leanh::LeanObject,
    mut v_target_624_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_vec_625_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_distance_626_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_628_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_629_: u8 = 0;
    let mut v___x_630_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_631_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_632_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_634_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_635_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_636_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_vec_625_ = crate::leanh::lean_ctor_get(v_target_624_, 0);
                v_distance_626_ = crate::leanh::lean_ctor_get(v_target_624_, 1);
                v_isSharedCheck_636_ = (!crate::leanh::lean_is_exclusive(v_target_624_)) as u8;
                if v_isSharedCheck_636_ == 0 {
                    v___x_628_ = v_target_624_;
                    v_isShared_629_ = v_isSharedCheck_636_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_distance_626_);
                    crate::leanh::lean_inc(v_vec_625_);
                    crate::leanh::lean_dec(v_target_624_);
                    v___x_628_ = crate::leanh::lean_box(0);
                    v_isShared_629_ = v_isSharedCheck_636_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_630_ = crate::leanh::lean_unsigned_to_nat(0);
                v___x_631_ = lean_mk_empty_array_with_capacity(v_w_622_);
                v___x_632_ =
                    l_Std_Tactic_BVDecide_BVExpr_bitblast_blastArithShiftRightConst_go___redArg(
                        v_w_622_,
                        v_vec_625_,
                        v_distance_626_,
                        v___x_630_,
                        v___x_631_,
                    );
                crate::leanh::lean_dec(v_distance_626_);
                crate::leanh::lean_dec_ref(v_vec_625_);
                if v_isShared_629_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_628_, 1, v___x_632_);
                    crate::leanh::lean_ctor_set(v___x_628_, 0, v_aig_623_);
                    v___x_634_ = v___x_628_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_635_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_635_, 0, v_aig_623_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_635_, 1, v___x_632_);
                    v___x_634_ = v_reuseFailAlloc_635_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_634_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Tactic_BVDecide_BVExpr_bitblast_blastArithShiftRightConst___redArg___boxed(
    mut v_w_637_: *mut crate::leanh::LeanObject,
    mut v_aig_638_: *mut crate::leanh::LeanObject,
    mut v_target_639_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_640_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_640_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastArithShiftRightConst___redArg(
        v_w_637_,
        v_aig_638_,
        v_target_639_,
    );
    crate::leanh::lean_dec(v_w_637_);
    return v_res_640_;
}
pub unsafe fn l_Std_Tactic_BVDecide_BVExpr_bitblast_blastArithShiftRightConst(
    mut v_00_u03b1_641_: *mut crate::leanh::LeanObject,
    mut v_inst_642_: *mut crate::leanh::LeanObject,
    mut v_inst_643_: *mut crate::leanh::LeanObject,
    mut v_w_644_: *mut crate::leanh::LeanObject,
    mut v_aig_645_: *mut crate::leanh::LeanObject,
    mut v_target_646_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_647_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_647_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastArithShiftRightConst___redArg(
        v_w_644_,
        v_aig_645_,
        v_target_646_,
    );
    return v___x_647_;
}
pub unsafe fn l_Std_Tactic_BVDecide_BVExpr_bitblast_blastArithShiftRightConst___boxed(
    mut v_00_u03b1_648_: *mut crate::leanh::LeanObject,
    mut v_inst_649_: *mut crate::leanh::LeanObject,
    mut v_inst_650_: *mut crate::leanh::LeanObject,
    mut v_w_651_: *mut crate::leanh::LeanObject,
    mut v_aig_652_: *mut crate::leanh::LeanObject,
    mut v_target_653_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_654_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_654_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastArithShiftRightConst(
        v_00_u03b1_648_,
        v_inst_649_,
        v_inst_650_,
        v_w_651_,
        v_aig_652_,
        v_target_653_,
    );
    crate::leanh::lean_dec(v_w_651_);
    crate::leanh::lean_dec_ref(v_inst_650_);
    crate::leanh::lean_dec_ref(v_inst_649_);
    return v_res_654_;
}
pub unsafe fn l_Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftRight_twoPowShift___redArg(
    mut v_inst_655_: *mut crate::leanh::LeanObject,
    mut v_inst_656_: *mut crate::leanh::LeanObject,
    mut v_w_657_: *mut crate::leanh::LeanObject,
    mut v_aig_658_: *mut crate::leanh::LeanObject,
    mut v_target_659_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_n_660_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_lhs_661_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_rhs_662_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_pow_663_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_664_: u8 = 0;
    let mut v___x_665_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_666_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_667_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_668_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_res_669_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_aig_670_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_vec_671_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_673_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_674_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_675_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_676_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_677_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_678_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_679_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_680_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_681_: u8 = 0;
    let mut v___x_682_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_683_: u8 = 0;
    let mut v___x_684_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_n_660_ = crate::leanh::lean_ctor_get(v_target_659_, 0);
                v_lhs_661_ = crate::leanh::lean_ctor_get(v_target_659_, 1);
                v_rhs_662_ = crate::leanh::lean_ctor_get(v_target_659_, 2);
                v_pow_663_ = crate::leanh::lean_ctor_get(v_target_659_, 3);
                v___x_664_ = lean_nat_dec_lt(v_pow_663_, v_n_660_);
                if v___x_664_ == 0 {
                    crate::leanh::lean_dec_ref(v_inst_656_);
                    crate::leanh::lean_dec_ref(v_inst_655_);
                    crate::leanh::lean_inc_ref(v_lhs_661_);
                    v___x_665_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_665_, 0, v_aig_658_);
                    crate::leanh::lean_ctor_set(v___x_665_, 1, v_lhs_661_);
                    return v___x_665_;
                } else {
                    v___x_666_ = crate::leanh::lean_unsigned_to_nat(2);
                    v___x_667_ = lean_nat_pow(v___x_666_, v_pow_663_);
                    crate::leanh::lean_inc_ref(v_lhs_661_);
                    v___x_668_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_668_, 0, v_lhs_661_);
                    crate::leanh::lean_ctor_set(v___x_668_, 1, v___x_667_);
                    v_res_669_ =
                        l_Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftRightConst___redArg(
                            v_w_657_, v_aig_658_, v___x_668_,
                        );
                    crate::leanh::lean_dec_ref_known(v___x_668_, 2);
                    v_aig_670_ = crate::leanh::lean_ctor_get(v_res_669_, 0);
                    crate::leanh::lean_inc_ref(v_aig_670_);
                    v_vec_671_ = crate::leanh::lean_ctor_get(v_res_669_, 1);
                    crate::leanh::lean_inc_ref(v_vec_671_);
                    crate::leanh::lean_dec_ref(v_res_669_);
                    v_ref_676_ = lean_array_fget_borrowed(v_rhs_662_, v_pow_663_);
                    v___x_677_ = crate::leanh::lean_unsigned_to_nat(1);
                    v___x_678_ = lean_nat_shiftr(v_ref_676_, v___x_677_);
                    v___x_679_ = lean_nat_land(v___x_677_, v_ref_676_);
                    v___x_680_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___x_681_ = lean_nat_dec_eq(v___x_679_, v___x_680_);
                    crate::leanh::lean_dec(v___x_679_);
                    if v___x_681_ == 0 {
                        v___x_682_ = crate::leanh::lean_alloc_ctor(0, 1, (1) as u32);
                        crate::leanh::lean_ctor_set(v___x_682_, 0, v___x_678_);
                        crate::leanh::lean_ctor_set_uint8(
                            v___x_682_,
                            (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                            v___x_664_,
                        );
                        v___y_673_ = v___x_682_;
                        state = 1;
                        continue;
                    } else {
                        v___x_683_ = 0;
                        v___x_684_ = crate::leanh::lean_alloc_ctor(0, 1, (1) as u32);
                        crate::leanh::lean_ctor_set(v___x_684_, 0, v___x_678_);
                        crate::leanh::lean_ctor_set_uint8(
                            v___x_684_,
                            (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                            v___x_683_,
                        );
                        v___y_673_ = v___x_684_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                crate::leanh::lean_inc_ref(v_lhs_661_);
                v___x_674_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_674_, 0, v___y_673_);
                crate::leanh::lean_ctor_set(v___x_674_, 1, v_vec_671_);
                crate::leanh::lean_ctor_set(v___x_674_, 2, v_lhs_661_);
                v___x_675_ = l_Std_Sat_AIG_RefVec_ite___redArg(
                    v_inst_655_,
                    v_inst_656_,
                    v_w_657_,
                    v_aig_670_,
                    v___x_674_,
                );
                return v___x_675_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftRight_twoPowShift___redArg___boxed(
    mut v_inst_685_: *mut crate::leanh::LeanObject,
    mut v_inst_686_: *mut crate::leanh::LeanObject,
    mut v_w_687_: *mut crate::leanh::LeanObject,
    mut v_aig_688_: *mut crate::leanh::LeanObject,
    mut v_target_689_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_690_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_690_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftRight_twoPowShift___redArg(
        v_inst_685_,
        v_inst_686_,
        v_w_687_,
        v_aig_688_,
        v_target_689_,
    );
    crate::leanh::lean_dec_ref(v_target_689_);
    crate::leanh::lean_dec(v_w_687_);
    return v_res_690_;
}
pub unsafe fn l_Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftRight_twoPowShift(
    mut v_00_u03b1_691_: *mut crate::leanh::LeanObject,
    mut v_inst_692_: *mut crate::leanh::LeanObject,
    mut v_inst_693_: *mut crate::leanh::LeanObject,
    mut v_w_694_: *mut crate::leanh::LeanObject,
    mut v_aig_695_: *mut crate::leanh::LeanObject,
    mut v_target_696_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_697_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_697_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftRight_twoPowShift___redArg(
        v_inst_692_,
        v_inst_693_,
        v_w_694_,
        v_aig_695_,
        v_target_696_,
    );
    return v___x_697_;
}
pub unsafe fn l_Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftRight_twoPowShift___boxed(
    mut v_00_u03b1_698_: *mut crate::leanh::LeanObject,
    mut v_inst_699_: *mut crate::leanh::LeanObject,
    mut v_inst_700_: *mut crate::leanh::LeanObject,
    mut v_w_701_: *mut crate::leanh::LeanObject,
    mut v_aig_702_: *mut crate::leanh::LeanObject,
    mut v_target_703_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_704_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_704_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftRight_twoPowShift(
        v_00_u03b1_698_,
        v_inst_699_,
        v_inst_700_,
        v_w_701_,
        v_aig_702_,
        v_target_703_,
    );
    crate::leanh::lean_dec_ref(v_target_703_);
    crate::leanh::lean_dec(v_w_701_);
    return v_res_704_;
}
pub unsafe fn l_Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftRight_go___redArg(
    mut v_inst_705_: *mut crate::leanh::LeanObject,
    mut v_inst_706_: *mut crate::leanh::LeanObject,
    mut v_w_707_: *mut crate::leanh::LeanObject,
    mut v_n_708_: *mut crate::leanh::LeanObject,
    mut v_aig_709_: *mut crate::leanh::LeanObject,
    mut v_distance_710_: *mut crate::leanh::LeanObject,
    mut v_curr_711_: *mut crate::leanh::LeanObject,
    mut v_acc_712_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_713_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_714_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_715_: u8 = 0;
    let mut v___x_716_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_717_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_718_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_res_719_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_aig_720_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_vec_721_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_713_ = crate::leanh::lean_unsigned_to_nat(1);
                v___x_714_ = lean_nat_sub(v_n_708_, v___x_713_);
                v___x_715_ = lean_nat_dec_lt(v_curr_711_, v___x_714_);
                crate::leanh::lean_dec(v___x_714_);
                if v___x_715_ == 0 {
                    crate::leanh::lean_dec(v_curr_711_);
                    crate::leanh::lean_dec_ref(v_distance_710_);
                    crate::leanh::lean_dec(v_n_708_);
                    crate::leanh::lean_dec_ref(v_inst_706_);
                    crate::leanh::lean_dec_ref(v_inst_705_);
                    v___x_716_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_716_, 0, v_aig_709_);
                    crate::leanh::lean_ctor_set(v___x_716_, 1, v_acc_712_);
                    return v___x_716_;
                } else {
                    v___x_717_ = lean_nat_add(v_curr_711_, v___x_713_);
                    crate::leanh::lean_dec(v_curr_711_);
                    crate::leanh::lean_inc(v___x_717_);
                    crate::leanh::lean_inc_ref(v_distance_710_);
                    crate::leanh::lean_inc(v_n_708_);
                    v___x_718_ = crate::leanh::lean_alloc_ctor(0, 4, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_718_, 0, v_n_708_);
                    crate::leanh::lean_ctor_set(v___x_718_, 1, v_acc_712_);
                    crate::leanh::lean_ctor_set(v___x_718_, 2, v_distance_710_);
                    crate::leanh::lean_ctor_set(v___x_718_, 3, v___x_717_);
                    crate::leanh::lean_inc_ref(v_inst_706_);
                    crate::leanh::lean_inc_ref(v_inst_705_);
                    v_res_719_ =
                        l_Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftRight_twoPowShift___redArg(
                            v_inst_705_,
                            v_inst_706_,
                            v_w_707_,
                            v_aig_709_,
                            v___x_718_,
                        );
                    crate::leanh::lean_dec_ref_known(v___x_718_, 4);
                    v_aig_720_ = crate::leanh::lean_ctor_get(v_res_719_, 0);
                    crate::leanh::lean_inc_ref(v_aig_720_);
                    v_vec_721_ = crate::leanh::lean_ctor_get(v_res_719_, 1);
                    crate::leanh::lean_inc_ref(v_vec_721_);
                    crate::leanh::lean_dec_ref(v_res_719_);
                    v_aig_709_ = v_aig_720_;
                    v_curr_711_ = v___x_717_;
                    v_acc_712_ = v_vec_721_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftRight_go___redArg___boxed(
    mut v_inst_723_: *mut crate::leanh::LeanObject,
    mut v_inst_724_: *mut crate::leanh::LeanObject,
    mut v_w_725_: *mut crate::leanh::LeanObject,
    mut v_n_726_: *mut crate::leanh::LeanObject,
    mut v_aig_727_: *mut crate::leanh::LeanObject,
    mut v_distance_728_: *mut crate::leanh::LeanObject,
    mut v_curr_729_: *mut crate::leanh::LeanObject,
    mut v_acc_730_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_731_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_731_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftRight_go___redArg(
        v_inst_723_,
        v_inst_724_,
        v_w_725_,
        v_n_726_,
        v_aig_727_,
        v_distance_728_,
        v_curr_729_,
        v_acc_730_,
    );
    crate::leanh::lean_dec(v_w_725_);
    return v_res_731_;
}
pub unsafe fn l_Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftRight_go(
    mut v_00_u03b1_732_: *mut crate::leanh::LeanObject,
    mut v_inst_733_: *mut crate::leanh::LeanObject,
    mut v_inst_734_: *mut crate::leanh::LeanObject,
    mut v_w_735_: *mut crate::leanh::LeanObject,
    mut v_n_736_: *mut crate::leanh::LeanObject,
    mut v_aig_737_: *mut crate::leanh::LeanObject,
    mut v_distance_738_: *mut crate::leanh::LeanObject,
    mut v_curr_739_: *mut crate::leanh::LeanObject,
    mut v_acc_740_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_741_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_741_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftRight_go___redArg(
        v_inst_733_,
        v_inst_734_,
        v_w_735_,
        v_n_736_,
        v_aig_737_,
        v_distance_738_,
        v_curr_739_,
        v_acc_740_,
    );
    return v___x_741_;
}
pub unsafe fn l_Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftRight_go___boxed(
    mut v_00_u03b1_742_: *mut crate::leanh::LeanObject,
    mut v_inst_743_: *mut crate::leanh::LeanObject,
    mut v_inst_744_: *mut crate::leanh::LeanObject,
    mut v_w_745_: *mut crate::leanh::LeanObject,
    mut v_n_746_: *mut crate::leanh::LeanObject,
    mut v_aig_747_: *mut crate::leanh::LeanObject,
    mut v_distance_748_: *mut crate::leanh::LeanObject,
    mut v_curr_749_: *mut crate::leanh::LeanObject,
    mut v_acc_750_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_751_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_751_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftRight_go(
        v_00_u03b1_742_,
        v_inst_743_,
        v_inst_744_,
        v_w_745_,
        v_n_746_,
        v_aig_747_,
        v_distance_748_,
        v_curr_749_,
        v_acc_750_,
    );
    crate::leanh::lean_dec(v_w_745_);
    return v_res_751_;
}
pub unsafe fn l_Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftRight___redArg(
    mut v_inst_752_: *mut crate::leanh::LeanObject,
    mut v_inst_753_: *mut crate::leanh::LeanObject,
    mut v_w_754_: *mut crate::leanh::LeanObject,
    mut v_aig_755_: *mut crate::leanh::LeanObject,
    mut v_target_756_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_n_757_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_target_758_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_distance_759_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_760_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_761_: u8 = 0;
    v_n_757_ = crate::leanh::lean_ctor_get(v_target_756_, 0);
    crate::leanh::lean_inc(v_n_757_);
    v_target_758_ = crate::leanh::lean_ctor_get(v_target_756_, 1);
    crate::leanh::lean_inc_ref(v_target_758_);
    v_distance_759_ = crate::leanh::lean_ctor_get(v_target_756_, 2);
    crate::leanh::lean_inc_ref(v_distance_759_);
    crate::leanh::lean_dec_ref(v_target_756_);
    v___x_760_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_761_ = lean_nat_dec_eq(v_n_757_, v___x_760_);
    if v___x_761_ == 0 {
        let mut v___x_762_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_res_763_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_aig_764_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_vec_765_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_766_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_inc_ref(v_distance_759_);
        crate::leanh::lean_inc(v_n_757_);
        v___x_762_ = crate::leanh::lean_alloc_ctor(0, 4, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_762_, 0, v_n_757_);
        crate::leanh::lean_ctor_set(v___x_762_, 1, v_target_758_);
        crate::leanh::lean_ctor_set(v___x_762_, 2, v_distance_759_);
        crate::leanh::lean_ctor_set(v___x_762_, 3, v___x_760_);
        crate::leanh::lean_inc_ref(v_inst_753_);
        crate::leanh::lean_inc_ref(v_inst_752_);
        v_res_763_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftRight_twoPowShift___redArg(
            v_inst_752_,
            v_inst_753_,
            v_w_754_,
            v_aig_755_,
            v___x_762_,
        );
        crate::leanh::lean_dec_ref_known(v___x_762_, 4);
        v_aig_764_ = crate::leanh::lean_ctor_get(v_res_763_, 0);
        crate::leanh::lean_inc_ref(v_aig_764_);
        v_vec_765_ = crate::leanh::lean_ctor_get(v_res_763_, 1);
        crate::leanh::lean_inc_ref(v_vec_765_);
        crate::leanh::lean_dec_ref(v_res_763_);
        v___x_766_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftRight_go___redArg(
            v_inst_752_,
            v_inst_753_,
            v_w_754_,
            v_n_757_,
            v_aig_764_,
            v_distance_759_,
            v___x_760_,
            v_vec_765_,
        );
        return v___x_766_;
    } else {
        let mut v___x_767_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec_ref(v_distance_759_);
        crate::leanh::lean_dec(v_n_757_);
        crate::leanh::lean_dec_ref(v_inst_753_);
        crate::leanh::lean_dec_ref(v_inst_752_);
        v___x_767_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_767_, 0, v_aig_755_);
        crate::leanh::lean_ctor_set(v___x_767_, 1, v_target_758_);
        return v___x_767_;
    }
}
pub unsafe fn l_Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftRight___redArg___boxed(
    mut v_inst_768_: *mut crate::leanh::LeanObject,
    mut v_inst_769_: *mut crate::leanh::LeanObject,
    mut v_w_770_: *mut crate::leanh::LeanObject,
    mut v_aig_771_: *mut crate::leanh::LeanObject,
    mut v_target_772_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_773_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_773_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftRight___redArg(
        v_inst_768_,
        v_inst_769_,
        v_w_770_,
        v_aig_771_,
        v_target_772_,
    );
    crate::leanh::lean_dec(v_w_770_);
    return v_res_773_;
}
pub unsafe fn l_Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftRight(
    mut v_00_u03b1_774_: *mut crate::leanh::LeanObject,
    mut v_inst_775_: *mut crate::leanh::LeanObject,
    mut v_inst_776_: *mut crate::leanh::LeanObject,
    mut v_w_777_: *mut crate::leanh::LeanObject,
    mut v_aig_778_: *mut crate::leanh::LeanObject,
    mut v_target_779_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_780_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_780_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftRight___redArg(
        v_inst_775_,
        v_inst_776_,
        v_w_777_,
        v_aig_778_,
        v_target_779_,
    );
    return v___x_780_;
}
pub unsafe fn l_Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftRight___boxed(
    mut v_00_u03b1_781_: *mut crate::leanh::LeanObject,
    mut v_inst_782_: *mut crate::leanh::LeanObject,
    mut v_inst_783_: *mut crate::leanh::LeanObject,
    mut v_w_784_: *mut crate::leanh::LeanObject,
    mut v_aig_785_: *mut crate::leanh::LeanObject,
    mut v_target_786_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_787_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_787_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastShiftRight(
        v_00_u03b1_781_,
        v_inst_782_,
        v_inst_783_,
        v_w_784_,
        v_aig_785_,
        v_target_786_,
    );
    crate::leanh::lean_dec(v_w_784_);
    return v_res_787_;
}
pub unsafe fn l_Std_Tactic_BVDecide_BVExpr_bitblast_blastArithShiftRight_twoPowShift___redArg(
    mut v_inst_788_: *mut crate::leanh::LeanObject,
    mut v_inst_789_: *mut crate::leanh::LeanObject,
    mut v_w_790_: *mut crate::leanh::LeanObject,
    mut v_aig_791_: *mut crate::leanh::LeanObject,
    mut v_target_792_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_n_793_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_lhs_794_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_rhs_795_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_pow_796_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_797_: u8 = 0;
    let mut v___x_798_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_799_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_800_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_801_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_res_802_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_aig_803_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_vec_804_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_806_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_807_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_808_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_809_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_810_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_811_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_812_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_813_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_814_: u8 = 0;
    let mut v___x_815_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_816_: u8 = 0;
    let mut v___x_817_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_n_793_ = crate::leanh::lean_ctor_get(v_target_792_, 0);
                v_lhs_794_ = crate::leanh::lean_ctor_get(v_target_792_, 1);
                v_rhs_795_ = crate::leanh::lean_ctor_get(v_target_792_, 2);
                v_pow_796_ = crate::leanh::lean_ctor_get(v_target_792_, 3);
                v___x_797_ = lean_nat_dec_lt(v_pow_796_, v_n_793_);
                if v___x_797_ == 0 {
                    crate::leanh::lean_dec_ref(v_inst_789_);
                    crate::leanh::lean_dec_ref(v_inst_788_);
                    crate::leanh::lean_inc_ref(v_lhs_794_);
                    v___x_798_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_798_, 0, v_aig_791_);
                    crate::leanh::lean_ctor_set(v___x_798_, 1, v_lhs_794_);
                    return v___x_798_;
                } else {
                    v___x_799_ = crate::leanh::lean_unsigned_to_nat(2);
                    v___x_800_ = lean_nat_pow(v___x_799_, v_pow_796_);
                    crate::leanh::lean_inc_ref(v_lhs_794_);
                    v___x_801_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_801_, 0, v_lhs_794_);
                    crate::leanh::lean_ctor_set(v___x_801_, 1, v___x_800_);
                    v_res_802_ =
                        l_Std_Tactic_BVDecide_BVExpr_bitblast_blastArithShiftRightConst___redArg(
                            v_w_790_, v_aig_791_, v___x_801_,
                        );
                    v_aig_803_ = crate::leanh::lean_ctor_get(v_res_802_, 0);
                    crate::leanh::lean_inc_ref(v_aig_803_);
                    v_vec_804_ = crate::leanh::lean_ctor_get(v_res_802_, 1);
                    crate::leanh::lean_inc_ref(v_vec_804_);
                    crate::leanh::lean_dec_ref(v_res_802_);
                    v_ref_809_ = lean_array_fget_borrowed(v_rhs_795_, v_pow_796_);
                    v___x_810_ = crate::leanh::lean_unsigned_to_nat(1);
                    v___x_811_ = lean_nat_shiftr(v_ref_809_, v___x_810_);
                    v___x_812_ = lean_nat_land(v___x_810_, v_ref_809_);
                    v___x_813_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___x_814_ = lean_nat_dec_eq(v___x_812_, v___x_813_);
                    crate::leanh::lean_dec(v___x_812_);
                    if v___x_814_ == 0 {
                        v___x_815_ = crate::leanh::lean_alloc_ctor(0, 1, (1) as u32);
                        crate::leanh::lean_ctor_set(v___x_815_, 0, v___x_811_);
                        crate::leanh::lean_ctor_set_uint8(
                            v___x_815_,
                            (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                            v___x_797_,
                        );
                        v___y_806_ = v___x_815_;
                        state = 1;
                        continue;
                    } else {
                        v___x_816_ = 0;
                        v___x_817_ = crate::leanh::lean_alloc_ctor(0, 1, (1) as u32);
                        crate::leanh::lean_ctor_set(v___x_817_, 0, v___x_811_);
                        crate::leanh::lean_ctor_set_uint8(
                            v___x_817_,
                            (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                            v___x_816_,
                        );
                        v___y_806_ = v___x_817_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                crate::leanh::lean_inc_ref(v_lhs_794_);
                v___x_807_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_807_, 0, v___y_806_);
                crate::leanh::lean_ctor_set(v___x_807_, 1, v_vec_804_);
                crate::leanh::lean_ctor_set(v___x_807_, 2, v_lhs_794_);
                v___x_808_ = l_Std_Sat_AIG_RefVec_ite___redArg(
                    v_inst_788_,
                    v_inst_789_,
                    v_w_790_,
                    v_aig_803_,
                    v___x_807_,
                );
                return v___x_808_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Tactic_BVDecide_BVExpr_bitblast_blastArithShiftRight_twoPowShift___redArg___boxed(
    mut v_inst_818_: *mut crate::leanh::LeanObject,
    mut v_inst_819_: *mut crate::leanh::LeanObject,
    mut v_w_820_: *mut crate::leanh::LeanObject,
    mut v_aig_821_: *mut crate::leanh::LeanObject,
    mut v_target_822_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_823_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_823_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastArithShiftRight_twoPowShift___redArg(
        v_inst_818_,
        v_inst_819_,
        v_w_820_,
        v_aig_821_,
        v_target_822_,
    );
    crate::leanh::lean_dec_ref(v_target_822_);
    crate::leanh::lean_dec(v_w_820_);
    return v_res_823_;
}
pub unsafe fn l_Std_Tactic_BVDecide_BVExpr_bitblast_blastArithShiftRight_twoPowShift(
    mut v_00_u03b1_824_: *mut crate::leanh::LeanObject,
    mut v_inst_825_: *mut crate::leanh::LeanObject,
    mut v_inst_826_: *mut crate::leanh::LeanObject,
    mut v_w_827_: *mut crate::leanh::LeanObject,
    mut v_aig_828_: *mut crate::leanh::LeanObject,
    mut v_target_829_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_830_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_830_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastArithShiftRight_twoPowShift___redArg(
        v_inst_825_,
        v_inst_826_,
        v_w_827_,
        v_aig_828_,
        v_target_829_,
    );
    return v___x_830_;
}
pub unsafe fn l_Std_Tactic_BVDecide_BVExpr_bitblast_blastArithShiftRight_twoPowShift___boxed(
    mut v_00_u03b1_831_: *mut crate::leanh::LeanObject,
    mut v_inst_832_: *mut crate::leanh::LeanObject,
    mut v_inst_833_: *mut crate::leanh::LeanObject,
    mut v_w_834_: *mut crate::leanh::LeanObject,
    mut v_aig_835_: *mut crate::leanh::LeanObject,
    mut v_target_836_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_837_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_837_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastArithShiftRight_twoPowShift(
        v_00_u03b1_831_,
        v_inst_832_,
        v_inst_833_,
        v_w_834_,
        v_aig_835_,
        v_target_836_,
    );
    crate::leanh::lean_dec_ref(v_target_836_);
    crate::leanh::lean_dec(v_w_834_);
    return v_res_837_;
}
pub unsafe fn l_Std_Tactic_BVDecide_BVExpr_bitblast_blastArithShiftRight_go___redArg(
    mut v_inst_838_: *mut crate::leanh::LeanObject,
    mut v_inst_839_: *mut crate::leanh::LeanObject,
    mut v_w_840_: *mut crate::leanh::LeanObject,
    mut v_n_841_: *mut crate::leanh::LeanObject,
    mut v_aig_842_: *mut crate::leanh::LeanObject,
    mut v_distance_843_: *mut crate::leanh::LeanObject,
    mut v_curr_844_: *mut crate::leanh::LeanObject,
    mut v_acc_845_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_846_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_847_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_848_: u8 = 0;
    let mut v___x_849_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_850_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_851_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_res_852_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_aig_853_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_vec_854_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_846_ = crate::leanh::lean_unsigned_to_nat(1);
                v___x_847_ = lean_nat_sub(v_n_841_, v___x_846_);
                v___x_848_ = lean_nat_dec_lt(v_curr_844_, v___x_847_);
                crate::leanh::lean_dec(v___x_847_);
                if v___x_848_ == 0 {
                    crate::leanh::lean_dec(v_curr_844_);
                    crate::leanh::lean_dec_ref(v_distance_843_);
                    crate::leanh::lean_dec(v_n_841_);
                    crate::leanh::lean_dec_ref(v_inst_839_);
                    crate::leanh::lean_dec_ref(v_inst_838_);
                    v___x_849_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_849_, 0, v_aig_842_);
                    crate::leanh::lean_ctor_set(v___x_849_, 1, v_acc_845_);
                    return v___x_849_;
                } else {
                    v___x_850_ = lean_nat_add(v_curr_844_, v___x_846_);
                    crate::leanh::lean_dec(v_curr_844_);
                    crate::leanh::lean_inc(v___x_850_);
                    crate::leanh::lean_inc_ref(v_distance_843_);
                    crate::leanh::lean_inc(v_n_841_);
                    v___x_851_ = crate::leanh::lean_alloc_ctor(0, 4, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_851_, 0, v_n_841_);
                    crate::leanh::lean_ctor_set(v___x_851_, 1, v_acc_845_);
                    crate::leanh::lean_ctor_set(v___x_851_, 2, v_distance_843_);
                    crate::leanh::lean_ctor_set(v___x_851_, 3, v___x_850_);
                    crate::leanh::lean_inc_ref(v_inst_839_);
                    crate::leanh::lean_inc_ref(v_inst_838_);
                    v_res_852_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastArithShiftRight_twoPowShift___redArg(v_inst_838_, v_inst_839_, v_w_840_, v_aig_842_, v___x_851_);
                    crate::leanh::lean_dec_ref_known(v___x_851_, 4);
                    v_aig_853_ = crate::leanh::lean_ctor_get(v_res_852_, 0);
                    crate::leanh::lean_inc_ref(v_aig_853_);
                    v_vec_854_ = crate::leanh::lean_ctor_get(v_res_852_, 1);
                    crate::leanh::lean_inc_ref(v_vec_854_);
                    crate::leanh::lean_dec_ref(v_res_852_);
                    v_aig_842_ = v_aig_853_;
                    v_curr_844_ = v___x_850_;
                    v_acc_845_ = v_vec_854_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Tactic_BVDecide_BVExpr_bitblast_blastArithShiftRight_go___redArg___boxed(
    mut v_inst_856_: *mut crate::leanh::LeanObject,
    mut v_inst_857_: *mut crate::leanh::LeanObject,
    mut v_w_858_: *mut crate::leanh::LeanObject,
    mut v_n_859_: *mut crate::leanh::LeanObject,
    mut v_aig_860_: *mut crate::leanh::LeanObject,
    mut v_distance_861_: *mut crate::leanh::LeanObject,
    mut v_curr_862_: *mut crate::leanh::LeanObject,
    mut v_acc_863_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_864_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_864_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastArithShiftRight_go___redArg(
        v_inst_856_,
        v_inst_857_,
        v_w_858_,
        v_n_859_,
        v_aig_860_,
        v_distance_861_,
        v_curr_862_,
        v_acc_863_,
    );
    crate::leanh::lean_dec(v_w_858_);
    return v_res_864_;
}
pub unsafe fn l_Std_Tactic_BVDecide_BVExpr_bitblast_blastArithShiftRight_go(
    mut v_00_u03b1_865_: *mut crate::leanh::LeanObject,
    mut v_inst_866_: *mut crate::leanh::LeanObject,
    mut v_inst_867_: *mut crate::leanh::LeanObject,
    mut v_w_868_: *mut crate::leanh::LeanObject,
    mut v_n_869_: *mut crate::leanh::LeanObject,
    mut v_aig_870_: *mut crate::leanh::LeanObject,
    mut v_distance_871_: *mut crate::leanh::LeanObject,
    mut v_curr_872_: *mut crate::leanh::LeanObject,
    mut v_acc_873_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_874_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_874_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastArithShiftRight_go___redArg(
        v_inst_866_,
        v_inst_867_,
        v_w_868_,
        v_n_869_,
        v_aig_870_,
        v_distance_871_,
        v_curr_872_,
        v_acc_873_,
    );
    return v___x_874_;
}
pub unsafe fn l_Std_Tactic_BVDecide_BVExpr_bitblast_blastArithShiftRight_go___boxed(
    mut v_00_u03b1_875_: *mut crate::leanh::LeanObject,
    mut v_inst_876_: *mut crate::leanh::LeanObject,
    mut v_inst_877_: *mut crate::leanh::LeanObject,
    mut v_w_878_: *mut crate::leanh::LeanObject,
    mut v_n_879_: *mut crate::leanh::LeanObject,
    mut v_aig_880_: *mut crate::leanh::LeanObject,
    mut v_distance_881_: *mut crate::leanh::LeanObject,
    mut v_curr_882_: *mut crate::leanh::LeanObject,
    mut v_acc_883_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_884_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_884_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastArithShiftRight_go(
        v_00_u03b1_875_,
        v_inst_876_,
        v_inst_877_,
        v_w_878_,
        v_n_879_,
        v_aig_880_,
        v_distance_881_,
        v_curr_882_,
        v_acc_883_,
    );
    crate::leanh::lean_dec(v_w_878_);
    return v_res_884_;
}
pub unsafe fn l_Std_Tactic_BVDecide_BVExpr_bitblast_blastArithShiftRight___redArg(
    mut v_inst_885_: *mut crate::leanh::LeanObject,
    mut v_inst_886_: *mut crate::leanh::LeanObject,
    mut v_w_887_: *mut crate::leanh::LeanObject,
    mut v_aig_888_: *mut crate::leanh::LeanObject,
    mut v_target_889_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_n_890_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_target_891_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_distance_892_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_893_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_894_: u8 = 0;
    v_n_890_ = crate::leanh::lean_ctor_get(v_target_889_, 0);
    crate::leanh::lean_inc(v_n_890_);
    v_target_891_ = crate::leanh::lean_ctor_get(v_target_889_, 1);
    crate::leanh::lean_inc_ref(v_target_891_);
    v_distance_892_ = crate::leanh::lean_ctor_get(v_target_889_, 2);
    crate::leanh::lean_inc_ref(v_distance_892_);
    crate::leanh::lean_dec_ref(v_target_889_);
    v___x_893_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_894_ = lean_nat_dec_eq(v_n_890_, v___x_893_);
    if v___x_894_ == 0 {
        let mut v___x_895_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_res_896_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_aig_897_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_vec_898_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_899_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_inc_ref(v_distance_892_);
        crate::leanh::lean_inc(v_n_890_);
        v___x_895_ = crate::leanh::lean_alloc_ctor(0, 4, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_895_, 0, v_n_890_);
        crate::leanh::lean_ctor_set(v___x_895_, 1, v_target_891_);
        crate::leanh::lean_ctor_set(v___x_895_, 2, v_distance_892_);
        crate::leanh::lean_ctor_set(v___x_895_, 3, v___x_893_);
        crate::leanh::lean_inc_ref(v_inst_886_);
        crate::leanh::lean_inc_ref(v_inst_885_);
        v_res_896_ =
            l_Std_Tactic_BVDecide_BVExpr_bitblast_blastArithShiftRight_twoPowShift___redArg(
                v_inst_885_,
                v_inst_886_,
                v_w_887_,
                v_aig_888_,
                v___x_895_,
            );
        crate::leanh::lean_dec_ref_known(v___x_895_, 4);
        v_aig_897_ = crate::leanh::lean_ctor_get(v_res_896_, 0);
        crate::leanh::lean_inc_ref(v_aig_897_);
        v_vec_898_ = crate::leanh::lean_ctor_get(v_res_896_, 1);
        crate::leanh::lean_inc_ref(v_vec_898_);
        crate::leanh::lean_dec_ref(v_res_896_);
        v___x_899_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastArithShiftRight_go___redArg(
            v_inst_885_,
            v_inst_886_,
            v_w_887_,
            v_n_890_,
            v_aig_897_,
            v_distance_892_,
            v___x_893_,
            v_vec_898_,
        );
        return v___x_899_;
    } else {
        let mut v___x_900_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec_ref(v_distance_892_);
        crate::leanh::lean_dec(v_n_890_);
        crate::leanh::lean_dec_ref(v_inst_886_);
        crate::leanh::lean_dec_ref(v_inst_885_);
        v___x_900_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_900_, 0, v_aig_888_);
        crate::leanh::lean_ctor_set(v___x_900_, 1, v_target_891_);
        return v___x_900_;
    }
}
pub unsafe fn l_Std_Tactic_BVDecide_BVExpr_bitblast_blastArithShiftRight___redArg___boxed(
    mut v_inst_901_: *mut crate::leanh::LeanObject,
    mut v_inst_902_: *mut crate::leanh::LeanObject,
    mut v_w_903_: *mut crate::leanh::LeanObject,
    mut v_aig_904_: *mut crate::leanh::LeanObject,
    mut v_target_905_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_906_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_906_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastArithShiftRight___redArg(
        v_inst_901_,
        v_inst_902_,
        v_w_903_,
        v_aig_904_,
        v_target_905_,
    );
    crate::leanh::lean_dec(v_w_903_);
    return v_res_906_;
}
pub unsafe fn l_Std_Tactic_BVDecide_BVExpr_bitblast_blastArithShiftRight(
    mut v_00_u03b1_907_: *mut crate::leanh::LeanObject,
    mut v_inst_908_: *mut crate::leanh::LeanObject,
    mut v_inst_909_: *mut crate::leanh::LeanObject,
    mut v_w_910_: *mut crate::leanh::LeanObject,
    mut v_aig_911_: *mut crate::leanh::LeanObject,
    mut v_target_912_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_913_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_913_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastArithShiftRight___redArg(
        v_inst_908_,
        v_inst_909_,
        v_w_910_,
        v_aig_911_,
        v_target_912_,
    );
    return v___x_913_;
}
pub unsafe fn l_Std_Tactic_BVDecide_BVExpr_bitblast_blastArithShiftRight___boxed(
    mut v_00_u03b1_914_: *mut crate::leanh::LeanObject,
    mut v_inst_915_: *mut crate::leanh::LeanObject,
    mut v_inst_916_: *mut crate::leanh::LeanObject,
    mut v_w_917_: *mut crate::leanh::LeanObject,
    mut v_aig_918_: *mut crate::leanh::LeanObject,
    mut v_target_919_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_920_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_920_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastArithShiftRight(
        v_00_u03b1_914_,
        v_inst_915_,
        v_inst_916_,
        v_w_917_,
        v_aig_918_,
        v_target_919_,
    );
    crate::leanh::lean_dec(v_w_917_);
    return v_res_920_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Operations_ShiftRight(
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
pub unsafe fn meta_initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Operations_ShiftRight(
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
pub unsafe fn initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Operations_ShiftRight(
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
    res = runtime_initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Operations_ShiftRight(
        builtin,
    );
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Operations_ShiftRight(
        builtin,
    );
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Operations_ShiftRight(
        builtin,
    );
}
