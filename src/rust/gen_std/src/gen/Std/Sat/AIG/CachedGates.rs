// Lean compiler output
// Module: Std.Sat.AIG.CachedGates
// Imports: Std.Sat.AIG.CachedLemmas
use crate::r#gen::Std::Sat::AIG::Cached::l_Std_Sat_AIG_mkGateCached___redArg;
use crate::r#gen::Std::Sat::AIG::CachedLemmas::{
    initialize_Std_Sat_AIG_CachedLemmas, runtime_initialize_Std_Sat_AIG_CachedLemmas,
};
pub unsafe fn l_Std_Sat_AIG_mkNotCached___redArg(
    mut v_aig_483_: *mut leanh::LeanObject,
    mut v_gate_484_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_invert_485_: u8 = 0;
    let mut v_gate_486_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_488_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_489_: u8 = 0;
    let mut v___x_490_: u8 = 0;
    let mut v___x_492_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_493_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_494_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_495_: u8 = 0;
    let mut v_gate_496_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_498_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_499_: u8 = 0;
    let mut v___x_500_: u8 = 0;
    let mut v___x_502_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_503_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_504_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_505_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_invert_485_ = leanh::lean_ctor_get_uint8(
                    v_gate_484_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                );
                if v_invert_485_ == 0 {
                    v_gate_486_ = leanh::lean_ctor_get(v_gate_484_, 0);
                    v_isSharedCheck_495_ = (!leanh::lean_is_exclusive(v_gate_484_)) as u8;
                    if v_isSharedCheck_495_ == 0 {
                        v___x_488_ = v_gate_484_;
                        v_isShared_489_ = v_isSharedCheck_495_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_gate_486_);
                        leanh::lean_dec(v_gate_484_);
                        v___x_488_ = leanh::lean_box(0);
                        v_isShared_489_ = v_isSharedCheck_495_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_gate_496_ = leanh::lean_ctor_get(v_gate_484_, 0);
                    v_isSharedCheck_505_ = (!leanh::lean_is_exclusive(v_gate_484_)) as u8;
                    if v_isSharedCheck_505_ == 0 {
                        v___x_498_ = v_gate_484_;
                        v_isShared_499_ = v_isSharedCheck_505_;
                        state = 3;
                        continue;
                    } else {
                        leanh::lean_inc(v_gate_496_);
                        leanh::lean_dec(v_gate_484_);
                        v___x_498_ = leanh::lean_box(0);
                        v_isShared_499_ = v_isSharedCheck_505_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v___x_490_ = 1;
                if v_isShared_489_ == 0 {
                    v___x_492_ = v___x_488_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_494_ = leanh::lean_alloc_ctor(0, 1, (1) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_494_, 0, v_gate_486_);
                    v___x_492_ = v_reuseFailAlloc_494_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                leanh::lean_ctor_set_uint8(
                    v___x_492_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                    v___x_490_,
                );
                v___x_493_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_493_, 0, v_aig_483_);
                leanh::lean_ctor_set(v___x_493_, 1, v___x_492_);
                return v___x_493_;
            }
            3 => {
                v___x_500_ = 0;
                if v_isShared_499_ == 0 {
                    v___x_502_ = v___x_498_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_504_ = leanh::lean_alloc_ctor(0, 1, (1) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_504_, 0, v_gate_496_);
                    v___x_502_ = v_reuseFailAlloc_504_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                leanh::lean_ctor_set_uint8(
                    v___x_502_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                    v___x_500_,
                );
                v___x_503_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_503_, 0, v_aig_483_);
                leanh::lean_ctor_set(v___x_503_, 1, v___x_502_);
                return v___x_503_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Sat_AIG_mkNotCached(
    mut v_00_u03b1_506_: *mut leanh::LeanObject,
    mut v_inst_507_: *mut leanh::LeanObject,
    mut v_inst_508_: *mut leanh::LeanObject,
    mut v_aig_509_: *mut leanh::LeanObject,
    mut v_gate_510_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_invert_511_: u8 = 0;
    let mut v_gate_512_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_514_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_515_: u8 = 0;
    let mut v___x_516_: u8 = 0;
    let mut v___x_518_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_519_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_520_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_521_: u8 = 0;
    let mut v_gate_522_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_524_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_525_: u8 = 0;
    let mut v___x_526_: u8 = 0;
    let mut v___x_528_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_529_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_530_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_531_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_invert_511_ = leanh::lean_ctor_get_uint8(
                    v_gate_510_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                );
                if v_invert_511_ == 0 {
                    v_gate_512_ = leanh::lean_ctor_get(v_gate_510_, 0);
                    v_isSharedCheck_521_ = (!leanh::lean_is_exclusive(v_gate_510_)) as u8;
                    if v_isSharedCheck_521_ == 0 {
                        v___x_514_ = v_gate_510_;
                        v_isShared_515_ = v_isSharedCheck_521_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_gate_512_);
                        leanh::lean_dec(v_gate_510_);
                        v___x_514_ = leanh::lean_box(0);
                        v_isShared_515_ = v_isSharedCheck_521_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_gate_522_ = leanh::lean_ctor_get(v_gate_510_, 0);
                    v_isSharedCheck_531_ = (!leanh::lean_is_exclusive(v_gate_510_)) as u8;
                    if v_isSharedCheck_531_ == 0 {
                        v___x_524_ = v_gate_510_;
                        v_isShared_525_ = v_isSharedCheck_531_;
                        state = 3;
                        continue;
                    } else {
                        leanh::lean_inc(v_gate_522_);
                        leanh::lean_dec(v_gate_510_);
                        v___x_524_ = leanh::lean_box(0);
                        v_isShared_525_ = v_isSharedCheck_531_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v___x_516_ = 1;
                if v_isShared_515_ == 0 {
                    v___x_518_ = v___x_514_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_520_ = leanh::lean_alloc_ctor(0, 1, (1) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_520_, 0, v_gate_512_);
                    v___x_518_ = v_reuseFailAlloc_520_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                leanh::lean_ctor_set_uint8(
                    v___x_518_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                    v___x_516_,
                );
                v___x_519_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_519_, 0, v_aig_509_);
                leanh::lean_ctor_set(v___x_519_, 1, v___x_518_);
                return v___x_519_;
            }
            3 => {
                v___x_526_ = 0;
                if v_isShared_525_ == 0 {
                    v___x_528_ = v___x_524_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_530_ = leanh::lean_alloc_ctor(0, 1, (1) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_530_, 0, v_gate_522_);
                    v___x_528_ = v_reuseFailAlloc_530_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                leanh::lean_ctor_set_uint8(
                    v___x_528_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                    v___x_526_,
                );
                v___x_529_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_529_, 0, v_aig_509_);
                leanh::lean_ctor_set(v___x_529_, 1, v___x_528_);
                return v___x_529_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Sat_AIG_mkNotCached___boxed(
    mut v_00_u03b1_532_: *mut leanh::LeanObject,
    mut v_inst_533_: *mut leanh::LeanObject,
    mut v_inst_534_: *mut leanh::LeanObject,
    mut v_aig_535_: *mut leanh::LeanObject,
    mut v_gate_536_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_537_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_537_ = l_Std_Sat_AIG_mkNotCached(
        v_00_u03b1_532_,
        v_inst_533_,
        v_inst_534_,
        v_aig_535_,
        v_gate_536_,
    );
    leanh::lean_dec_ref(v_inst_534_);
    leanh::lean_dec_ref(v_inst_533_);
    return v_res_537_;
}
pub unsafe fn l_Std_Sat_AIG_mkAndCached___redArg(
    mut v_inst_538_: *mut leanh::LeanObject,
    mut v_inst_539_: *mut leanh::LeanObject,
    mut v_aig_540_: *mut leanh::LeanObject,
    mut v_input_541_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_542_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_542_ =
        l_Std_Sat_AIG_mkGateCached___redArg(v_inst_538_, v_inst_539_, v_aig_540_, v_input_541_);
    return v___x_542_;
}
pub unsafe fn l_Std_Sat_AIG_mkAndCached(
    mut v_00_u03b1_543_: *mut leanh::LeanObject,
    mut v_inst_544_: *mut leanh::LeanObject,
    mut v_inst_545_: *mut leanh::LeanObject,
    mut v_aig_546_: *mut leanh::LeanObject,
    mut v_input_547_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_548_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_548_ =
        l_Std_Sat_AIG_mkGateCached___redArg(v_inst_544_, v_inst_545_, v_aig_546_, v_input_547_);
    return v___x_548_;
}
pub unsafe fn l_Std_Sat_AIG_mkOrCached___redArg(
    mut v_inst_549_: *mut leanh::LeanObject,
    mut v_inst_550_: *mut leanh::LeanObject,
    mut v_aig_551_: *mut leanh::LeanObject,
    mut v_input_552_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___y_554_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_res_555_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_556_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_invert_557_: u8 = 0;
    let mut v_aig_558_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_560_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_561_: u8 = 0;
    let mut v_gate_562_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_564_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_565_: u8 = 0;
    let mut v___x_566_: u8 = 0;
    let mut v___x_568_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_570_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_571_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_572_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_573_: u8 = 0;
    let mut v_isSharedCheck_574_: u8 = 0;
    let mut v_unused_575_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_aig_576_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_578_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_579_: u8 = 0;
    let mut v_gate_580_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_582_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_583_: u8 = 0;
    let mut v___x_584_: u8 = 0;
    let mut v___x_586_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_588_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_589_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_590_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_591_: u8 = 0;
    let mut v_isSharedCheck_592_: u8 = 0;
    let mut v_unused_593_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_lhs_594_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_rhs_595_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_597_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_598_: u8 = 0;
    let mut v___y_600_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_invert_601_: u8 = 0;
    let mut v_gate_602_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_604_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_605_: u8 = 0;
    let mut v___x_606_: u8 = 0;
    let mut v___x_608_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_610_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_611_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_612_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_613_: u8 = 0;
    let mut v_gate_614_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_616_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_617_: u8 = 0;
    let mut v___x_618_: u8 = 0;
    let mut v___x_620_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_622_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_623_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_624_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_625_: u8 = 0;
    let mut v_invert_626_: u8 = 0;
    let mut v_gate_627_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_629_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_630_: u8 = 0;
    let mut v___x_631_: u8 = 0;
    let mut v___x_633_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_634_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_635_: u8 = 0;
    let mut v_gate_636_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_638_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_639_: u8 = 0;
    let mut v___x_640_: u8 = 0;
    let mut v___x_642_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_643_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_644_: u8 = 0;
    let mut v_isSharedCheck_645_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_lhs_594_ = leanh::lean_ctor_get(v_input_552_, 0);
                v_rhs_595_ = leanh::lean_ctor_get(v_input_552_, 1);
                v_isSharedCheck_645_ = (!leanh::lean_is_exclusive(v_input_552_)) as u8;
                if v_isSharedCheck_645_ == 0 {
                    v___x_597_ = v_input_552_;
                    v_isShared_598_ = v_isSharedCheck_645_;
                    state = 10;
                    continue;
                } else {
                    leanh::lean_inc(v_rhs_595_);
                    leanh::lean_inc(v_lhs_594_);
                    leanh::lean_dec(v_input_552_);
                    v___x_597_ = leanh::lean_box(0);
                    v_isShared_598_ = v_isSharedCheck_645_;
                    state = 10;
                    continue;
                }
            }
            1 => {
                v_res_555_ = l_Std_Sat_AIG_mkGateCached___redArg(
                    v_inst_549_,
                    v_inst_550_,
                    v_aig_551_,
                    v___y_554_,
                );
                v_ref_556_ = leanh::lean_ctor_get(v_res_555_, 1);
                leanh::lean_inc_ref(v_ref_556_);
                v_invert_557_ = leanh::lean_ctor_get_uint8(
                    v_ref_556_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                );
                if v_invert_557_ == 0 {
                    v_aig_558_ = leanh::lean_ctor_get(v_res_555_, 0);
                    v_isSharedCheck_574_ = (!leanh::lean_is_exclusive(v_res_555_)) as u8;
                    if v_isSharedCheck_574_ == 0 {
                        v_unused_575_ = leanh::lean_ctor_get(v_res_555_, 1);
                        leanh::lean_dec(v_unused_575_);
                        v___x_560_ = v_res_555_;
                        v_isShared_561_ = v_isSharedCheck_574_;
                        state = 2;
                        continue;
                    } else {
                        leanh::lean_inc(v_aig_558_);
                        leanh::lean_dec(v_res_555_);
                        v___x_560_ = leanh::lean_box(0);
                        v_isShared_561_ = v_isSharedCheck_574_;
                        state = 2;
                        continue;
                    }
                } else {
                    v_aig_576_ = leanh::lean_ctor_get(v_res_555_, 0);
                    v_isSharedCheck_592_ = (!leanh::lean_is_exclusive(v_res_555_)) as u8;
                    if v_isSharedCheck_592_ == 0 {
                        v_unused_593_ = leanh::lean_ctor_get(v_res_555_, 1);
                        leanh::lean_dec(v_unused_593_);
                        v___x_578_ = v_res_555_;
                        v_isShared_579_ = v_isSharedCheck_592_;
                        state = 6;
                        continue;
                    } else {
                        leanh::lean_inc(v_aig_576_);
                        leanh::lean_dec(v_res_555_);
                        v___x_578_ = leanh::lean_box(0);
                        v_isShared_579_ = v_isSharedCheck_592_;
                        state = 6;
                        continue;
                    }
                }
            }
            2 => {
                v_gate_562_ = leanh::lean_ctor_get(v_ref_556_, 0);
                v_isSharedCheck_573_ = (!leanh::lean_is_exclusive(v_ref_556_)) as u8;
                if v_isSharedCheck_573_ == 0 {
                    v___x_564_ = v_ref_556_;
                    v_isShared_565_ = v_isSharedCheck_573_;
                    state = 3;
                    continue;
                } else {
                    leanh::lean_inc(v_gate_562_);
                    leanh::lean_dec(v_ref_556_);
                    v___x_564_ = leanh::lean_box(0);
                    v_isShared_565_ = v_isSharedCheck_573_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_566_ = 1;
                if v_isShared_565_ == 0 {
                    v___x_568_ = v___x_564_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_572_ = leanh::lean_alloc_ctor(0, 1, (1) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_572_, 0, v_gate_562_);
                    v___x_568_ = v_reuseFailAlloc_572_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                leanh::lean_ctor_set_uint8(
                    v___x_568_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                    v___x_566_,
                );
                if v_isShared_561_ == 0 {
                    leanh::lean_ctor_set(v___x_560_, 1, v___x_568_);
                    v___x_570_ = v___x_560_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_571_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_571_, 0, v_aig_558_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_571_, 1, v___x_568_);
                    v___x_570_ = v_reuseFailAlloc_571_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_570_;
            }
            6 => {
                v_gate_580_ = leanh::lean_ctor_get(v_ref_556_, 0);
                v_isSharedCheck_591_ = (!leanh::lean_is_exclusive(v_ref_556_)) as u8;
                if v_isSharedCheck_591_ == 0 {
                    v___x_582_ = v_ref_556_;
                    v_isShared_583_ = v_isSharedCheck_591_;
                    state = 7;
                    continue;
                } else {
                    leanh::lean_inc(v_gate_580_);
                    leanh::lean_dec(v_ref_556_);
                    v___x_582_ = leanh::lean_box(0);
                    v_isShared_583_ = v_isSharedCheck_591_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                v___x_584_ = 0;
                if v_isShared_583_ == 0 {
                    v___x_586_ = v___x_582_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_590_ = leanh::lean_alloc_ctor(0, 1, (1) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_590_, 0, v_gate_580_);
                    v___x_586_ = v_reuseFailAlloc_590_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                leanh::lean_ctor_set_uint8(
                    v___x_586_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                    v___x_584_,
                );
                if v_isShared_579_ == 0 {
                    leanh::lean_ctor_set(v___x_578_, 1, v___x_586_);
                    v___x_588_ = v___x_578_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_589_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_589_, 0, v_aig_576_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_589_, 1, v___x_586_);
                    v___x_588_ = v_reuseFailAlloc_589_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                return v___x_588_;
            }
            10 => {
                v_invert_626_ = leanh::lean_ctor_get_uint8(
                    v_lhs_594_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                );
                if v_invert_626_ == 0 {
                    v_gate_627_ = leanh::lean_ctor_get(v_lhs_594_, 0);
                    v_isSharedCheck_635_ = (!leanh::lean_is_exclusive(v_lhs_594_)) as u8;
                    if v_isSharedCheck_635_ == 0 {
                        v___x_629_ = v_lhs_594_;
                        v_isShared_630_ = v_isSharedCheck_635_;
                        state = 18;
                        continue;
                    } else {
                        leanh::lean_inc(v_gate_627_);
                        leanh::lean_dec(v_lhs_594_);
                        v___x_629_ = leanh::lean_box(0);
                        v_isShared_630_ = v_isSharedCheck_635_;
                        state = 18;
                        continue;
                    }
                } else {
                    v_gate_636_ = leanh::lean_ctor_get(v_lhs_594_, 0);
                    v_isSharedCheck_644_ = (!leanh::lean_is_exclusive(v_lhs_594_)) as u8;
                    if v_isSharedCheck_644_ == 0 {
                        v___x_638_ = v_lhs_594_;
                        v_isShared_639_ = v_isSharedCheck_644_;
                        state = 20;
                        continue;
                    } else {
                        leanh::lean_inc(v_gate_636_);
                        leanh::lean_dec(v_lhs_594_);
                        v___x_638_ = leanh::lean_box(0);
                        v_isShared_639_ = v_isSharedCheck_644_;
                        state = 20;
                        continue;
                    }
                }
            }
            11 => {
                v_invert_601_ = leanh::lean_ctor_get_uint8(
                    v_rhs_595_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                );
                if v_invert_601_ == 0 {
                    v_gate_602_ = leanh::lean_ctor_get(v_rhs_595_, 0);
                    v_isSharedCheck_613_ = (!leanh::lean_is_exclusive(v_rhs_595_)) as u8;
                    if v_isSharedCheck_613_ == 0 {
                        v___x_604_ = v_rhs_595_;
                        v_isShared_605_ = v_isSharedCheck_613_;
                        state = 12;
                        continue;
                    } else {
                        leanh::lean_inc(v_gate_602_);
                        leanh::lean_dec(v_rhs_595_);
                        v___x_604_ = leanh::lean_box(0);
                        v_isShared_605_ = v_isSharedCheck_613_;
                        state = 12;
                        continue;
                    }
                } else {
                    v_gate_614_ = leanh::lean_ctor_get(v_rhs_595_, 0);
                    v_isSharedCheck_625_ = (!leanh::lean_is_exclusive(v_rhs_595_)) as u8;
                    if v_isSharedCheck_625_ == 0 {
                        v___x_616_ = v_rhs_595_;
                        v_isShared_617_ = v_isSharedCheck_625_;
                        state = 15;
                        continue;
                    } else {
                        leanh::lean_inc(v_gate_614_);
                        leanh::lean_dec(v_rhs_595_);
                        v___x_616_ = leanh::lean_box(0);
                        v_isShared_617_ = v_isSharedCheck_625_;
                        state = 15;
                        continue;
                    }
                }
            }
            12 => {
                v___x_606_ = 1;
                if v_isShared_605_ == 0 {
                    v___x_608_ = v___x_604_;
                    state = 13;
                    continue;
                } else {
                    v_reuseFailAlloc_612_ = leanh::lean_alloc_ctor(0, 1, (1) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_612_, 0, v_gate_602_);
                    v___x_608_ = v_reuseFailAlloc_612_;
                    state = 13;
                    continue;
                }
            }
            13 => {
                leanh::lean_ctor_set_uint8(
                    v___x_608_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                    v___x_606_,
                );
                if v_isShared_598_ == 0 {
                    leanh::lean_ctor_set(v___x_597_, 1, v___x_608_);
                    leanh::lean_ctor_set(v___x_597_, 0, v___y_600_);
                    v___x_610_ = v___x_597_;
                    state = 14;
                    continue;
                } else {
                    v_reuseFailAlloc_611_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_611_, 0, v___y_600_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_611_, 1, v___x_608_);
                    v___x_610_ = v_reuseFailAlloc_611_;
                    state = 14;
                    continue;
                }
            }
            14 => {
                v___y_554_ = v___x_610_;
                state = 1;
                continue;
            }
            15 => {
                v___x_618_ = 0;
                if v_isShared_617_ == 0 {
                    v___x_620_ = v___x_616_;
                    state = 16;
                    continue;
                } else {
                    v_reuseFailAlloc_624_ = leanh::lean_alloc_ctor(0, 1, (1) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_624_, 0, v_gate_614_);
                    v___x_620_ = v_reuseFailAlloc_624_;
                    state = 16;
                    continue;
                }
            }
            16 => {
                leanh::lean_ctor_set_uint8(
                    v___x_620_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                    v___x_618_,
                );
                if v_isShared_598_ == 0 {
                    leanh::lean_ctor_set(v___x_597_, 1, v___x_620_);
                    leanh::lean_ctor_set(v___x_597_, 0, v___y_600_);
                    v___x_622_ = v___x_597_;
                    state = 17;
                    continue;
                } else {
                    v_reuseFailAlloc_623_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_623_, 0, v___y_600_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_623_, 1, v___x_620_);
                    v___x_622_ = v_reuseFailAlloc_623_;
                    state = 17;
                    continue;
                }
            }
            17 => {
                v___y_554_ = v___x_622_;
                state = 1;
                continue;
            }
            18 => {
                v___x_631_ = 1;
                if v_isShared_630_ == 0 {
                    v___x_633_ = v___x_629_;
                    state = 19;
                    continue;
                } else {
                    v_reuseFailAlloc_634_ = leanh::lean_alloc_ctor(0, 1, (1) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_634_, 0, v_gate_627_);
                    v___x_633_ = v_reuseFailAlloc_634_;
                    state = 19;
                    continue;
                }
            }
            19 => {
                leanh::lean_ctor_set_uint8(
                    v___x_633_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                    v___x_631_,
                );
                v___y_600_ = v___x_633_;
                state = 11;
                continue;
            }
            20 => {
                v___x_640_ = 0;
                if v_isShared_639_ == 0 {
                    v___x_642_ = v___x_638_;
                    state = 21;
                    continue;
                } else {
                    v_reuseFailAlloc_643_ = leanh::lean_alloc_ctor(0, 1, (1) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_643_, 0, v_gate_636_);
                    v___x_642_ = v_reuseFailAlloc_643_;
                    state = 21;
                    continue;
                }
            }
            21 => {
                leanh::lean_ctor_set_uint8(
                    v___x_642_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                    v___x_640_,
                );
                v___y_600_ = v___x_642_;
                state = 11;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Sat_AIG_mkOrCached(
    mut v_00_u03b1_646_: *mut leanh::LeanObject,
    mut v_inst_647_: *mut leanh::LeanObject,
    mut v_inst_648_: *mut leanh::LeanObject,
    mut v_aig_649_: *mut leanh::LeanObject,
    mut v_input_650_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_651_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_651_ =
        l_Std_Sat_AIG_mkOrCached___redArg(v_inst_647_, v_inst_648_, v_aig_649_, v_input_650_);
    return v___x_651_;
}
pub unsafe fn l_Std_Sat_AIG_mkXorCached___redArg(
    mut v_inst_652_: *mut leanh::LeanObject,
    mut v_inst_653_: *mut leanh::LeanObject,
    mut v_aig_654_: *mut leanh::LeanObject,
    mut v_input_655_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___y_657_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_658_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_659_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_660_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_661_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_663_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_664_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_665_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_invert_666_: u8 = 0;
    let mut v_gate_667_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_669_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_670_: u8 = 0;
    let mut v___x_671_: u8 = 0;
    let mut v___x_673_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_674_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_675_: u8 = 0;
    let mut v_gate_676_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_678_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_679_: u8 = 0;
    let mut v___x_680_: u8 = 0;
    let mut v___x_682_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_683_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_684_: u8 = 0;
    let mut v_res_685_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_aig_686_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_687_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_689_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_res_690_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_invert_691_: u8 = 0;
    let mut v_aig_692_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_693_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_gate_694_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_696_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_697_: u8 = 0;
    let mut v___x_698_: u8 = 0;
    let mut v___x_700_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_701_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_702_: u8 = 0;
    let mut v_aig_703_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_704_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_gate_705_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_707_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_708_: u8 = 0;
    let mut v___x_709_: u8 = 0;
    let mut v___x_711_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_712_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_713_: u8 = 0;
    let mut v_lhs_714_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_rhs_715_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_717_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_718_: u8 = 0;
    let mut v_gate_719_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_invert_720_: u8 = 0;
    let mut v___x_722_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_723_: u8 = 0;
    let mut v_gate_724_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_invert_725_: u8 = 0;
    let mut v___x_727_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_728_: u8 = 0;
    let mut v___y_730_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_731_: u8 = 0;
    let mut v___x_733_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_735_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_736_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_737_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_738_: u8 = 0;
    let mut v___x_740_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_742_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_743_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_744_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_745_: u8 = 0;
    let mut v___x_747_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_748_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_749_: u8 = 0;
    let mut v___x_751_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_752_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_753_: u8 = 0;
    let mut v_isSharedCheck_754_: u8 = 0;
    let mut v_isSharedCheck_755_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                leanh::lean_inc_ref(v_input_655_);
                leanh::lean_inc_ref(v_inst_653_);
                leanh::lean_inc_ref(v_inst_652_);
                v_res_685_ = l_Std_Sat_AIG_mkGateCached___redArg(
                    v_inst_652_,
                    v_inst_653_,
                    v_aig_654_,
                    v_input_655_,
                );
                v_aig_686_ = leanh::lean_ctor_get(v_res_685_, 0);
                leanh::lean_inc_ref(v_aig_686_);
                v_ref_687_ = leanh::lean_ctor_get(v_res_685_, 1);
                leanh::lean_inc_ref(v_ref_687_);
                leanh::lean_dec_ref(v_res_685_);
                v_lhs_714_ = leanh::lean_ctor_get(v_input_655_, 0);
                v_rhs_715_ = leanh::lean_ctor_get(v_input_655_, 1);
                v_isSharedCheck_755_ = (!leanh::lean_is_exclusive(v_input_655_)) as u8;
                if v_isSharedCheck_755_ == 0 {
                    v___x_717_ = v_input_655_;
                    v_isShared_718_ = v_isSharedCheck_755_;
                    state = 12;
                    continue;
                } else {
                    leanh::lean_inc(v_rhs_715_);
                    leanh::lean_inc(v_lhs_714_);
                    leanh::lean_dec(v_input_655_);
                    v___x_717_ = leanh::lean_box(0);
                    v_isShared_718_ = v_isSharedCheck_755_;
                    state = 12;
                    continue;
                }
            }
            1 => {
                v___x_660_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_660_, 0, v___y_658_);
                leanh::lean_ctor_set(v___x_660_, 1, v___y_659_);
                v___x_661_ = l_Std_Sat_AIG_mkGateCached___redArg(
                    v_inst_652_,
                    v_inst_653_,
                    v___y_657_,
                    v___x_660_,
                );
                return v___x_661_;
            }
            2 => {
                v_invert_666_ = leanh::lean_ctor_get_uint8(
                    v___y_663_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                );
                if v_invert_666_ == 0 {
                    v_gate_667_ = leanh::lean_ctor_get(v___y_663_, 0);
                    v_isSharedCheck_675_ = (!leanh::lean_is_exclusive(v___y_663_)) as u8;
                    if v_isSharedCheck_675_ == 0 {
                        v___x_669_ = v___y_663_;
                        v_isShared_670_ = v_isSharedCheck_675_;
                        state = 3;
                        continue;
                    } else {
                        leanh::lean_inc(v_gate_667_);
                        leanh::lean_dec(v___y_663_);
                        v___x_669_ = leanh::lean_box(0);
                        v_isShared_670_ = v_isSharedCheck_675_;
                        state = 3;
                        continue;
                    }
                } else {
                    v_gate_676_ = leanh::lean_ctor_get(v___y_663_, 0);
                    v_isSharedCheck_684_ = (!leanh::lean_is_exclusive(v___y_663_)) as u8;
                    if v_isSharedCheck_684_ == 0 {
                        v___x_678_ = v___y_663_;
                        v_isShared_679_ = v_isSharedCheck_684_;
                        state = 5;
                        continue;
                    } else {
                        leanh::lean_inc(v_gate_676_);
                        leanh::lean_dec(v___y_663_);
                        v___x_678_ = leanh::lean_box(0);
                        v_isShared_679_ = v_isSharedCheck_684_;
                        state = 5;
                        continue;
                    }
                }
            }
            3 => {
                v___x_671_ = 1;
                if v_isShared_670_ == 0 {
                    v___x_673_ = v___x_669_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_674_ = leanh::lean_alloc_ctor(0, 1, (1) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_674_, 0, v_gate_667_);
                    v___x_673_ = v_reuseFailAlloc_674_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                leanh::lean_ctor_set_uint8(
                    v___x_673_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                    v___x_671_,
                );
                v___y_657_ = v___y_664_;
                v___y_658_ = v___y_665_;
                v___y_659_ = v___x_673_;
                state = 1;
                continue;
            }
            5 => {
                v___x_680_ = 0;
                if v_isShared_679_ == 0 {
                    v___x_682_ = v___x_678_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_683_ = leanh::lean_alloc_ctor(0, 1, (1) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_683_, 0, v_gate_676_);
                    v___x_682_ = v_reuseFailAlloc_683_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                leanh::lean_ctor_set_uint8(
                    v___x_682_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                    v___x_680_,
                );
                v___y_657_ = v___y_664_;
                v___y_658_ = v___y_665_;
                v___y_659_ = v___x_682_;
                state = 1;
                continue;
            }
            7 => {
                leanh::lean_inc_ref(v_inst_653_);
                leanh::lean_inc_ref(v_inst_652_);
                v_res_690_ = l_Std_Sat_AIG_mkGateCached___redArg(
                    v_inst_652_,
                    v_inst_653_,
                    v_aig_686_,
                    v___y_689_,
                );
                v_invert_691_ = leanh::lean_ctor_get_uint8(
                    v_ref_687_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                );
                if v_invert_691_ == 0 {
                    v_aig_692_ = leanh::lean_ctor_get(v_res_690_, 0);
                    leanh::lean_inc_ref(v_aig_692_);
                    v_ref_693_ = leanh::lean_ctor_get(v_res_690_, 1);
                    leanh::lean_inc_ref(v_ref_693_);
                    leanh::lean_dec_ref(v_res_690_);
                    v_gate_694_ = leanh::lean_ctor_get(v_ref_687_, 0);
                    v_isSharedCheck_702_ = (!leanh::lean_is_exclusive(v_ref_687_)) as u8;
                    if v_isSharedCheck_702_ == 0 {
                        v___x_696_ = v_ref_687_;
                        v_isShared_697_ = v_isSharedCheck_702_;
                        state = 8;
                        continue;
                    } else {
                        leanh::lean_inc(v_gate_694_);
                        leanh::lean_dec(v_ref_687_);
                        v___x_696_ = leanh::lean_box(0);
                        v_isShared_697_ = v_isSharedCheck_702_;
                        state = 8;
                        continue;
                    }
                } else {
                    v_aig_703_ = leanh::lean_ctor_get(v_res_690_, 0);
                    leanh::lean_inc_ref(v_aig_703_);
                    v_ref_704_ = leanh::lean_ctor_get(v_res_690_, 1);
                    leanh::lean_inc_ref(v_ref_704_);
                    leanh::lean_dec_ref(v_res_690_);
                    v_gate_705_ = leanh::lean_ctor_get(v_ref_687_, 0);
                    v_isSharedCheck_713_ = (!leanh::lean_is_exclusive(v_ref_687_)) as u8;
                    if v_isSharedCheck_713_ == 0 {
                        v___x_707_ = v_ref_687_;
                        v_isShared_708_ = v_isSharedCheck_713_;
                        state = 10;
                        continue;
                    } else {
                        leanh::lean_inc(v_gate_705_);
                        leanh::lean_dec(v_ref_687_);
                        v___x_707_ = leanh::lean_box(0);
                        v_isShared_708_ = v_isSharedCheck_713_;
                        state = 10;
                        continue;
                    }
                }
            }
            8 => {
                v___x_698_ = 1;
                if v_isShared_697_ == 0 {
                    v___x_700_ = v___x_696_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_701_ = leanh::lean_alloc_ctor(0, 1, (1) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_701_, 0, v_gate_694_);
                    v___x_700_ = v_reuseFailAlloc_701_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                leanh::lean_ctor_set_uint8(
                    v___x_700_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                    v___x_698_,
                );
                v___y_663_ = v_ref_693_;
                v___y_664_ = v_aig_692_;
                v___y_665_ = v___x_700_;
                state = 2;
                continue;
            }
            10 => {
                v___x_709_ = 0;
                if v_isShared_708_ == 0 {
                    v___x_711_ = v___x_707_;
                    state = 11;
                    continue;
                } else {
                    v_reuseFailAlloc_712_ = leanh::lean_alloc_ctor(0, 1, (1) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_712_, 0, v_gate_705_);
                    v___x_711_ = v_reuseFailAlloc_712_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                leanh::lean_ctor_set_uint8(
                    v___x_711_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                    v___x_709_,
                );
                v___y_663_ = v_ref_704_;
                v___y_664_ = v_aig_703_;
                v___y_665_ = v___x_711_;
                state = 2;
                continue;
            }
            12 => {
                v_gate_719_ = leanh::lean_ctor_get(v_lhs_714_, 0);
                v_invert_720_ = leanh::lean_ctor_get_uint8(
                    v_lhs_714_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                );
                v_isSharedCheck_754_ = (!leanh::lean_is_exclusive(v_lhs_714_)) as u8;
                if v_isSharedCheck_754_ == 0 {
                    v___x_722_ = v_lhs_714_;
                    v_isShared_723_ = v_isSharedCheck_754_;
                    state = 13;
                    continue;
                } else {
                    leanh::lean_inc(v_gate_719_);
                    leanh::lean_dec(v_lhs_714_);
                    v___x_722_ = leanh::lean_box(0);
                    v_isShared_723_ = v_isSharedCheck_754_;
                    state = 13;
                    continue;
                }
            }
            13 => {
                v_gate_724_ = leanh::lean_ctor_get(v_rhs_715_, 0);
                v_invert_725_ = leanh::lean_ctor_get_uint8(
                    v_rhs_715_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                );
                v_isSharedCheck_753_ = (!leanh::lean_is_exclusive(v_rhs_715_)) as u8;
                if v_isSharedCheck_753_ == 0 {
                    v___x_727_ = v_rhs_715_;
                    v_isShared_728_ = v_isSharedCheck_753_;
                    state = 14;
                    continue;
                } else {
                    leanh::lean_inc(v_gate_724_);
                    leanh::lean_dec(v_rhs_715_);
                    v___x_727_ = leanh::lean_box(0);
                    v_isShared_728_ = v_isSharedCheck_753_;
                    state = 14;
                    continue;
                }
            }
            14 => {
                if v_invert_720_ == 0 {
                    v___x_745_ = 1;
                    if v_isShared_723_ == 0 {
                        v___x_747_ = v___x_722_;
                        state = 20;
                        continue;
                    } else {
                        v_reuseFailAlloc_748_ = leanh::lean_alloc_ctor(0, 1, (1) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_748_, 0, v_gate_719_);
                        v___x_747_ = v_reuseFailAlloc_748_;
                        state = 20;
                        continue;
                    }
                } else {
                    v___x_749_ = 0;
                    if v_isShared_723_ == 0 {
                        v___x_751_ = v___x_722_;
                        state = 21;
                        continue;
                    } else {
                        v_reuseFailAlloc_752_ = leanh::lean_alloc_ctor(0, 1, (1) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_752_, 0, v_gate_719_);
                        v___x_751_ = v_reuseFailAlloc_752_;
                        state = 21;
                        continue;
                    }
                }
            }
            15 => {
                if v_invert_725_ == 0 {
                    v___x_731_ = 1;
                    if v_isShared_728_ == 0 {
                        v___x_733_ = v___x_727_;
                        state = 16;
                        continue;
                    } else {
                        v_reuseFailAlloc_737_ = leanh::lean_alloc_ctor(0, 1, (1) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_737_, 0, v_gate_724_);
                        v___x_733_ = v_reuseFailAlloc_737_;
                        state = 16;
                        continue;
                    }
                } else {
                    v___x_738_ = 0;
                    if v_isShared_728_ == 0 {
                        v___x_740_ = v___x_727_;
                        state = 18;
                        continue;
                    } else {
                        v_reuseFailAlloc_744_ = leanh::lean_alloc_ctor(0, 1, (1) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_744_, 0, v_gate_724_);
                        v___x_740_ = v_reuseFailAlloc_744_;
                        state = 18;
                        continue;
                    }
                }
            }
            16 => {
                leanh::lean_ctor_set_uint8(
                    v___x_733_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                    v___x_731_,
                );
                if v_isShared_718_ == 0 {
                    leanh::lean_ctor_set(v___x_717_, 1, v___x_733_);
                    leanh::lean_ctor_set(v___x_717_, 0, v___y_730_);
                    v___x_735_ = v___x_717_;
                    state = 17;
                    continue;
                } else {
                    v_reuseFailAlloc_736_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_736_, 0, v___y_730_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_736_, 1, v___x_733_);
                    v___x_735_ = v_reuseFailAlloc_736_;
                    state = 17;
                    continue;
                }
            }
            17 => {
                v___y_689_ = v___x_735_;
                state = 7;
                continue;
            }
            18 => {
                leanh::lean_ctor_set_uint8(
                    v___x_740_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                    v___x_738_,
                );
                if v_isShared_718_ == 0 {
                    leanh::lean_ctor_set(v___x_717_, 1, v___x_740_);
                    leanh::lean_ctor_set(v___x_717_, 0, v___y_730_);
                    v___x_742_ = v___x_717_;
                    state = 19;
                    continue;
                } else {
                    v_reuseFailAlloc_743_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_743_, 0, v___y_730_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_743_, 1, v___x_740_);
                    v___x_742_ = v_reuseFailAlloc_743_;
                    state = 19;
                    continue;
                }
            }
            19 => {
                v___y_689_ = v___x_742_;
                state = 7;
                continue;
            }
            20 => {
                leanh::lean_ctor_set_uint8(
                    v___x_747_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                    v___x_745_,
                );
                v___y_730_ = v___x_747_;
                state = 15;
                continue;
            }
            21 => {
                leanh::lean_ctor_set_uint8(
                    v___x_751_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                    v___x_749_,
                );
                v___y_730_ = v___x_751_;
                state = 15;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Sat_AIG_mkXorCached(
    mut v_00_u03b1_756_: *mut leanh::LeanObject,
    mut v_inst_757_: *mut leanh::LeanObject,
    mut v_inst_758_: *mut leanh::LeanObject,
    mut v_aig_759_: *mut leanh::LeanObject,
    mut v_input_760_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_761_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_761_ =
        l_Std_Sat_AIG_mkXorCached___redArg(v_inst_757_, v_inst_758_, v_aig_759_, v_input_760_);
    return v___x_761_;
}
pub unsafe fn l_Std_Sat_AIG_mkBEqCached___redArg(
    mut v_inst_762_: *mut leanh::LeanObject,
    mut v_inst_763_: *mut leanh::LeanObject,
    mut v_aig_764_: *mut leanh::LeanObject,
    mut v_input_765_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___y_767_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_768_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_769_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_770_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_771_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_773_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_774_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_775_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_invert_776_: u8 = 0;
    let mut v_gate_777_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_779_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_780_: u8 = 0;
    let mut v___x_781_: u8 = 0;
    let mut v___x_783_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_784_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_785_: u8 = 0;
    let mut v_gate_786_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_788_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_789_: u8 = 0;
    let mut v___x_790_: u8 = 0;
    let mut v___x_792_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_793_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_794_: u8 = 0;
    let mut v___y_796_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_797_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_798_: u8 = 0;
    let mut v___y_799_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_800_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_801_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_802_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_res_803_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_invert_804_: u8 = 0;
    let mut v_aig_805_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_806_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_gate_807_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_809_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_810_: u8 = 0;
    let mut v___x_811_: u8 = 0;
    let mut v___x_813_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_814_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_815_: u8 = 0;
    let mut v_aig_816_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_817_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_gate_818_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_820_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_821_: u8 = 0;
    let mut v___x_822_: u8 = 0;
    let mut v___x_824_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_825_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_826_: u8 = 0;
    let mut v_lhs_827_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_rhs_828_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_830_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_831_: u8 = 0;
    let mut v_gate_832_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_invert_833_: u8 = 0;
    let mut v___x_835_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_836_: u8 = 0;
    let mut v_gate_837_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_invert_838_: u8 = 0;
    let mut v___x_840_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_841_: u8 = 0;
    let mut v___y_843_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_res_844_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_aig_845_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_846_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_847_: u8 = 0;
    let mut v___x_849_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_850_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_aig_851_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_852_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_853_: u8 = 0;
    let mut v___x_855_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_856_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_858_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_859_: u8 = 0;
    let mut v___x_860_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_862_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_863_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_864_: u8 = 0;
    let mut v___x_865_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_867_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_868_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_869_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_870_: u8 = 0;
    let mut v_isSharedCheck_871_: u8 = 0;
    let mut v_isSharedCheck_872_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_lhs_827_ = leanh::lean_ctor_get(v_input_765_, 0);
                v_rhs_828_ = leanh::lean_ctor_get(v_input_765_, 1);
                v_isSharedCheck_872_ = (!leanh::lean_is_exclusive(v_input_765_)) as u8;
                if v_isSharedCheck_872_ == 0 {
                    v___x_830_ = v_input_765_;
                    v_isShared_831_ = v_isSharedCheck_872_;
                    state = 12;
                    continue;
                } else {
                    leanh::lean_inc(v_rhs_828_);
                    leanh::lean_inc(v_lhs_827_);
                    leanh::lean_dec(v_input_765_);
                    v___x_830_ = leanh::lean_box(0);
                    v_isShared_831_ = v_isSharedCheck_872_;
                    state = 12;
                    continue;
                }
            }
            1 => {
                v___x_770_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_770_, 0, v___y_768_);
                leanh::lean_ctor_set(v___x_770_, 1, v___y_769_);
                v___x_771_ = l_Std_Sat_AIG_mkGateCached___redArg(
                    v_inst_762_,
                    v_inst_763_,
                    v___y_767_,
                    v___x_770_,
                );
                return v___x_771_;
            }
            2 => {
                v_invert_776_ = leanh::lean_ctor_get_uint8(
                    v___y_773_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                );
                if v_invert_776_ == 0 {
                    v_gate_777_ = leanh::lean_ctor_get(v___y_773_, 0);
                    v_isSharedCheck_785_ = (!leanh::lean_is_exclusive(v___y_773_)) as u8;
                    if v_isSharedCheck_785_ == 0 {
                        v___x_779_ = v___y_773_;
                        v_isShared_780_ = v_isSharedCheck_785_;
                        state = 3;
                        continue;
                    } else {
                        leanh::lean_inc(v_gate_777_);
                        leanh::lean_dec(v___y_773_);
                        v___x_779_ = leanh::lean_box(0);
                        v_isShared_780_ = v_isSharedCheck_785_;
                        state = 3;
                        continue;
                    }
                } else {
                    v_gate_786_ = leanh::lean_ctor_get(v___y_773_, 0);
                    v_isSharedCheck_794_ = (!leanh::lean_is_exclusive(v___y_773_)) as u8;
                    if v_isSharedCheck_794_ == 0 {
                        v___x_788_ = v___y_773_;
                        v_isShared_789_ = v_isSharedCheck_794_;
                        state = 5;
                        continue;
                    } else {
                        leanh::lean_inc(v_gate_786_);
                        leanh::lean_dec(v___y_773_);
                        v___x_788_ = leanh::lean_box(0);
                        v_isShared_789_ = v_isSharedCheck_794_;
                        state = 5;
                        continue;
                    }
                }
            }
            3 => {
                v___x_781_ = 1;
                if v_isShared_780_ == 0 {
                    v___x_783_ = v___x_779_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_784_ = leanh::lean_alloc_ctor(0, 1, (1) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_784_, 0, v_gate_777_);
                    v___x_783_ = v_reuseFailAlloc_784_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                leanh::lean_ctor_set_uint8(
                    v___x_783_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                    v___x_781_,
                );
                v___y_767_ = v___y_774_;
                v___y_768_ = v___y_775_;
                v___y_769_ = v___x_783_;
                state = 1;
                continue;
            }
            5 => {
                v___x_790_ = 0;
                if v_isShared_789_ == 0 {
                    v___x_792_ = v___x_788_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_793_ = leanh::lean_alloc_ctor(0, 1, (1) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_793_, 0, v_gate_786_);
                    v___x_792_ = v_reuseFailAlloc_793_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                leanh::lean_ctor_set_uint8(
                    v___x_792_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                    v___x_790_,
                );
                v___y_767_ = v___y_774_;
                v___y_768_ = v___y_775_;
                v___y_769_ = v___x_792_;
                state = 1;
                continue;
            }
            7 => {
                v___x_801_ = leanh::lean_alloc_ctor(0, 1, (1) as u32);
                leanh::lean_ctor_set(v___x_801_, 0, v___y_796_);
                leanh::lean_ctor_set_uint8(
                    v___x_801_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                    v___y_798_,
                );
                v___x_802_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_802_, 0, v___y_800_);
                leanh::lean_ctor_set(v___x_802_, 1, v___x_801_);
                leanh::lean_inc_ref(v_inst_763_);
                leanh::lean_inc_ref(v_inst_762_);
                v_res_803_ = l_Std_Sat_AIG_mkGateCached___redArg(
                    v_inst_762_,
                    v_inst_763_,
                    v___y_799_,
                    v___x_802_,
                );
                v_invert_804_ = leanh::lean_ctor_get_uint8(
                    v___y_797_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                );
                if v_invert_804_ == 0 {
                    v_aig_805_ = leanh::lean_ctor_get(v_res_803_, 0);
                    leanh::lean_inc_ref(v_aig_805_);
                    v_ref_806_ = leanh::lean_ctor_get(v_res_803_, 1);
                    leanh::lean_inc_ref(v_ref_806_);
                    leanh::lean_dec_ref(v_res_803_);
                    v_gate_807_ = leanh::lean_ctor_get(v___y_797_, 0);
                    v_isSharedCheck_815_ = (!leanh::lean_is_exclusive(v___y_797_)) as u8;
                    if v_isSharedCheck_815_ == 0 {
                        v___x_809_ = v___y_797_;
                        v_isShared_810_ = v_isSharedCheck_815_;
                        state = 8;
                        continue;
                    } else {
                        leanh::lean_inc(v_gate_807_);
                        leanh::lean_dec(v___y_797_);
                        v___x_809_ = leanh::lean_box(0);
                        v_isShared_810_ = v_isSharedCheck_815_;
                        state = 8;
                        continue;
                    }
                } else {
                    v_aig_816_ = leanh::lean_ctor_get(v_res_803_, 0);
                    leanh::lean_inc_ref(v_aig_816_);
                    v_ref_817_ = leanh::lean_ctor_get(v_res_803_, 1);
                    leanh::lean_inc_ref(v_ref_817_);
                    leanh::lean_dec_ref(v_res_803_);
                    v_gate_818_ = leanh::lean_ctor_get(v___y_797_, 0);
                    v_isSharedCheck_826_ = (!leanh::lean_is_exclusive(v___y_797_)) as u8;
                    if v_isSharedCheck_826_ == 0 {
                        v___x_820_ = v___y_797_;
                        v_isShared_821_ = v_isSharedCheck_826_;
                        state = 10;
                        continue;
                    } else {
                        leanh::lean_inc(v_gate_818_);
                        leanh::lean_dec(v___y_797_);
                        v___x_820_ = leanh::lean_box(0);
                        v_isShared_821_ = v_isSharedCheck_826_;
                        state = 10;
                        continue;
                    }
                }
            }
            8 => {
                v___x_811_ = 1;
                if v_isShared_810_ == 0 {
                    v___x_813_ = v___x_809_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_814_ = leanh::lean_alloc_ctor(0, 1, (1) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_814_, 0, v_gate_807_);
                    v___x_813_ = v_reuseFailAlloc_814_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                leanh::lean_ctor_set_uint8(
                    v___x_813_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                    v___x_811_,
                );
                v___y_773_ = v_ref_806_;
                v___y_774_ = v_aig_805_;
                v___y_775_ = v___x_813_;
                state = 2;
                continue;
            }
            10 => {
                v___x_822_ = 0;
                if v_isShared_821_ == 0 {
                    v___x_824_ = v___x_820_;
                    state = 11;
                    continue;
                } else {
                    v_reuseFailAlloc_825_ = leanh::lean_alloc_ctor(0, 1, (1) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_825_, 0, v_gate_818_);
                    v___x_824_ = v_reuseFailAlloc_825_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                leanh::lean_ctor_set_uint8(
                    v___x_824_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                    v___x_822_,
                );
                v___y_773_ = v_ref_817_;
                v___y_774_ = v_aig_816_;
                v___y_775_ = v___x_824_;
                state = 2;
                continue;
            }
            12 => {
                v_gate_832_ = leanh::lean_ctor_get(v_lhs_827_, 0);
                v_invert_833_ = leanh::lean_ctor_get_uint8(
                    v_lhs_827_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                );
                v_isSharedCheck_871_ = (!leanh::lean_is_exclusive(v_lhs_827_)) as u8;
                if v_isSharedCheck_871_ == 0 {
                    v___x_835_ = v_lhs_827_;
                    v_isShared_836_ = v_isSharedCheck_871_;
                    state = 13;
                    continue;
                } else {
                    leanh::lean_inc(v_gate_832_);
                    leanh::lean_dec(v_lhs_827_);
                    v___x_835_ = leanh::lean_box(0);
                    v_isShared_836_ = v_isSharedCheck_871_;
                    state = 13;
                    continue;
                }
            }
            13 => {
                v_gate_837_ = leanh::lean_ctor_get(v_rhs_828_, 0);
                v_invert_838_ = leanh::lean_ctor_get_uint8(
                    v_rhs_828_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                );
                v_isSharedCheck_870_ = (!leanh::lean_is_exclusive(v_rhs_828_)) as u8;
                if v_isSharedCheck_870_ == 0 {
                    v___x_840_ = v_rhs_828_;
                    v_isShared_841_ = v_isSharedCheck_870_;
                    state = 14;
                    continue;
                } else {
                    leanh::lean_inc(v_gate_837_);
                    leanh::lean_dec(v_rhs_828_);
                    v___x_840_ = leanh::lean_box(0);
                    v_isShared_841_ = v_isSharedCheck_870_;
                    state = 14;
                    continue;
                }
            }
            14 => {
                leanh::lean_inc(v_gate_832_);
                if v_isShared_836_ == 0 {
                    v___x_858_ = v___x_835_;
                    state = 18;
                    continue;
                } else {
                    v_reuseFailAlloc_869_ = leanh::lean_alloc_ctor(0, 1, (1) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_869_, 0, v_gate_832_);
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_869_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                        v_invert_833_,
                    );
                    v___x_858_ = v_reuseFailAlloc_869_;
                    state = 18;
                    continue;
                }
            }
            15 => {
                leanh::lean_inc_ref(v_inst_763_);
                leanh::lean_inc_ref(v_inst_762_);
                v_res_844_ = l_Std_Sat_AIG_mkGateCached___redArg(
                    v_inst_762_,
                    v_inst_763_,
                    v_aig_764_,
                    v___y_843_,
                );
                if v_invert_833_ == 0 {
                    v_aig_845_ = leanh::lean_ctor_get(v_res_844_, 0);
                    leanh::lean_inc_ref(v_aig_845_);
                    v_ref_846_ = leanh::lean_ctor_get(v_res_844_, 1);
                    leanh::lean_inc_ref(v_ref_846_);
                    leanh::lean_dec_ref(v_res_844_);
                    v___x_847_ = 1;
                    if v_isShared_841_ == 0 {
                        leanh::lean_ctor_set(v___x_840_, 0, v_gate_832_);
                        v___x_849_ = v___x_840_;
                        state = 16;
                        continue;
                    } else {
                        v_reuseFailAlloc_850_ = leanh::lean_alloc_ctor(0, 1, (1) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_850_, 0, v_gate_832_);
                        v___x_849_ = v_reuseFailAlloc_850_;
                        state = 16;
                        continue;
                    }
                } else {
                    v_aig_851_ = leanh::lean_ctor_get(v_res_844_, 0);
                    leanh::lean_inc_ref(v_aig_851_);
                    v_ref_852_ = leanh::lean_ctor_get(v_res_844_, 1);
                    leanh::lean_inc_ref(v_ref_852_);
                    leanh::lean_dec_ref(v_res_844_);
                    v___x_853_ = 0;
                    if v_isShared_841_ == 0 {
                        leanh::lean_ctor_set(v___x_840_, 0, v_gate_832_);
                        v___x_855_ = v___x_840_;
                        state = 17;
                        continue;
                    } else {
                        v_reuseFailAlloc_856_ = leanh::lean_alloc_ctor(0, 1, (1) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_856_, 0, v_gate_832_);
                        v___x_855_ = v_reuseFailAlloc_856_;
                        state = 17;
                        continue;
                    }
                }
            }
            16 => {
                leanh::lean_ctor_set_uint8(
                    v___x_849_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                    v___x_847_,
                );
                v___y_796_ = v_gate_837_;
                v___y_797_ = v_ref_846_;
                v___y_798_ = v_invert_838_;
                v___y_799_ = v_aig_845_;
                v___y_800_ = v___x_849_;
                state = 7;
                continue;
            }
            17 => {
                leanh::lean_ctor_set_uint8(
                    v___x_855_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                    v___x_853_,
                );
                v___y_796_ = v_gate_837_;
                v___y_797_ = v_ref_852_;
                v___y_798_ = v_invert_838_;
                v___y_799_ = v_aig_851_;
                v___y_800_ = v___x_855_;
                state = 7;
                continue;
            }
            18 => {
                if v_invert_838_ == 0 {
                    v___x_859_ = 1;
                    leanh::lean_inc(v_gate_837_);
                    v___x_860_ = leanh::lean_alloc_ctor(0, 1, (1) as u32);
                    leanh::lean_ctor_set(v___x_860_, 0, v_gate_837_);
                    leanh::lean_ctor_set_uint8(
                        v___x_860_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                        v___x_859_,
                    );
                    if v_isShared_831_ == 0 {
                        leanh::lean_ctor_set(v___x_830_, 1, v___x_860_);
                        leanh::lean_ctor_set(v___x_830_, 0, v___x_858_);
                        v___x_862_ = v___x_830_;
                        state = 19;
                        continue;
                    } else {
                        v_reuseFailAlloc_863_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_863_, 0, v___x_858_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_863_, 1, v___x_860_);
                        v___x_862_ = v_reuseFailAlloc_863_;
                        state = 19;
                        continue;
                    }
                } else {
                    v___x_864_ = 0;
                    leanh::lean_inc(v_gate_837_);
                    v___x_865_ = leanh::lean_alloc_ctor(0, 1, (1) as u32);
                    leanh::lean_ctor_set(v___x_865_, 0, v_gate_837_);
                    leanh::lean_ctor_set_uint8(
                        v___x_865_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                        v___x_864_,
                    );
                    if v_isShared_831_ == 0 {
                        leanh::lean_ctor_set(v___x_830_, 1, v___x_865_);
                        leanh::lean_ctor_set(v___x_830_, 0, v___x_858_);
                        v___x_867_ = v___x_830_;
                        state = 20;
                        continue;
                    } else {
                        v_reuseFailAlloc_868_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_868_, 0, v___x_858_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_868_, 1, v___x_865_);
                        v___x_867_ = v_reuseFailAlloc_868_;
                        state = 20;
                        continue;
                    }
                }
            }
            19 => {
                v___y_843_ = v___x_862_;
                state = 15;
                continue;
            }
            20 => {
                v___y_843_ = v___x_867_;
                state = 15;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Sat_AIG_mkBEqCached(
    mut v_00_u03b1_873_: *mut leanh::LeanObject,
    mut v_inst_874_: *mut leanh::LeanObject,
    mut v_inst_875_: *mut leanh::LeanObject,
    mut v_aig_876_: *mut leanh::LeanObject,
    mut v_input_877_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_878_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_878_ =
        l_Std_Sat_AIG_mkBEqCached___redArg(v_inst_874_, v_inst_875_, v_aig_876_, v_input_877_);
    return v___x_878_;
}
pub unsafe fn l_Std_Sat_AIG_mkImpCached___redArg(
    mut v_inst_879_: *mut leanh::LeanObject,
    mut v_inst_880_: *mut leanh::LeanObject,
    mut v_aig_881_: *mut leanh::LeanObject,
    mut v_input_882_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___y_884_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_res_885_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_886_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_invert_887_: u8 = 0;
    let mut v_aig_888_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_890_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_891_: u8 = 0;
    let mut v_gate_892_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_894_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_895_: u8 = 0;
    let mut v___x_896_: u8 = 0;
    let mut v___x_898_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_900_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_901_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_902_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_903_: u8 = 0;
    let mut v_isSharedCheck_904_: u8 = 0;
    let mut v_unused_905_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_aig_906_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_908_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_909_: u8 = 0;
    let mut v_gate_910_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_912_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_913_: u8 = 0;
    let mut v___x_914_: u8 = 0;
    let mut v___x_916_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_918_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_919_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_920_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_921_: u8 = 0;
    let mut v_isSharedCheck_922_: u8 = 0;
    let mut v_unused_923_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_lhs_924_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_rhs_925_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_927_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_928_: u8 = 0;
    let mut v_gate_929_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_invert_930_: u8 = 0;
    let mut v___x_932_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_933_: u8 = 0;
    let mut v_gate_934_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_invert_935_: u8 = 0;
    let mut v___x_937_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_938_: u8 = 0;
    let mut v___x_940_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_941_: u8 = 0;
    let mut v___x_943_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_945_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_946_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_947_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_948_: u8 = 0;
    let mut v___x_950_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_952_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_953_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_954_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_955_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_956_: u8 = 0;
    let mut v_isSharedCheck_957_: u8 = 0;
    let mut v_isSharedCheck_958_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_lhs_924_ = leanh::lean_ctor_get(v_input_882_, 0);
                v_rhs_925_ = leanh::lean_ctor_get(v_input_882_, 1);
                v_isSharedCheck_958_ = (!leanh::lean_is_exclusive(v_input_882_)) as u8;
                if v_isSharedCheck_958_ == 0 {
                    v___x_927_ = v_input_882_;
                    v_isShared_928_ = v_isSharedCheck_958_;
                    state = 10;
                    continue;
                } else {
                    leanh::lean_inc(v_rhs_925_);
                    leanh::lean_inc(v_lhs_924_);
                    leanh::lean_dec(v_input_882_);
                    v___x_927_ = leanh::lean_box(0);
                    v_isShared_928_ = v_isSharedCheck_958_;
                    state = 10;
                    continue;
                }
            }
            1 => {
                v_res_885_ = l_Std_Sat_AIG_mkGateCached___redArg(
                    v_inst_879_,
                    v_inst_880_,
                    v_aig_881_,
                    v___y_884_,
                );
                v_ref_886_ = leanh::lean_ctor_get(v_res_885_, 1);
                leanh::lean_inc_ref(v_ref_886_);
                v_invert_887_ = leanh::lean_ctor_get_uint8(
                    v_ref_886_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                );
                if v_invert_887_ == 0 {
                    v_aig_888_ = leanh::lean_ctor_get(v_res_885_, 0);
                    v_isSharedCheck_904_ = (!leanh::lean_is_exclusive(v_res_885_)) as u8;
                    if v_isSharedCheck_904_ == 0 {
                        v_unused_905_ = leanh::lean_ctor_get(v_res_885_, 1);
                        leanh::lean_dec(v_unused_905_);
                        v___x_890_ = v_res_885_;
                        v_isShared_891_ = v_isSharedCheck_904_;
                        state = 2;
                        continue;
                    } else {
                        leanh::lean_inc(v_aig_888_);
                        leanh::lean_dec(v_res_885_);
                        v___x_890_ = leanh::lean_box(0);
                        v_isShared_891_ = v_isSharedCheck_904_;
                        state = 2;
                        continue;
                    }
                } else {
                    v_aig_906_ = leanh::lean_ctor_get(v_res_885_, 0);
                    v_isSharedCheck_922_ = (!leanh::lean_is_exclusive(v_res_885_)) as u8;
                    if v_isSharedCheck_922_ == 0 {
                        v_unused_923_ = leanh::lean_ctor_get(v_res_885_, 1);
                        leanh::lean_dec(v_unused_923_);
                        v___x_908_ = v_res_885_;
                        v_isShared_909_ = v_isSharedCheck_922_;
                        state = 6;
                        continue;
                    } else {
                        leanh::lean_inc(v_aig_906_);
                        leanh::lean_dec(v_res_885_);
                        v___x_908_ = leanh::lean_box(0);
                        v_isShared_909_ = v_isSharedCheck_922_;
                        state = 6;
                        continue;
                    }
                }
            }
            2 => {
                v_gate_892_ = leanh::lean_ctor_get(v_ref_886_, 0);
                v_isSharedCheck_903_ = (!leanh::lean_is_exclusive(v_ref_886_)) as u8;
                if v_isSharedCheck_903_ == 0 {
                    v___x_894_ = v_ref_886_;
                    v_isShared_895_ = v_isSharedCheck_903_;
                    state = 3;
                    continue;
                } else {
                    leanh::lean_inc(v_gate_892_);
                    leanh::lean_dec(v_ref_886_);
                    v___x_894_ = leanh::lean_box(0);
                    v_isShared_895_ = v_isSharedCheck_903_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_896_ = 1;
                if v_isShared_895_ == 0 {
                    v___x_898_ = v___x_894_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_902_ = leanh::lean_alloc_ctor(0, 1, (1) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_902_, 0, v_gate_892_);
                    v___x_898_ = v_reuseFailAlloc_902_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                leanh::lean_ctor_set_uint8(
                    v___x_898_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                    v___x_896_,
                );
                if v_isShared_891_ == 0 {
                    leanh::lean_ctor_set(v___x_890_, 1, v___x_898_);
                    v___x_900_ = v___x_890_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_901_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_901_, 0, v_aig_888_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_901_, 1, v___x_898_);
                    v___x_900_ = v_reuseFailAlloc_901_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_900_;
            }
            6 => {
                v_gate_910_ = leanh::lean_ctor_get(v_ref_886_, 0);
                v_isSharedCheck_921_ = (!leanh::lean_is_exclusive(v_ref_886_)) as u8;
                if v_isSharedCheck_921_ == 0 {
                    v___x_912_ = v_ref_886_;
                    v_isShared_913_ = v_isSharedCheck_921_;
                    state = 7;
                    continue;
                } else {
                    leanh::lean_inc(v_gate_910_);
                    leanh::lean_dec(v_ref_886_);
                    v___x_912_ = leanh::lean_box(0);
                    v_isShared_913_ = v_isSharedCheck_921_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                v___x_914_ = 0;
                if v_isShared_913_ == 0 {
                    v___x_916_ = v___x_912_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_920_ = leanh::lean_alloc_ctor(0, 1, (1) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_920_, 0, v_gate_910_);
                    v___x_916_ = v_reuseFailAlloc_920_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                leanh::lean_ctor_set_uint8(
                    v___x_916_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                    v___x_914_,
                );
                if v_isShared_909_ == 0 {
                    leanh::lean_ctor_set(v___x_908_, 1, v___x_916_);
                    v___x_918_ = v___x_908_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_919_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_919_, 0, v_aig_906_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_919_, 1, v___x_916_);
                    v___x_918_ = v_reuseFailAlloc_919_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                return v___x_918_;
            }
            10 => {
                v_gate_929_ = leanh::lean_ctor_get(v_lhs_924_, 0);
                v_invert_930_ = leanh::lean_ctor_get_uint8(
                    v_lhs_924_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                );
                v_isSharedCheck_957_ = (!leanh::lean_is_exclusive(v_lhs_924_)) as u8;
                if v_isSharedCheck_957_ == 0 {
                    v___x_932_ = v_lhs_924_;
                    v_isShared_933_ = v_isSharedCheck_957_;
                    state = 11;
                    continue;
                } else {
                    leanh::lean_inc(v_gate_929_);
                    leanh::lean_dec(v_lhs_924_);
                    v___x_932_ = leanh::lean_box(0);
                    v_isShared_933_ = v_isSharedCheck_957_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                v_gate_934_ = leanh::lean_ctor_get(v_rhs_925_, 0);
                v_invert_935_ = leanh::lean_ctor_get_uint8(
                    v_rhs_925_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                );
                v_isSharedCheck_956_ = (!leanh::lean_is_exclusive(v_rhs_925_)) as u8;
                if v_isSharedCheck_956_ == 0 {
                    v___x_937_ = v_rhs_925_;
                    v_isShared_938_ = v_isSharedCheck_956_;
                    state = 12;
                    continue;
                } else {
                    leanh::lean_inc(v_gate_934_);
                    leanh::lean_dec(v_rhs_925_);
                    v___x_937_ = leanh::lean_box(0);
                    v_isShared_938_ = v_isSharedCheck_956_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                if v_isShared_938_ == 0 {
                    leanh::lean_ctor_set(v___x_937_, 0, v_gate_929_);
                    v___x_940_ = v___x_937_;
                    state = 13;
                    continue;
                } else {
                    v_reuseFailAlloc_955_ = leanh::lean_alloc_ctor(0, 1, (1) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_955_, 0, v_gate_929_);
                    v___x_940_ = v_reuseFailAlloc_955_;
                    state = 13;
                    continue;
                }
            }
            13 => {
                leanh::lean_ctor_set_uint8(
                    v___x_940_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                    v_invert_930_,
                );
                if v_invert_935_ == 0 {
                    v___x_941_ = 1;
                    if v_isShared_933_ == 0 {
                        leanh::lean_ctor_set(v___x_932_, 0, v_gate_934_);
                        v___x_943_ = v___x_932_;
                        state = 14;
                        continue;
                    } else {
                        v_reuseFailAlloc_947_ = leanh::lean_alloc_ctor(0, 1, (1) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_947_, 0, v_gate_934_);
                        v___x_943_ = v_reuseFailAlloc_947_;
                        state = 14;
                        continue;
                    }
                } else {
                    v___x_948_ = 0;
                    if v_isShared_933_ == 0 {
                        leanh::lean_ctor_set(v___x_932_, 0, v_gate_934_);
                        v___x_950_ = v___x_932_;
                        state = 16;
                        continue;
                    } else {
                        v_reuseFailAlloc_954_ = leanh::lean_alloc_ctor(0, 1, (1) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_954_, 0, v_gate_934_);
                        v___x_950_ = v_reuseFailAlloc_954_;
                        state = 16;
                        continue;
                    }
                }
            }
            14 => {
                leanh::lean_ctor_set_uint8(
                    v___x_943_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                    v___x_941_,
                );
                if v_isShared_928_ == 0 {
                    leanh::lean_ctor_set(v___x_927_, 1, v___x_943_);
                    leanh::lean_ctor_set(v___x_927_, 0, v___x_940_);
                    v___x_945_ = v___x_927_;
                    state = 15;
                    continue;
                } else {
                    v_reuseFailAlloc_946_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_946_, 0, v___x_940_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_946_, 1, v___x_943_);
                    v___x_945_ = v_reuseFailAlloc_946_;
                    state = 15;
                    continue;
                }
            }
            15 => {
                v___y_884_ = v___x_945_;
                state = 1;
                continue;
            }
            16 => {
                leanh::lean_ctor_set_uint8(
                    v___x_950_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                    v___x_948_,
                );
                if v_isShared_928_ == 0 {
                    leanh::lean_ctor_set(v___x_927_, 1, v___x_950_);
                    leanh::lean_ctor_set(v___x_927_, 0, v___x_940_);
                    v___x_952_ = v___x_927_;
                    state = 17;
                    continue;
                } else {
                    v_reuseFailAlloc_953_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_953_, 0, v___x_940_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_953_, 1, v___x_950_);
                    v___x_952_ = v_reuseFailAlloc_953_;
                    state = 17;
                    continue;
                }
            }
            17 => {
                v___y_884_ = v___x_952_;
                state = 1;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Sat_AIG_mkImpCached(
    mut v_00_u03b1_959_: *mut leanh::LeanObject,
    mut v_inst_960_: *mut leanh::LeanObject,
    mut v_inst_961_: *mut leanh::LeanObject,
    mut v_aig_962_: *mut leanh::LeanObject,
    mut v_input_963_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_964_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_964_ =
        l_Std_Sat_AIG_mkImpCached___redArg(v_inst_960_, v_inst_961_, v_aig_962_, v_input_963_);
    return v___x_964_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Std_Sat_AIG_CachedGates(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Std_Sat_AIG_CachedLemmas(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Std_Sat_AIG_CachedGates(
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
pub unsafe fn initialize_Std_Sat_AIG_CachedGates(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Std_Sat_AIG_CachedLemmas(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Std_Sat_AIG_CachedGates(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = meta_initialize_Std_Sat_AIG_CachedGates(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return initialize_Std_Sat_AIG_CachedGates(builtin);
}