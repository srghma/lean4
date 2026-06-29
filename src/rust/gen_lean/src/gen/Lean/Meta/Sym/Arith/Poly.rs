// Lean compiler output
// Module: Lean.Meta.Sym.Arith.Poly
// Imports: Init.Grind.Ring.CommSolver Init.Data.Nat.Gcd Init.Data.Nat.Lemmas Init.Data.Nat.Linear Init.WFTactics
use crate::ffi::{
    lean_int_dec_eq, lean_int_ediv, lean_int_neg, lean_nat_abs, lean_nat_add, lean_nat_dec_eq,
    lean_nat_dec_le, lean_nat_dec_lt, lean_nat_gcd, lean_nat_sub, lean_nat_to_int,
};
use crate::r#gen::Init::Data::Nat::Gcd::{
    initialize_Init_Data_Nat_Gcd, runtime_initialize_Init_Data_Nat_Gcd,
};
use crate::r#gen::Init::Data::Nat::Lemmas::{
    initialize_Init_Data_Nat_Lemmas, runtime_initialize_Init_Data_Nat_Lemmas,
};
use crate::r#gen::Init::Data::Nat::Linear::{
    initialize_Init_Data_Nat_Linear, runtime_initialize_Init_Data_Nat_Linear,
};
use crate::r#gen::Init::Grind::Ring::CommSolver::{
    initialize_Init_Grind_Ring_CommSolver, l_Lean_Grind_CommRing_Mon_degree,
    l_Lean_Grind_CommRing_Mon_degreeOf, l_Lean_Grind_CommRing_Poly_combine,
    l_Lean_Grind_CommRing_Poly_combineC, l_Lean_Grind_CommRing_Poly_mulConst,
    l_Lean_Grind_CommRing_Poly_mulConstC, l_Lean_Grind_CommRing_Poly_mulMon,
    l_Lean_Grind_CommRing_Poly_mulMonC, runtime_initialize_Init_Grind_Ring_CommSolver,
};
use crate::r#gen::Init::WFTactics::{initialize_Init_WFTactics, runtime_initialize_Init_WFTactics};
static mut l_Lean_Grind_CommRing_Poly_spol___closed__0_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Grind_CommRing_Poly_spol___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Grind_CommRing_Poly_spol___closed__1_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Grind_CommRing_Poly_spol___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Grind_CommRing_Poly_spol___closed__2_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Grind_CommRing_Poly_spol___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Grind_CommRing_Mon_toExpr___closed__0_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Grind_CommRing_Mon_toExpr___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Grind_CommRing_Mon_toExpr___closed__1_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Grind_CommRing_Mon_toExpr___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub unsafe fn l_Lean_Grind_CommRing_Mon_sharesVar(
    mut v_x_503_: *mut crate::leanh::LeanObject,
    mut v_x_504_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_505_: u8 = 0;
    let mut v___x_506_: u8 = 0;
    let mut v_p_507_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_p_508_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_m_509_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_m_510_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_x_511_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_x_512_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_513_: u8 = 0;
    let mut v___x_514_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_503_) == 0 {
                    v___x_505_ = 0;
                    return v___x_505_;
                } else {
                    if crate::leanh::lean_obj_tag(v_x_504_) == 0 {
                        v___x_506_ = 0;
                        return v___x_506_;
                    } else {
                        v_p_507_ = crate::leanh::lean_ctor_get(v_x_503_, 0);
                        v_p_508_ = crate::leanh::lean_ctor_get(v_x_504_, 0);
                        v_m_509_ = crate::leanh::lean_ctor_get(v_x_503_, 1);
                        v_m_510_ = crate::leanh::lean_ctor_get(v_x_504_, 1);
                        v_x_511_ = crate::leanh::lean_ctor_get(v_p_507_, 0);
                        v_x_512_ = crate::leanh::lean_ctor_get(v_p_508_, 0);
                        v___x_513_ = lean_nat_dec_lt(v_x_511_, v_x_512_);
                        if v___x_513_ == 0 {
                            v___x_514_ = lean_nat_dec_eq(v_x_511_, v_x_512_);
                            if v___x_514_ == 0 {
                                v_x_504_ = v_m_510_;
                                state = 0;
                                continue;
                            } else {
                                return v___x_514_;
                            }
                        } else {
                            v_x_503_ = v_m_509_;
                            state = 0;
                            continue;
                        }
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Grind_CommRing_Mon_sharesVar___boxed(
    mut v_x_517_: *mut crate::leanh::LeanObject,
    mut v_x_518_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_519_: u8 = 0;
    let mut v_r_520_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_519_ = l_Lean_Grind_CommRing_Mon_sharesVar(v_x_517_, v_x_518_);
    crate::leanh::lean_dec(v_x_518_);
    crate::leanh::lean_dec(v_x_517_);
    v_r_520_ = crate::leanh::lean_box((v_res_519_) as usize);
    return v_r_520_;
}
pub unsafe fn l___private_Lean_Meta_Sym_Arith_Poly_0__Lean_Grind_CommRing_Mon_sharesVar_match__3_splitter___redArg(
    mut v_x_521_: *mut crate::leanh::LeanObject,
    mut v_x_522_: *mut crate::leanh::LeanObject,
    mut v_h__1_523_: *mut crate::leanh::LeanObject,
    mut v_h__2_524_: *mut crate::leanh::LeanObject,
    mut v_h__3_525_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_521_) == 0 {
        let mut v___x_526_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__3_525_);
        crate::leanh::lean_dec(v_h__2_524_);
        v___x_526_ = crate::leanh::lean_apply_1(v_h__1_523_, v_x_522_);
        return v___x_526_;
    } else {
        crate::leanh::lean_dec(v_h__1_523_);
        if crate::leanh::lean_obj_tag(v_x_522_) == 0 {
            let mut v___x_527_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__3_525_);
            v___x_527_ =
                crate::leanh::lean_apply_2(v_h__2_524_, v_x_521_, crate::leanh::lean_box(0));
            return v___x_527_;
        } else {
            let mut v_p_528_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_m_529_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_p_530_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_m_531_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_532_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__2_524_);
            v_p_528_ = crate::leanh::lean_ctor_get(v_x_521_, 0);
            crate::leanh::lean_inc_ref(v_p_528_);
            v_m_529_ = crate::leanh::lean_ctor_get(v_x_521_, 1);
            crate::leanh::lean_inc(v_m_529_);
            crate::leanh::lean_dec_ref_known(v_x_521_, 2);
            v_p_530_ = crate::leanh::lean_ctor_get(v_x_522_, 0);
            crate::leanh::lean_inc_ref(v_p_530_);
            v_m_531_ = crate::leanh::lean_ctor_get(v_x_522_, 1);
            crate::leanh::lean_inc(v_m_531_);
            crate::leanh::lean_dec_ref_known(v_x_522_, 2);
            v___x_532_ =
                crate::leanh::lean_apply_4(v_h__3_525_, v_p_528_, v_m_529_, v_p_530_, v_m_531_);
            return v___x_532_;
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Sym_Arith_Poly_0__Lean_Grind_CommRing_Mon_sharesVar_match__3_splitter(
    mut v_motive_533_: *mut crate::leanh::LeanObject,
    mut v_x_534_: *mut crate::leanh::LeanObject,
    mut v_x_535_: *mut crate::leanh::LeanObject,
    mut v_h__1_536_: *mut crate::leanh::LeanObject,
    mut v_h__2_537_: *mut crate::leanh::LeanObject,
    mut v_h__3_538_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_534_) == 0 {
        let mut v___x_539_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__3_538_);
        crate::leanh::lean_dec(v_h__2_537_);
        v___x_539_ = crate::leanh::lean_apply_1(v_h__1_536_, v_x_535_);
        return v___x_539_;
    } else {
        crate::leanh::lean_dec(v_h__1_536_);
        if crate::leanh::lean_obj_tag(v_x_535_) == 0 {
            let mut v___x_540_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__3_538_);
            v___x_540_ =
                crate::leanh::lean_apply_2(v_h__2_537_, v_x_534_, crate::leanh::lean_box(0));
            return v___x_540_;
        } else {
            let mut v_p_541_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_m_542_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_p_543_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_m_544_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_545_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__2_537_);
            v_p_541_ = crate::leanh::lean_ctor_get(v_x_534_, 0);
            crate::leanh::lean_inc_ref(v_p_541_);
            v_m_542_ = crate::leanh::lean_ctor_get(v_x_534_, 1);
            crate::leanh::lean_inc(v_m_542_);
            crate::leanh::lean_dec_ref_known(v_x_534_, 2);
            v_p_543_ = crate::leanh::lean_ctor_get(v_x_535_, 0);
            crate::leanh::lean_inc_ref(v_p_543_);
            v_m_544_ = crate::leanh::lean_ctor_get(v_x_535_, 1);
            crate::leanh::lean_inc(v_m_544_);
            crate::leanh::lean_dec_ref_known(v_x_535_, 2);
            v___x_545_ =
                crate::leanh::lean_apply_4(v_h__3_538_, v_p_541_, v_m_542_, v_p_543_, v_m_544_);
            return v___x_545_;
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Sym_Arith_Poly_0__Lean_Grind_CommRing_Mon_sharesVar_match__1_splitter___redArg(
    mut v_x_546_: u8,
    mut v_h__1_547_: *mut crate::leanh::LeanObject,
    mut v_h__2_548_: *mut crate::leanh::LeanObject,
    mut v_h__3_549_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    match v_x_546_ {
        0 => {
            let mut v___x_550_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_551_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__3_549_);
            crate::leanh::lean_dec(v_h__1_547_);
            v___x_550_ = crate::leanh::lean_box(0);
            v___x_551_ = crate::leanh::lean_apply_1(v_h__2_548_, v___x_550_);
            return v___x_551_;
        }
        1 => {
            let mut v___x_552_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_553_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__3_549_);
            crate::leanh::lean_dec(v_h__2_548_);
            v___x_552_ = crate::leanh::lean_box(0);
            v___x_553_ = crate::leanh::lean_apply_1(v_h__1_547_, v___x_552_);
            return v___x_553_;
        }
        _ => {
            let mut v___x_554_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_555_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__2_548_);
            crate::leanh::lean_dec(v_h__1_547_);
            v___x_554_ = crate::leanh::lean_box(0);
            v___x_555_ = crate::leanh::lean_apply_1(v_h__3_549_, v___x_554_);
            return v___x_555_;
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Sym_Arith_Poly_0__Lean_Grind_CommRing_Mon_sharesVar_match__1_splitter___redArg___boxed(
    mut v_x_556_: *mut crate::leanh::LeanObject,
    mut v_h__1_557_: *mut crate::leanh::LeanObject,
    mut v_h__2_558_: *mut crate::leanh::LeanObject,
    mut v_h__3_559_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x_36__boxed_560_: u8 = 0;
    let mut v_res_561_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_x_36__boxed_560_ = (crate::leanh::lean_unbox(v_x_556_) as u8);
    v_res_561_ = l___private_Lean_Meta_Sym_Arith_Poly_0__Lean_Grind_CommRing_Mon_sharesVar_match__1_splitter___redArg(v_x_36__boxed_560_, v_h__1_557_, v_h__2_558_, v_h__3_559_);
    return v_res_561_;
}
pub unsafe fn l___private_Lean_Meta_Sym_Arith_Poly_0__Lean_Grind_CommRing_Mon_sharesVar_match__1_splitter(
    mut v_motive_562_: *mut crate::leanh::LeanObject,
    mut v_x_563_: u8,
    mut v_h__1_564_: *mut crate::leanh::LeanObject,
    mut v_h__2_565_: *mut crate::leanh::LeanObject,
    mut v_h__3_566_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    match v_x_563_ {
        0 => {
            let mut v___x_567_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_568_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__3_566_);
            crate::leanh::lean_dec(v_h__1_564_);
            v___x_567_ = crate::leanh::lean_box(0);
            v___x_568_ = crate::leanh::lean_apply_1(v_h__2_565_, v___x_567_);
            return v___x_568_;
        }
        1 => {
            let mut v___x_569_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_570_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__3_566_);
            crate::leanh::lean_dec(v_h__2_565_);
            v___x_569_ = crate::leanh::lean_box(0);
            v___x_570_ = crate::leanh::lean_apply_1(v_h__1_564_, v___x_569_);
            return v___x_570_;
        }
        _ => {
            let mut v___x_571_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_572_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__2_565_);
            crate::leanh::lean_dec(v_h__1_564_);
            v___x_571_ = crate::leanh::lean_box(0);
            v___x_572_ = crate::leanh::lean_apply_1(v_h__3_566_, v___x_571_);
            return v___x_572_;
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Sym_Arith_Poly_0__Lean_Grind_CommRing_Mon_sharesVar_match__1_splitter___boxed(
    mut v_motive_573_: *mut crate::leanh::LeanObject,
    mut v_x_574_: *mut crate::leanh::LeanObject,
    mut v_h__1_575_: *mut crate::leanh::LeanObject,
    mut v_h__2_576_: *mut crate::leanh::LeanObject,
    mut v_h__3_577_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x_51__boxed_578_: u8 = 0;
    let mut v_res_579_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_x_51__boxed_578_ = (crate::leanh::lean_unbox(v_x_574_) as u8);
    v_res_579_ =
        l___private_Lean_Meta_Sym_Arith_Poly_0__Lean_Grind_CommRing_Mon_sharesVar_match__1_splitter(
            v_motive_573_,
            v_x_51__boxed_578_,
            v_h__1_575_,
            v_h__2_576_,
            v_h__3_577_,
        );
    return v_res_579_;
}
pub unsafe fn l_Lean_Grind_CommRing_Mon_lcm(
    mut v_x_580_: *mut crate::leanh::LeanObject,
    mut v_x_581_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_p_582_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_m_583_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_p_584_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_m_585_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_x_586_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_587_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_589_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_590_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_591_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_592_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_x_593_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_594_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_595_: u8 = 0;
    let mut v___x_597_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_598_: u8 = 0;
    let mut v___x_599_: u8 = 0;
    let mut v___x_600_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_602_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_603_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_604_: u8 = 0;
    let mut v_isSharedCheck_605_: u8 = 0;
    let mut v_unused_606_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_607_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_609_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_610_: u8 = 0;
    let mut v___x_611_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_613_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_614_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_615_: u8 = 0;
    let mut v_unused_616_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_617_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_580_) == 0 {
                    return v_x_581_;
                } else {
                    if crate::leanh::lean_obj_tag(v_x_581_) == 0 {
                        return v_x_580_;
                    } else {
                        v_p_582_ = crate::leanh::lean_ctor_get(v_x_580_, 0);
                        v_m_583_ = crate::leanh::lean_ctor_get(v_x_580_, 1);
                        v_p_584_ = crate::leanh::lean_ctor_get(v_x_581_, 0);
                        v_m_585_ = crate::leanh::lean_ctor_get(v_x_581_, 1);
                        v_x_586_ = crate::leanh::lean_ctor_get(v_p_582_, 0);
                        v_k_587_ = crate::leanh::lean_ctor_get(v_p_582_, 1);
                        v_x_593_ = crate::leanh::lean_ctor_get(v_p_584_, 0);
                        v_k_594_ = crate::leanh::lean_ctor_get(v_p_584_, 1);
                        v___x_595_ = lean_nat_dec_lt(v_x_586_, v_x_593_);
                        if v___x_595_ == 0 {
                            crate::leanh::lean_inc(v_m_585_);
                            crate::leanh::lean_inc_ref(v_p_584_);
                            v_isSharedCheck_605_ =
                                (!crate::leanh::lean_is_exclusive(v_x_581_)) as u8;
                            if v_isSharedCheck_605_ == 0 {
                                v_unused_606_ = crate::leanh::lean_ctor_get(v_x_581_, 1);
                                crate::leanh::lean_dec(v_unused_606_);
                                v_unused_607_ = crate::leanh::lean_ctor_get(v_x_581_, 0);
                                crate::leanh::lean_dec(v_unused_607_);
                                v___x_597_ = v_x_581_;
                                v_isShared_598_ = v_isSharedCheck_605_;
                                state = 2;
                                continue;
                            } else {
                                crate::leanh::lean_dec(v_x_581_);
                                v___x_597_ = crate::leanh::lean_box(0);
                                v_isShared_598_ = v_isSharedCheck_605_;
                                state = 2;
                                continue;
                            }
                        } else {
                            crate::leanh::lean_inc(v_m_583_);
                            crate::leanh::lean_inc_ref(v_p_582_);
                            v_isSharedCheck_615_ =
                                (!crate::leanh::lean_is_exclusive(v_x_580_)) as u8;
                            if v_isSharedCheck_615_ == 0 {
                                v_unused_616_ = crate::leanh::lean_ctor_get(v_x_580_, 1);
                                crate::leanh::lean_dec(v_unused_616_);
                                v_unused_617_ = crate::leanh::lean_ctor_get(v_x_580_, 0);
                                crate::leanh::lean_dec(v_unused_617_);
                                v___x_609_ = v_x_580_;
                                v_isShared_610_ = v_isSharedCheck_615_;
                                state = 4;
                                continue;
                            } else {
                                crate::leanh::lean_dec(v_x_580_);
                                v___x_609_ = crate::leanh::lean_box(0);
                                v_isShared_610_ = v_isSharedCheck_615_;
                                state = 4;
                                continue;
                            }
                        }
                    }
                }
            }
            1 => {
                v___x_590_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_590_, 0, v_x_586_);
                crate::leanh::lean_ctor_set(v___x_590_, 1, v___y_589_);
                v___x_591_ = l_Lean_Grind_CommRing_Mon_lcm(v_m_583_, v_m_585_);
                v___x_592_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_592_, 0, v___x_590_);
                crate::leanh::lean_ctor_set(v___x_592_, 1, v___x_591_);
                return v___x_592_;
            }
            2 => {
                v___x_599_ = lean_nat_dec_eq(v_x_586_, v_x_593_);
                if v___x_599_ == 0 {
                    v___x_600_ = l_Lean_Grind_CommRing_Mon_lcm(v_x_580_, v_m_585_);
                    if v_isShared_598_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_597_, 1, v___x_600_);
                        v___x_602_ = v___x_597_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_603_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_603_, 0, v_p_584_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_603_, 1, v___x_600_);
                        v___x_602_ = v_reuseFailAlloc_603_;
                        state = 3;
                        continue;
                    }
                } else {
                    crate::leanh::lean_inc(v_k_594_);
                    crate::leanh::lean_inc(v_k_587_);
                    crate::leanh::lean_inc(v_x_586_);
                    crate::leanh::lean_inc(v_m_583_);
                    crate::leanh::lean_del_object(v___x_597_);
                    crate::leanh::lean_dec_ref(v_p_584_);
                    crate::leanh::lean_dec_ref_known(v_x_580_, 2);
                    v___x_604_ = lean_nat_dec_le(v_k_587_, v_k_594_);
                    if v___x_604_ == 0 {
                        crate::leanh::lean_dec(v_k_594_);
                        v___y_589_ = v_k_587_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v_k_587_);
                        v___y_589_ = v_k_594_;
                        state = 1;
                        continue;
                    }
                }
            }
            3 => {
                return v___x_602_;
            }
            4 => {
                v___x_611_ = l_Lean_Grind_CommRing_Mon_lcm(v_m_583_, v_x_581_);
                if v_isShared_610_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_609_, 1, v___x_611_);
                    v___x_613_ = v___x_609_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_614_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_614_, 0, v_p_582_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_614_, 1, v___x_611_);
                    v___x_613_ = v_reuseFailAlloc_614_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_613_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Grind_CommRing_Mon_divides(
    mut v_x_618_: *mut crate::leanh::LeanObject,
    mut v_x_619_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_620_: u8 = 0;
    let mut v___x_621_: u8 = 0;
    let mut v_p_622_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_p_623_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_m_624_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_m_625_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_x_626_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_627_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_x_628_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_629_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_630_: u8 = 0;
    let mut v___x_631_: u8 = 0;
    let mut v___x_633_: u8 = 0;
    let mut v___x_635_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_618_) == 0 {
                    v___x_620_ = 1;
                    return v___x_620_;
                } else {
                    if crate::leanh::lean_obj_tag(v_x_619_) == 0 {
                        v___x_621_ = 0;
                        return v___x_621_;
                    } else {
                        v_p_622_ = crate::leanh::lean_ctor_get(v_x_618_, 0);
                        v_p_623_ = crate::leanh::lean_ctor_get(v_x_619_, 0);
                        v_m_624_ = crate::leanh::lean_ctor_get(v_x_618_, 1);
                        v_m_625_ = crate::leanh::lean_ctor_get(v_x_619_, 1);
                        v_x_626_ = crate::leanh::lean_ctor_get(v_p_622_, 0);
                        v_k_627_ = crate::leanh::lean_ctor_get(v_p_622_, 1);
                        v_x_628_ = crate::leanh::lean_ctor_get(v_p_623_, 0);
                        v_k_629_ = crate::leanh::lean_ctor_get(v_p_623_, 1);
                        v___x_630_ = lean_nat_dec_lt(v_x_626_, v_x_628_);
                        if v___x_630_ == 0 {
                            v___x_631_ = lean_nat_dec_eq(v_x_626_, v_x_628_);
                            if v___x_631_ == 0 {
                                v_x_619_ = v_m_625_;
                                state = 0;
                                continue;
                            } else {
                                v___x_633_ = lean_nat_dec_le(v_k_627_, v_k_629_);
                                if v___x_633_ == 0 {
                                    return v___x_633_;
                                } else {
                                    v_x_618_ = v_m_624_;
                                    v_x_619_ = v_m_625_;
                                    state = 0;
                                    continue;
                                }
                            }
                        } else {
                            v___x_635_ = 0;
                            return v___x_635_;
                        }
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Grind_CommRing_Mon_divides___boxed(
    mut v_x_636_: *mut crate::leanh::LeanObject,
    mut v_x_637_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_638_: u8 = 0;
    let mut v_r_639_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_638_ = l_Lean_Grind_CommRing_Mon_divides(v_x_636_, v_x_637_);
    crate::leanh::lean_dec(v_x_637_);
    crate::leanh::lean_dec(v_x_636_);
    v_r_639_ = crate::leanh::lean_box((v_res_638_) as usize);
    return v_r_639_;
}
pub unsafe fn l_Lean_Grind_CommRing_Mon_div(
    mut v_x_640_: *mut crate::leanh::LeanObject,
    mut v_x_641_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_p_642_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_p_643_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_m_644_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_m_645_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_647_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_648_: u8 = 0;
    let mut v_x_649_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_650_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_x_651_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_652_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_654_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_655_: u8 = 0;
    let mut v___x_656_: u8 = 0;
    let mut v___x_657_: u8 = 0;
    let mut v___x_658_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_659_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_660_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_661_: u8 = 0;
    let mut v___x_663_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_664_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_666_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_667_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_668_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_670_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_672_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_673_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_674_: u8 = 0;
    let mut v_isSharedCheck_675_: u8 = 0;
    let mut v_unused_676_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_641_) == 0 {
                    return v_x_640_;
                } else {
                    if crate::leanh::lean_obj_tag(v_x_640_) == 0 {
                        crate::leanh::lean_dec_ref_known(v_x_641_, 2);
                        return v_x_640_;
                    } else {
                        v_p_642_ = crate::leanh::lean_ctor_get(v_x_640_, 0);
                        crate::leanh::lean_inc_ref(v_p_642_);
                        v_p_643_ = crate::leanh::lean_ctor_get(v_x_641_, 0);
                        crate::leanh::lean_inc_ref(v_p_643_);
                        v_m_644_ = crate::leanh::lean_ctor_get(v_x_641_, 1);
                        v_m_645_ = crate::leanh::lean_ctor_get(v_x_640_, 1);
                        v_isSharedCheck_675_ = (!crate::leanh::lean_is_exclusive(v_x_640_)) as u8;
                        if v_isSharedCheck_675_ == 0 {
                            v_unused_676_ = crate::leanh::lean_ctor_get(v_x_640_, 0);
                            crate::leanh::lean_dec(v_unused_676_);
                            v___x_647_ = v_x_640_;
                            v_isShared_648_ = v_isSharedCheck_675_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_m_645_);
                            crate::leanh::lean_dec(v_x_640_);
                            v___x_647_ = crate::leanh::lean_box(0);
                            v_isShared_648_ = v_isSharedCheck_675_;
                            state = 1;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v_x_649_ = crate::leanh::lean_ctor_get(v_p_642_, 0);
                v_k_650_ = crate::leanh::lean_ctor_get(v_p_642_, 1);
                v_x_651_ = crate::leanh::lean_ctor_get(v_p_643_, 0);
                v_k_652_ = crate::leanh::lean_ctor_get(v_p_643_, 1);
                v_isSharedCheck_674_ = (!crate::leanh::lean_is_exclusive(v_p_643_)) as u8;
                if v_isSharedCheck_674_ == 0 {
                    v___x_654_ = v_p_643_;
                    v_isShared_655_ = v_isSharedCheck_674_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_k_652_);
                    crate::leanh::lean_inc(v_x_651_);
                    crate::leanh::lean_dec(v_p_643_);
                    v___x_654_ = crate::leanh::lean_box(0);
                    v_isShared_655_ = v_isSharedCheck_674_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_656_ = lean_nat_dec_lt(v_x_649_, v_x_651_);
                if v___x_656_ == 0 {
                    crate::leanh::lean_inc(v_k_650_);
                    crate::leanh::lean_inc(v_x_649_);
                    crate::leanh::lean_inc(v_m_644_);
                    crate::leanh::lean_dec_ref(v_p_642_);
                    crate::leanh::lean_dec_ref_known(v_x_641_, 2);
                    v___x_657_ = lean_nat_dec_eq(v_x_649_, v_x_651_);
                    crate::leanh::lean_dec(v_x_651_);
                    if v___x_657_ == 0 {
                        crate::leanh::lean_del_object(v___x_654_);
                        crate::leanh::lean_dec(v_k_652_);
                        crate::leanh::lean_dec(v_k_650_);
                        crate::leanh::lean_dec(v_x_649_);
                        crate::leanh::lean_del_object(v___x_647_);
                        crate::leanh::lean_dec(v_m_645_);
                        crate::leanh::lean_dec(v_m_644_);
                        v___x_658_ = crate::leanh::lean_box(0);
                        return v___x_658_;
                    } else {
                        v_k_659_ = lean_nat_sub(v_k_650_, v_k_652_);
                        crate::leanh::lean_dec(v_k_652_);
                        crate::leanh::lean_dec(v_k_650_);
                        v___x_660_ = crate::leanh::lean_unsigned_to_nat(0);
                        v___x_661_ = lean_nat_dec_eq(v_k_659_, v___x_660_);
                        if v___x_661_ == 0 {
                            if v_isShared_655_ == 0 {
                                crate::leanh::lean_ctor_set(v___x_654_, 1, v_k_659_);
                                crate::leanh::lean_ctor_set(v___x_654_, 0, v_x_649_);
                                v___x_663_ = v___x_654_;
                                state = 3;
                                continue;
                            } else {
                                v_reuseFailAlloc_668_ =
                                    crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                                crate::leanh::lean_ctor_set(v_reuseFailAlloc_668_, 0, v_x_649_);
                                crate::leanh::lean_ctor_set(v_reuseFailAlloc_668_, 1, v_k_659_);
                                v___x_663_ = v_reuseFailAlloc_668_;
                                state = 3;
                                continue;
                            }
                        } else {
                            crate::leanh::lean_dec(v_k_659_);
                            crate::leanh::lean_del_object(v___x_654_);
                            crate::leanh::lean_dec(v_x_649_);
                            crate::leanh::lean_del_object(v___x_647_);
                            v_x_640_ = v_m_645_;
                            v_x_641_ = v_m_644_;
                            state = 0;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_654_);
                    crate::leanh::lean_dec(v_k_652_);
                    crate::leanh::lean_dec(v_x_651_);
                    v___x_670_ = l_Lean_Grind_CommRing_Mon_div(v_m_645_, v_x_641_);
                    if v_isShared_648_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_647_, 1, v___x_670_);
                        v___x_672_ = v___x_647_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_673_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_673_, 0, v_p_642_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_673_, 1, v___x_670_);
                        v___x_672_ = v_reuseFailAlloc_673_;
                        state = 5;
                        continue;
                    }
                }
            }
            3 => {
                v___x_664_ = l_Lean_Grind_CommRing_Mon_div(v_m_645_, v_m_644_);
                if v_isShared_648_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_647_, 1, v___x_664_);
                    crate::leanh::lean_ctor_set(v___x_647_, 0, v___x_663_);
                    v___x_666_ = v___x_647_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_667_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_667_, 0, v___x_663_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_667_, 1, v___x_664_);
                    v___x_666_ = v_reuseFailAlloc_667_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_666_;
            }
            5 => {
                return v___x_672_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Grind_CommRing_Mon_coprime(
    mut v_x_677_: *mut crate::leanh::LeanObject,
    mut v_x_678_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_679_: u8 = 0;
    let mut v___x_680_: u8 = 0;
    let mut v_p_681_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_p_682_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_m_683_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_m_684_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_x_685_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_x_686_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_687_: u8 = 0;
    let mut v___x_688_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_677_) == 0 {
                    v___x_679_ = 1;
                    return v___x_679_;
                } else {
                    if crate::leanh::lean_obj_tag(v_x_678_) == 0 {
                        v___x_680_ = 1;
                        return v___x_680_;
                    } else {
                        v_p_681_ = crate::leanh::lean_ctor_get(v_x_677_, 0);
                        v_p_682_ = crate::leanh::lean_ctor_get(v_x_678_, 0);
                        v_m_683_ = crate::leanh::lean_ctor_get(v_x_677_, 1);
                        v_m_684_ = crate::leanh::lean_ctor_get(v_x_678_, 1);
                        v_x_685_ = crate::leanh::lean_ctor_get(v_p_681_, 0);
                        v_x_686_ = crate::leanh::lean_ctor_get(v_p_682_, 0);
                        v___x_687_ = lean_nat_dec_lt(v_x_685_, v_x_686_);
                        if v___x_687_ == 0 {
                            v___x_688_ = lean_nat_dec_eq(v_x_685_, v_x_686_);
                            if v___x_688_ == 0 {
                                v_x_678_ = v_m_684_;
                                state = 0;
                                continue;
                            } else {
                                return v___x_687_;
                            }
                        } else {
                            v_x_677_ = v_m_683_;
                            state = 0;
                            continue;
                        }
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Grind_CommRing_Mon_coprime___boxed(
    mut v_x_691_: *mut crate::leanh::LeanObject,
    mut v_x_692_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_693_: u8 = 0;
    let mut v_r_694_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_693_ = l_Lean_Grind_CommRing_Mon_coprime(v_x_691_, v_x_692_);
    crate::leanh::lean_dec(v_x_692_);
    crate::leanh::lean_dec(v_x_691_);
    v_r_694_ = crate::leanh::lean_box((v_res_693_) as usize);
    return v_r_694_;
}
pub unsafe fn l_Lean_Grind_CommRing_Poly_mulConst_x27(
    mut v_p_695_: *mut crate::leanh::LeanObject,
    mut v_k_696_: *mut crate::leanh::LeanObject,
    mut v_char_x3f_697_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_char_x3f_697_) == 1 {
        let mut v_val_698_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_699_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_val_698_ = crate::leanh::lean_ctor_get(v_char_x3f_697_, 0);
        crate::leanh::lean_inc(v_val_698_);
        crate::leanh::lean_dec_ref_known(v_char_x3f_697_, 1);
        v___x_699_ = l_Lean_Grind_CommRing_Poly_mulConstC(v_k_696_, v_p_695_, v_val_698_);
        return v___x_699_;
    } else {
        let mut v___x_700_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_char_x3f_697_);
        v___x_700_ = l_Lean_Grind_CommRing_Poly_mulConst(v_k_696_, v_p_695_);
        return v___x_700_;
    }
}
pub unsafe fn l_Lean_Grind_CommRing_Poly_mulConst_x27___boxed(
    mut v_p_701_: *mut crate::leanh::LeanObject,
    mut v_k_702_: *mut crate::leanh::LeanObject,
    mut v_char_x3f_703_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_704_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_704_ = l_Lean_Grind_CommRing_Poly_mulConst_x27(v_p_701_, v_k_702_, v_char_x3f_703_);
    crate::leanh::lean_dec(v_k_702_);
    return v_res_704_;
}
pub unsafe fn l_Lean_Grind_CommRing_Poly_mulMon_x27(
    mut v_p_705_: *mut crate::leanh::LeanObject,
    mut v_k_706_: *mut crate::leanh::LeanObject,
    mut v_m_707_: *mut crate::leanh::LeanObject,
    mut v_char_x3f_708_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_char_x3f_708_) == 1 {
        let mut v_val_709_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_710_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_val_709_ = crate::leanh::lean_ctor_get(v_char_x3f_708_, 0);
        crate::leanh::lean_inc(v_val_709_);
        crate::leanh::lean_dec_ref_known(v_char_x3f_708_, 1);
        v___x_710_ = l_Lean_Grind_CommRing_Poly_mulMonC(v_k_706_, v_m_707_, v_p_705_, v_val_709_);
        return v___x_710_;
    } else {
        let mut v___x_711_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_char_x3f_708_);
        v___x_711_ = l_Lean_Grind_CommRing_Poly_mulMon(v_k_706_, v_m_707_, v_p_705_);
        return v___x_711_;
    }
}
pub unsafe fn l_Lean_Grind_CommRing_Poly_mulMon_x27___boxed(
    mut v_p_712_: *mut crate::leanh::LeanObject,
    mut v_k_713_: *mut crate::leanh::LeanObject,
    mut v_m_714_: *mut crate::leanh::LeanObject,
    mut v_char_x3f_715_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_716_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_716_ =
        l_Lean_Grind_CommRing_Poly_mulMon_x27(v_p_712_, v_k_713_, v_m_714_, v_char_x3f_715_);
    crate::leanh::lean_dec(v_k_713_);
    return v_res_716_;
}
pub unsafe fn l_Lean_Grind_CommRing_Poly_combine_x27(
    mut v_p_u2081_717_: *mut crate::leanh::LeanObject,
    mut v_p_u2082_718_: *mut crate::leanh::LeanObject,
    mut v_char_x3f_719_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_char_x3f_719_) == 1 {
        let mut v_val_720_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_721_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_val_720_ = crate::leanh::lean_ctor_get(v_char_x3f_719_, 0);
        crate::leanh::lean_inc(v_val_720_);
        crate::leanh::lean_dec_ref_known(v_char_x3f_719_, 1);
        v___x_721_ =
            l_Lean_Grind_CommRing_Poly_combineC(v_p_u2081_717_, v_p_u2082_718_, v_val_720_);
        return v___x_721_;
    } else {
        let mut v___x_722_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_char_x3f_719_);
        v___x_722_ = l_Lean_Grind_CommRing_Poly_combine(v_p_u2081_717_, v_p_u2082_718_);
        return v___x_722_;
    }
}
pub unsafe fn l_Nat_cast___at___00Lean_Grind_CommRing_Poly_spol_spec__0(
    mut v_a_723_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_724_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_724_ = lean_nat_to_int(v_a_723_);
    return v___x_724_;
}
pub unsafe fn _init_l_Lean_Grind_CommRing_Poly_spol___closed__0() -> *mut crate::leanh::LeanObject {
    let mut v___x_725_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_726_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_725_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_726_ = lean_nat_to_int(v___x_725_);
    return v___x_726_;
}
pub unsafe fn _init_l_Lean_Grind_CommRing_Poly_spol___closed__1() -> *mut crate::leanh::LeanObject {
    let mut v___x_727_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_728_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_727_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Grind_CommRing_Poly_spol___closed__0),
        core::ptr::addr_of_mut!(l_Lean_Grind_CommRing_Poly_spol___closed__0_once),
        _init_l_Lean_Grind_CommRing_Poly_spol___closed__0,
    );
    v___x_728_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_728_, 0, v___x_727_);
    return v___x_728_;
}
pub unsafe fn _init_l_Lean_Grind_CommRing_Poly_spol___closed__2() -> *mut crate::leanh::LeanObject {
    let mut v___x_729_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_730_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_731_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_732_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_729_ = crate::leanh::lean_box(0);
    v___x_730_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Grind_CommRing_Poly_spol___closed__0),
        core::ptr::addr_of_mut!(l_Lean_Grind_CommRing_Poly_spol___closed__0_once),
        _init_l_Lean_Grind_CommRing_Poly_spol___closed__0,
    );
    v___x_731_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Grind_CommRing_Poly_spol___closed__1),
        core::ptr::addr_of_mut!(l_Lean_Grind_CommRing_Poly_spol___closed__1_once),
        _init_l_Lean_Grind_CommRing_Poly_spol___closed__1,
    );
    v___x_732_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_732_, 0, v___x_731_);
    crate::leanh::lean_ctor_set(v___x_732_, 1, v___x_730_);
    crate::leanh::lean_ctor_set(v___x_732_, 2, v___x_729_);
    crate::leanh::lean_ctor_set(v___x_732_, 3, v___x_730_);
    crate::leanh::lean_ctor_set(v___x_732_, 4, v___x_729_);
    return v___x_732_;
}
pub unsafe fn l_Lean_Grind_CommRing_Poly_spol(
    mut v_p_u2081_733_: *mut crate::leanh::LeanObject,
    mut v_p_u2082_734_: *mut crate::leanh::LeanObject,
    mut v_char_x3f_735_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_737_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_738_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_739_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_p_740_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_741_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_742_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_p_743_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_m_744_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_m_u2081_745_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_m_u2082_746_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_747_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_748_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_g_749_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_750_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_c_u2081_751_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_752_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_c_u2082_753_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_p_u2081_754_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_p_u2082_755_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_spol_756_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_757_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_p_u2081_733_) == 1 {
                    if crate::leanh::lean_obj_tag(v_p_u2082_734_) == 1 {
                        v_k_738_ = crate::leanh::lean_ctor_get(v_p_u2081_733_, 0);
                        crate::leanh::lean_inc(v_k_738_);
                        v_v_739_ = crate::leanh::lean_ctor_get(v_p_u2081_733_, 1);
                        crate::leanh::lean_inc_n(v_v_739_, 2);
                        v_p_740_ = crate::leanh::lean_ctor_get(v_p_u2081_733_, 2);
                        crate::leanh::lean_inc_ref(v_p_740_);
                        crate::leanh::lean_dec_ref_known(v_p_u2081_733_, 3);
                        v_k_741_ = crate::leanh::lean_ctor_get(v_p_u2082_734_, 0);
                        crate::leanh::lean_inc(v_k_741_);
                        v_v_742_ = crate::leanh::lean_ctor_get(v_p_u2082_734_, 1);
                        crate::leanh::lean_inc_n(v_v_742_, 2);
                        v_p_743_ = crate::leanh::lean_ctor_get(v_p_u2082_734_, 2);
                        crate::leanh::lean_inc_ref(v_p_743_);
                        crate::leanh::lean_dec_ref_known(v_p_u2082_734_, 3);
                        v_m_744_ = l_Lean_Grind_CommRing_Mon_lcm(v_v_739_, v_v_742_);
                        crate::leanh::lean_inc(v_m_744_);
                        v_m_u2081_745_ = l_Lean_Grind_CommRing_Mon_div(v_m_744_, v_v_739_);
                        v_m_u2082_746_ = l_Lean_Grind_CommRing_Mon_div(v_m_744_, v_v_742_);
                        v___x_747_ = lean_nat_abs(v_k_738_);
                        v___x_748_ = lean_nat_abs(v_k_741_);
                        v_g_749_ = lean_nat_gcd(v___x_747_, v___x_748_);
                        crate::leanh::lean_dec(v___x_748_);
                        crate::leanh::lean_dec(v___x_747_);
                        v___x_750_ = lean_nat_to_int(v_g_749_);
                        v_c_u2081_751_ = lean_int_ediv(v_k_741_, v___x_750_);
                        crate::leanh::lean_dec(v_k_741_);
                        v___x_752_ = lean_int_neg(v_k_738_);
                        crate::leanh::lean_dec(v_k_738_);
                        v_c_u2082_753_ = lean_int_ediv(v___x_752_, v___x_750_);
                        crate::leanh::lean_dec(v___x_750_);
                        crate::leanh::lean_dec(v___x_752_);
                        crate::leanh::lean_inc_n(v_char_x3f_735_, 2);
                        crate::leanh::lean_inc(v_m_u2081_745_);
                        v_p_u2081_754_ = l_Lean_Grind_CommRing_Poly_mulMon_x27(
                            v_p_740_,
                            v_c_u2081_751_,
                            v_m_u2081_745_,
                            v_char_x3f_735_,
                        );
                        crate::leanh::lean_inc(v_m_u2082_746_);
                        v_p_u2082_755_ = l_Lean_Grind_CommRing_Poly_mulMon_x27(
                            v_p_743_,
                            v_c_u2082_753_,
                            v_m_u2082_746_,
                            v_char_x3f_735_,
                        );
                        v_spol_756_ = l_Lean_Grind_CommRing_Poly_combine_x27(
                            v_p_u2081_754_,
                            v_p_u2082_755_,
                            v_char_x3f_735_,
                        );
                        v___x_757_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_757_, 0, v_spol_756_);
                        crate::leanh::lean_ctor_set(v___x_757_, 1, v_c_u2081_751_);
                        crate::leanh::lean_ctor_set(v___x_757_, 2, v_m_u2081_745_);
                        crate::leanh::lean_ctor_set(v___x_757_, 3, v_c_u2082_753_);
                        crate::leanh::lean_ctor_set(v___x_757_, 4, v_m_u2082_746_);
                        return v___x_757_;
                    } else {
                        crate::leanh::lean_dec_ref_known(v_p_u2081_733_, 3);
                        crate::leanh::lean_dec(v_char_x3f_735_);
                        crate::leanh::lean_dec_ref(v_p_u2082_734_);
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_char_x3f_735_);
                    crate::leanh::lean_dec_ref(v_p_u2082_734_);
                    crate::leanh::lean_dec_ref(v_p_u2081_733_);
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_737_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_Grind_CommRing_Poly_spol___closed__2),
                    core::ptr::addr_of_mut!(l_Lean_Grind_CommRing_Poly_spol___closed__2_once),
                    _init_l_Lean_Grind_CommRing_Poly_spol___closed__2,
                );
                return v___x_737_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Grind_CommRing_Poly_degree(
    mut v_x_758_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_758_) == 0 {
        let mut v___x_759_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_759_ = crate::leanh::lean_unsigned_to_nat(0);
        return v___x_759_;
    } else {
        let mut v_v_760_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_761_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_v_760_ = crate::leanh::lean_ctor_get(v_x_758_, 1);
        v___x_761_ = l_Lean_Grind_CommRing_Mon_degree(v_v_760_);
        return v___x_761_;
    }
}
pub unsafe fn l_Lean_Grind_CommRing_Poly_degree___boxed(
    mut v_x_762_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_763_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_763_ = l_Lean_Grind_CommRing_Poly_degree(v_x_762_);
    crate::leanh::lean_dec_ref(v_x_762_);
    return v_res_763_;
}
pub unsafe fn l___private_Lean_Meta_Sym_Arith_Poly_0__Lean_Grind_CommRing_Poly_numTerms_go(
    mut v_p_764_: *mut crate::leanh::LeanObject,
    mut v_acc_765_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_p_766_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_767_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_768_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_p_764_) == 0 {
                    return v_acc_765_;
                } else {
                    v_p_766_ = crate::leanh::lean_ctor_get(v_p_764_, 2);
                    v___x_767_ = crate::leanh::lean_unsigned_to_nat(1);
                    v___x_768_ = lean_nat_add(v_acc_765_, v___x_767_);
                    crate::leanh::lean_dec(v_acc_765_);
                    v_p_764_ = v_p_766_;
                    v_acc_765_ = v___x_768_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Sym_Arith_Poly_0__Lean_Grind_CommRing_Poly_numTerms_go___boxed(
    mut v_p_770_: *mut crate::leanh::LeanObject,
    mut v_acc_771_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_772_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_772_ = l___private_Lean_Meta_Sym_Arith_Poly_0__Lean_Grind_CommRing_Poly_numTerms_go(
        v_p_770_, v_acc_771_,
    );
    crate::leanh::lean_dec_ref(v_p_770_);
    return v_res_772_;
}
pub unsafe fn l_Lean_Grind_CommRing_Poly_numTerms(
    mut v_p_773_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_774_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_775_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_774_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_775_ = l___private_Lean_Meta_Sym_Arith_Poly_0__Lean_Grind_CommRing_Poly_numTerms_go(
        v_p_773_, v___x_774_,
    );
    return v___x_775_;
}
pub unsafe fn l_Lean_Grind_CommRing_Poly_numTerms___boxed(
    mut v_p_776_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_777_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_777_ = l_Lean_Grind_CommRing_Poly_numTerms(v_p_776_);
    crate::leanh::lean_dec_ref(v_p_776_);
    return v_res_777_;
}
pub unsafe fn l_Lean_Grind_CommRing_Poly_divides(
    mut v_p_778_: *mut crate::leanh::LeanObject,
    mut v_m_779_: *mut crate::leanh::LeanObject,
) -> u8 {
    if crate::leanh::lean_obj_tag(v_p_778_) == 0 {
        let mut v___x_780_: u8 = 0;
        v___x_780_ = 1;
        return v___x_780_;
    } else {
        let mut v_v_781_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_782_: u8 = 0;
        v_v_781_ = crate::leanh::lean_ctor_get(v_p_778_, 1);
        v___x_782_ = l_Lean_Grind_CommRing_Mon_divides(v_v_781_, v_m_779_);
        return v___x_782_;
    }
}
pub unsafe fn l_Lean_Grind_CommRing_Poly_divides___boxed(
    mut v_p_783_: *mut crate::leanh::LeanObject,
    mut v_m_784_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_785_: u8 = 0;
    let mut v_r_786_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_785_ = l_Lean_Grind_CommRing_Poly_divides(v_p_783_, v_m_784_);
    crate::leanh::lean_dec(v_m_784_);
    crate::leanh::lean_dec_ref(v_p_783_);
    v_r_786_ = crate::leanh::lean_box((v_res_785_) as usize);
    return v_r_786_;
}
pub unsafe fn l_Lean_Grind_CommRing_Poly_lc(
    mut v_x_787_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_k_788_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_k_788_ = crate::leanh::lean_ctor_get(v_x_787_, 0);
    crate::leanh::lean_inc(v_k_788_);
    return v_k_788_;
}
pub unsafe fn l_Lean_Grind_CommRing_Poly_lc___boxed(
    mut v_x_789_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_790_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_790_ = l_Lean_Grind_CommRing_Poly_lc(v_x_789_);
    crate::leanh::lean_dec_ref(v_x_789_);
    return v_res_790_;
}
pub unsafe fn l_Lean_Grind_CommRing_Poly_lm(
    mut v_x_791_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_791_) == 0 {
        let mut v___x_792_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_792_ = crate::leanh::lean_box(0);
        return v___x_792_;
    } else {
        let mut v_v_793_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_v_793_ = crate::leanh::lean_ctor_get(v_x_791_, 1);
        crate::leanh::lean_inc(v_v_793_);
        return v_v_793_;
    }
}
pub unsafe fn l_Lean_Grind_CommRing_Poly_lm___boxed(
    mut v_x_794_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_795_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_795_ = l_Lean_Grind_CommRing_Poly_lm(v_x_794_);
    crate::leanh::lean_dec_ref(v_x_794_);
    return v_res_795_;
}
pub unsafe fn l_Lean_Grind_CommRing_Poly_isZero(mut v_x_796_: *mut crate::leanh::LeanObject) -> u8 {
    if crate::leanh::lean_obj_tag(v_x_796_) == 0 {
        let mut v_k_797_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_798_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_799_: u8 = 0;
        v_k_797_ = crate::leanh::lean_ctor_get(v_x_796_, 0);
        v___x_798_ = crate::leanh::lean_obj_once(
            core::ptr::addr_of_mut!(l_Lean_Grind_CommRing_Poly_spol___closed__0),
            core::ptr::addr_of_mut!(l_Lean_Grind_CommRing_Poly_spol___closed__0_once),
            _init_l_Lean_Grind_CommRing_Poly_spol___closed__0,
        );
        v___x_799_ = lean_int_dec_eq(v_k_797_, v___x_798_);
        return v___x_799_;
    } else {
        let mut v___x_800_: u8 = 0;
        v___x_800_ = 0;
        return v___x_800_;
    }
}
pub unsafe fn l_Lean_Grind_CommRing_Poly_isZero___boxed(
    mut v_x_801_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_802_: u8 = 0;
    let mut v_r_803_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_802_ = l_Lean_Grind_CommRing_Poly_isZero(v_x_801_);
    crate::leanh::lean_dec_ref(v_x_801_);
    v_r_803_ = crate::leanh::lean_box((v_res_802_) as usize);
    return v_r_803_;
}
pub unsafe fn l_Lean_Grind_CommRing_Poly_getConst(
    mut v_x_804_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_k_805_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_p_806_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_804_) == 0 {
                    v_k_805_ = crate::leanh::lean_ctor_get(v_x_804_, 0);
                    crate::leanh::lean_inc(v_k_805_);
                    return v_k_805_;
                } else {
                    v_p_806_ = crate::leanh::lean_ctor_get(v_x_804_, 2);
                    v_x_804_ = v_p_806_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Grind_CommRing_Poly_getConst___boxed(
    mut v_x_808_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_809_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_809_ = l_Lean_Grind_CommRing_Poly_getConst(v_x_808_);
    crate::leanh::lean_dec_ref(v_x_808_);
    return v_res_809_;
}
pub unsafe fn l_Lean_Grind_CommRing_Poly_checkCoeffs(
    mut v_x_810_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_811_: u8 = 0;
    let mut v_k_812_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_p_813_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_814_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_815_: u8 = 0;
    let mut v___x_817_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_810_) == 0 {
                    v___x_811_ = 1;
                    return v___x_811_;
                } else {
                    v_k_812_ = crate::leanh::lean_ctor_get(v_x_810_, 0);
                    v_p_813_ = crate::leanh::lean_ctor_get(v_x_810_, 2);
                    v___x_814_ = crate::leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(l_Lean_Grind_CommRing_Poly_spol___closed__0),
                        core::ptr::addr_of_mut!(l_Lean_Grind_CommRing_Poly_spol___closed__0_once),
                        _init_l_Lean_Grind_CommRing_Poly_spol___closed__0,
                    );
                    v___x_815_ = lean_int_dec_eq(v_k_812_, v___x_814_);
                    if v___x_815_ == 0 {
                        v_x_810_ = v_p_813_;
                        state = 0;
                        continue;
                    } else {
                        v___x_817_ = 0;
                        return v___x_817_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Grind_CommRing_Poly_checkCoeffs___boxed(
    mut v_x_818_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_819_: u8 = 0;
    let mut v_r_820_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_819_ = l_Lean_Grind_CommRing_Poly_checkCoeffs(v_x_818_);
    crate::leanh::lean_dec_ref(v_x_818_);
    v_r_820_ = crate::leanh::lean_box((v_res_819_) as usize);
    return v_r_820_;
}
pub unsafe fn l_Lean_Grind_CommRing_Poly_checkNoUnitMon(
    mut v_x_821_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_822_: u8 = 0;
    let mut v_v_823_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_824_: u8 = 0;
    let mut v_p_825_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_821_) == 0 {
                    v___x_822_ = 1;
                    return v___x_822_;
                } else {
                    v_v_823_ = crate::leanh::lean_ctor_get(v_x_821_, 1);
                    if crate::leanh::lean_obj_tag(v_v_823_) == 0 {
                        v___x_824_ = 0;
                        return v___x_824_;
                    } else {
                        v_p_825_ = crate::leanh::lean_ctor_get(v_x_821_, 2);
                        v_x_821_ = v_p_825_;
                        state = 0;
                        continue;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Grind_CommRing_Poly_checkNoUnitMon___boxed(
    mut v_x_827_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_828_: u8 = 0;
    let mut v_r_829_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_828_ = l_Lean_Grind_CommRing_Poly_checkNoUnitMon(v_x_827_);
    crate::leanh::lean_dec_ref(v_x_827_);
    v_r_829_ = crate::leanh::lean_box((v_res_828_) as usize);
    return v_r_829_;
}
pub unsafe fn l___private_Lean_Meta_Sym_Arith_Poly_0__Lean_Grind_CommRing_Poly_gcdCoeffs_go(
    mut v_p_830_: *mut crate::leanh::LeanObject,
    mut v_acc_831_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_832_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_833_: u8 = 0;
    let mut v_k_834_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_835_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_836_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_837_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_p_838_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_839_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_840_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_832_ = crate::leanh::lean_unsigned_to_nat(1);
                v___x_833_ = lean_nat_dec_eq(v_acc_831_, v___x_832_);
                if v___x_833_ == 0 {
                    if crate::leanh::lean_obj_tag(v_p_830_) == 0 {
                        v_k_834_ = crate::leanh::lean_ctor_get(v_p_830_, 0);
                        v___x_835_ = lean_nat_abs(v_k_834_);
                        v___x_836_ = lean_nat_gcd(v_acc_831_, v___x_835_);
                        crate::leanh::lean_dec(v___x_835_);
                        crate::leanh::lean_dec(v_acc_831_);
                        return v___x_836_;
                    } else {
                        v_k_837_ = crate::leanh::lean_ctor_get(v_p_830_, 0);
                        v_p_838_ = crate::leanh::lean_ctor_get(v_p_830_, 2);
                        v___x_839_ = lean_nat_abs(v_k_837_);
                        v___x_840_ = lean_nat_gcd(v_acc_831_, v___x_839_);
                        crate::leanh::lean_dec(v___x_839_);
                        crate::leanh::lean_dec(v_acc_831_);
                        v_p_830_ = v_p_838_;
                        v_acc_831_ = v___x_840_;
                        state = 0;
                        continue;
                    }
                } else {
                    return v_acc_831_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Sym_Arith_Poly_0__Lean_Grind_CommRing_Poly_gcdCoeffs_go___boxed(
    mut v_p_842_: *mut crate::leanh::LeanObject,
    mut v_acc_843_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_844_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_844_ = l___private_Lean_Meta_Sym_Arith_Poly_0__Lean_Grind_CommRing_Poly_gcdCoeffs_go(
        v_p_842_, v_acc_843_,
    );
    crate::leanh::lean_dec_ref(v_p_842_);
    return v_res_844_;
}
pub unsafe fn l_Lean_Grind_CommRing_Poly_gcdCoeffs(
    mut v_x_845_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_845_) == 0 {
        let mut v_k_846_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_847_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_k_846_ = crate::leanh::lean_ctor_get(v_x_845_, 0);
        v___x_847_ = lean_nat_abs(v_k_846_);
        return v___x_847_;
    } else {
        let mut v_k_848_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_p_849_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_850_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_851_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_k_848_ = crate::leanh::lean_ctor_get(v_x_845_, 0);
        v_p_849_ = crate::leanh::lean_ctor_get(v_x_845_, 2);
        v___x_850_ = lean_nat_abs(v_k_848_);
        v___x_851_ = l___private_Lean_Meta_Sym_Arith_Poly_0__Lean_Grind_CommRing_Poly_gcdCoeffs_go(
            v_p_849_, v___x_850_,
        );
        return v___x_851_;
    }
}
pub unsafe fn l_Lean_Grind_CommRing_Poly_gcdCoeffs___boxed(
    mut v_x_852_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_853_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_853_ = l_Lean_Grind_CommRing_Poly_gcdCoeffs(v_x_852_);
    crate::leanh::lean_dec_ref(v_x_852_);
    return v_res_853_;
}
pub unsafe fn l_Lean_Grind_CommRing_Poly_divConst(
    mut v_p_854_: *mut crate::leanh::LeanObject,
    mut v_a_855_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_k_856_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_858_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_859_: u8 = 0;
    let mut v___x_860_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_862_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_863_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_864_: u8 = 0;
    let mut v_k_865_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_866_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_p_867_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_869_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_870_: u8 = 0;
    let mut v___x_871_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_872_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_874_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_875_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_876_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_p_854_) == 0 {
                    v_k_856_ = crate::leanh::lean_ctor_get(v_p_854_, 0);
                    v_isSharedCheck_864_ = (!crate::leanh::lean_is_exclusive(v_p_854_)) as u8;
                    if v_isSharedCheck_864_ == 0 {
                        v___x_858_ = v_p_854_;
                        v_isShared_859_ = v_isSharedCheck_864_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_k_856_);
                        crate::leanh::lean_dec(v_p_854_);
                        v___x_858_ = crate::leanh::lean_box(0);
                        v_isShared_859_ = v_isSharedCheck_864_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_k_865_ = crate::leanh::lean_ctor_get(v_p_854_, 0);
                    v_v_866_ = crate::leanh::lean_ctor_get(v_p_854_, 1);
                    v_p_867_ = crate::leanh::lean_ctor_get(v_p_854_, 2);
                    v_isSharedCheck_876_ = (!crate::leanh::lean_is_exclusive(v_p_854_)) as u8;
                    if v_isSharedCheck_876_ == 0 {
                        v___x_869_ = v_p_854_;
                        v_isShared_870_ = v_isSharedCheck_876_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_p_867_);
                        crate::leanh::lean_inc(v_v_866_);
                        crate::leanh::lean_inc(v_k_865_);
                        crate::leanh::lean_dec(v_p_854_);
                        v___x_869_ = crate::leanh::lean_box(0);
                        v_isShared_870_ = v_isSharedCheck_876_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v___x_860_ = lean_int_ediv(v_k_856_, v_a_855_);
                crate::leanh::lean_dec(v_k_856_);
                if v_isShared_859_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_858_, 0, v___x_860_);
                    v___x_862_ = v___x_858_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_863_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_863_, 0, v___x_860_);
                    v___x_862_ = v_reuseFailAlloc_863_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_862_;
            }
            3 => {
                v___x_871_ = lean_int_ediv(v_k_865_, v_a_855_);
                crate::leanh::lean_dec(v_k_865_);
                v___x_872_ = l_Lean_Grind_CommRing_Poly_divConst(v_p_867_, v_a_855_);
                if v_isShared_870_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_869_, 2, v___x_872_);
                    crate::leanh::lean_ctor_set(v___x_869_, 0, v___x_871_);
                    v___x_874_ = v___x_869_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_875_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_875_, 0, v___x_871_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_875_, 1, v_v_866_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_875_, 2, v___x_872_);
                    v___x_874_ = v_reuseFailAlloc_875_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_874_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Grind_CommRing_Poly_divConst___boxed(
    mut v_p_877_: *mut crate::leanh::LeanObject,
    mut v_a_878_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_879_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_879_ = l_Lean_Grind_CommRing_Poly_divConst(v_p_877_, v_a_878_);
    crate::leanh::lean_dec(v_a_878_);
    return v_res_879_;
}
pub unsafe fn l_Lean_Grind_CommRing_Mon_size(
    mut v_x_880_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_880_) == 0 {
        let mut v___x_881_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_881_ = crate::leanh::lean_unsigned_to_nat(0);
        return v___x_881_;
    } else {
        let mut v_m_882_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_883_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_884_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_885_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_m_882_ = crate::leanh::lean_ctor_get(v_x_880_, 1);
        v___x_883_ = l_Lean_Grind_CommRing_Mon_size(v_m_882_);
        v___x_884_ = crate::leanh::lean_unsigned_to_nat(1);
        v___x_885_ = lean_nat_add(v___x_883_, v___x_884_);
        crate::leanh::lean_dec(v___x_883_);
        return v___x_885_;
    }
}
pub unsafe fn l_Lean_Grind_CommRing_Mon_size___boxed(
    mut v_x_886_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_887_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_887_ = l_Lean_Grind_CommRing_Mon_size(v_x_886_);
    crate::leanh::lean_dec(v_x_886_);
    return v_res_887_;
}
pub unsafe fn l_Lean_Grind_CommRing_Poly_size(
    mut v_x_888_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_888_) == 0 {
        let mut v___x_889_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_889_ = crate::leanh::lean_unsigned_to_nat(1);
        return v___x_889_;
    } else {
        let mut v_v_890_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_p_891_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_892_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_893_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_894_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_895_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_896_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_v_890_ = crate::leanh::lean_ctor_get(v_x_888_, 1);
        v_p_891_ = crate::leanh::lean_ctor_get(v_x_888_, 2);
        v___x_892_ = l_Lean_Grind_CommRing_Mon_size(v_v_890_);
        v___x_893_ = crate::leanh::lean_unsigned_to_nat(1);
        v___x_894_ = lean_nat_add(v___x_892_, v___x_893_);
        crate::leanh::lean_dec(v___x_892_);
        v___x_895_ = l_Lean_Grind_CommRing_Poly_size(v_p_891_);
        v___x_896_ = lean_nat_add(v___x_894_, v___x_895_);
        crate::leanh::lean_dec(v___x_895_);
        crate::leanh::lean_dec(v___x_894_);
        return v___x_896_;
    }
}
pub unsafe fn l_Lean_Grind_CommRing_Poly_size___boxed(
    mut v_x_897_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_898_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_898_ = l_Lean_Grind_CommRing_Poly_size(v_x_897_);
    crate::leanh::lean_dec_ref(v_x_897_);
    return v_res_898_;
}
pub unsafe fn l_Lean_Grind_CommRing_Poly_length(
    mut v_x_899_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_899_) == 0 {
        let mut v___x_900_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_900_ = crate::leanh::lean_unsigned_to_nat(0);
        return v___x_900_;
    } else {
        let mut v_p_901_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_902_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_903_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_904_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_p_901_ = crate::leanh::lean_ctor_get(v_x_899_, 2);
        v___x_902_ = crate::leanh::lean_unsigned_to_nat(1);
        v___x_903_ = l_Lean_Grind_CommRing_Poly_length(v_p_901_);
        v___x_904_ = lean_nat_add(v___x_902_, v___x_903_);
        crate::leanh::lean_dec(v___x_903_);
        return v___x_904_;
    }
}
pub unsafe fn l_Lean_Grind_CommRing_Poly_length___boxed(
    mut v_x_905_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_906_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_906_ = l_Lean_Grind_CommRing_Poly_length(v_x_905_);
    crate::leanh::lean_dec_ref(v_x_905_);
    return v_res_906_;
}
pub unsafe fn l_Lean_Grind_CommRing_Power_toExpr(
    mut v_pw_907_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x_908_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_909_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_911_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_912_: u8 = 0;
    let mut v___x_913_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_914_: u8 = 0;
    let mut v___x_915_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_917_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_918_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_919_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_920_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_x_908_ = crate::leanh::lean_ctor_get(v_pw_907_, 0);
                v_k_909_ = crate::leanh::lean_ctor_get(v_pw_907_, 1);
                v_isSharedCheck_920_ = (!crate::leanh::lean_is_exclusive(v_pw_907_)) as u8;
                if v_isSharedCheck_920_ == 0 {
                    v___x_911_ = v_pw_907_;
                    v_isShared_912_ = v_isSharedCheck_920_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_k_909_);
                    crate::leanh::lean_inc(v_x_908_);
                    crate::leanh::lean_dec(v_pw_907_);
                    v___x_911_ = crate::leanh::lean_box(0);
                    v_isShared_912_ = v_isSharedCheck_920_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_913_ = crate::leanh::lean_unsigned_to_nat(1);
                v___x_914_ = lean_nat_dec_eq(v_k_909_, v___x_913_);
                if v___x_914_ == 0 {
                    v___x_915_ = crate::leanh::lean_alloc_ctor(3, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_915_, 0, v_x_908_);
                    if v_isShared_912_ == 0 {
                        crate::leanh::lean_ctor_set_tag(v___x_911_, 8);
                        crate::leanh::lean_ctor_set(v___x_911_, 0, v___x_915_);
                        v___x_917_ = v___x_911_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_918_ = crate::leanh::lean_alloc_ctor(8, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_918_, 0, v___x_915_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_918_, 1, v_k_909_);
                        v___x_917_ = v_reuseFailAlloc_918_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_911_);
                    crate::leanh::lean_dec(v_k_909_);
                    v___x_919_ = crate::leanh::lean_alloc_ctor(3, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_919_, 0, v_x_908_);
                    return v___x_919_;
                }
            }
            2 => {
                return v___x_917_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Sym_Arith_Poly_0__Lean_Grind_CommRing_Mon_toExpr_go(
    mut v_m_921_: *mut crate::leanh::LeanObject,
    mut v_acc_922_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_p_923_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_m_924_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_926_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_927_: u8 = 0;
    let mut v___x_928_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_930_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_932_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_933_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_m_921_) == 0 {
                    return v_acc_922_;
                } else {
                    v_p_923_ = crate::leanh::lean_ctor_get(v_m_921_, 0);
                    v_m_924_ = crate::leanh::lean_ctor_get(v_m_921_, 1);
                    v_isSharedCheck_933_ = (!crate::leanh::lean_is_exclusive(v_m_921_)) as u8;
                    if v_isSharedCheck_933_ == 0 {
                        v___x_926_ = v_m_921_;
                        v_isShared_927_ = v_isSharedCheck_933_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_m_924_);
                        crate::leanh::lean_inc(v_p_923_);
                        crate::leanh::lean_dec(v_m_921_);
                        v___x_926_ = crate::leanh::lean_box(0);
                        v_isShared_927_ = v_isSharedCheck_933_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_928_ = l_Lean_Grind_CommRing_Power_toExpr(v_p_923_);
                if v_isShared_927_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_926_, 7);
                    crate::leanh::lean_ctor_set(v___x_926_, 1, v___x_928_);
                    crate::leanh::lean_ctor_set(v___x_926_, 0, v_acc_922_);
                    v___x_930_ = v___x_926_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_932_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_932_, 0, v_acc_922_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_932_, 1, v___x_928_);
                    v___x_930_ = v_reuseFailAlloc_932_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v_m_921_ = v_m_924_;
                v_acc_922_ = v___x_930_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn _init_l_Lean_Grind_CommRing_Mon_toExpr___closed__0() -> *mut crate::leanh::LeanObject
{
    let mut v___x_934_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_935_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_934_ = crate::leanh::lean_unsigned_to_nat(1);
    v___x_935_ = lean_nat_to_int(v___x_934_);
    return v___x_935_;
}
pub unsafe fn _init_l_Lean_Grind_CommRing_Mon_toExpr___closed__1() -> *mut crate::leanh::LeanObject
{
    let mut v___x_936_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_937_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_936_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Grind_CommRing_Mon_toExpr___closed__0),
        core::ptr::addr_of_mut!(l_Lean_Grind_CommRing_Mon_toExpr___closed__0_once),
        _init_l_Lean_Grind_CommRing_Mon_toExpr___closed__0,
    );
    v___x_937_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_937_, 0, v___x_936_);
    return v___x_937_;
}
pub unsafe fn l_Lean_Grind_CommRing_Mon_toExpr(
    mut v_m_938_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_m_938_) == 0 {
        let mut v___x_939_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_939_ = crate::leanh::lean_obj_once(
            core::ptr::addr_of_mut!(l_Lean_Grind_CommRing_Mon_toExpr___closed__1),
            core::ptr::addr_of_mut!(l_Lean_Grind_CommRing_Mon_toExpr___closed__1_once),
            _init_l_Lean_Grind_CommRing_Mon_toExpr___closed__1,
        );
        return v___x_939_;
    } else {
        let mut v_p_940_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_m_941_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_942_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_943_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_p_940_ = crate::leanh::lean_ctor_get(v_m_938_, 0);
        crate::leanh::lean_inc_ref(v_p_940_);
        v_m_941_ = crate::leanh::lean_ctor_get(v_m_938_, 1);
        crate::leanh::lean_inc(v_m_941_);
        crate::leanh::lean_dec_ref_known(v_m_938_, 2);
        v___x_942_ = l_Lean_Grind_CommRing_Power_toExpr(v_p_940_);
        v___x_943_ = l___private_Lean_Meta_Sym_Arith_Poly_0__Lean_Grind_CommRing_Mon_toExpr_go(
            v_m_941_, v___x_942_,
        );
        return v___x_943_;
    }
}
pub unsafe fn l___private_Lean_Meta_Sym_Arith_Poly_0__Lean_Grind_CommRing_Poly_toExpr_goTerm(
    mut v_k_944_: *mut crate::leanh::LeanObject,
    mut v_m_945_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_946_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_947_: u8 = 0;
    v___x_946_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Grind_CommRing_Mon_toExpr___closed__0),
        core::ptr::addr_of_mut!(l_Lean_Grind_CommRing_Mon_toExpr___closed__0_once),
        _init_l_Lean_Grind_CommRing_Mon_toExpr___closed__0,
    );
    v___x_947_ = lean_int_dec_eq(v_k_944_, v___x_946_);
    if v___x_947_ == 0 {
        let mut v___x_948_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_949_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_950_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_948_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_948_, 0, v_k_944_);
        v___x_949_ = l_Lean_Grind_CommRing_Mon_toExpr(v_m_945_);
        v___x_950_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_950_, 0, v___x_948_);
        crate::leanh::lean_ctor_set(v___x_950_, 1, v___x_949_);
        return v___x_950_;
    } else {
        let mut v___x_951_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_k_944_);
        v___x_951_ = l_Lean_Grind_CommRing_Mon_toExpr(v_m_945_);
        return v___x_951_;
    }
}
pub unsafe fn l___private_Lean_Meta_Sym_Arith_Poly_0__Lean_Grind_CommRing_Poly_toExpr_go(
    mut v_p_952_: *mut crate::leanh::LeanObject,
    mut v_acc_953_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_k_954_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_956_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_957_: u8 = 0;
    let mut v___x_958_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_959_: u8 = 0;
    let mut v___x_961_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_962_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_963_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_964_: u8 = 0;
    let mut v_k_965_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_966_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_p_967_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_968_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_969_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_p_952_) == 0 {
                    v_k_954_ = crate::leanh::lean_ctor_get(v_p_952_, 0);
                    v_isSharedCheck_964_ = (!crate::leanh::lean_is_exclusive(v_p_952_)) as u8;
                    if v_isSharedCheck_964_ == 0 {
                        v___x_956_ = v_p_952_;
                        v_isShared_957_ = v_isSharedCheck_964_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_k_954_);
                        crate::leanh::lean_dec(v_p_952_);
                        v___x_956_ = crate::leanh::lean_box(0);
                        v_isShared_957_ = v_isSharedCheck_964_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_k_965_ = crate::leanh::lean_ctor_get(v_p_952_, 0);
                    crate::leanh::lean_inc(v_k_965_);
                    v_v_966_ = crate::leanh::lean_ctor_get(v_p_952_, 1);
                    crate::leanh::lean_inc(v_v_966_);
                    v_p_967_ = crate::leanh::lean_ctor_get(v_p_952_, 2);
                    crate::leanh::lean_inc_ref(v_p_967_);
                    crate::leanh::lean_dec_ref_known(v_p_952_, 3);
                    v___x_968_ = l___private_Lean_Meta_Sym_Arith_Poly_0__Lean_Grind_CommRing_Poly_toExpr_goTerm(v_k_965_, v_v_966_);
                    v___x_969_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_969_, 0, v_acc_953_);
                    crate::leanh::lean_ctor_set(v___x_969_, 1, v___x_968_);
                    v_p_952_ = v_p_967_;
                    v_acc_953_ = v___x_969_;
                    state = 0;
                    continue;
                }
            }
            1 => {
                v___x_958_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_Grind_CommRing_Poly_spol___closed__0),
                    core::ptr::addr_of_mut!(l_Lean_Grind_CommRing_Poly_spol___closed__0_once),
                    _init_l_Lean_Grind_CommRing_Poly_spol___closed__0,
                );
                v___x_959_ = lean_int_dec_eq(v_k_954_, v___x_958_);
                if v___x_959_ == 0 {
                    if v_isShared_957_ == 0 {
                        v___x_961_ = v___x_956_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_963_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_963_, 0, v_k_954_);
                        v___x_961_ = v_reuseFailAlloc_963_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_956_);
                    crate::leanh::lean_dec(v_k_954_);
                    return v_acc_953_;
                }
            }
            2 => {
                v___x_962_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_962_, 0, v_acc_953_);
                crate::leanh::lean_ctor_set(v___x_962_, 1, v___x_961_);
                return v___x_962_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Grind_CommRing_Poly_toExpr(
    mut v_p_971_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_k_972_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_974_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_975_: u8 = 0;
    let mut v___x_977_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_978_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_979_: u8 = 0;
    let mut v_k_980_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_981_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_p_982_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_983_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_984_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_p_971_) == 0 {
                    v_k_972_ = crate::leanh::lean_ctor_get(v_p_971_, 0);
                    v_isSharedCheck_979_ = (!crate::leanh::lean_is_exclusive(v_p_971_)) as u8;
                    if v_isSharedCheck_979_ == 0 {
                        v___x_974_ = v_p_971_;
                        v_isShared_975_ = v_isSharedCheck_979_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_k_972_);
                        crate::leanh::lean_dec(v_p_971_);
                        v___x_974_ = crate::leanh::lean_box(0);
                        v_isShared_975_ = v_isSharedCheck_979_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_k_980_ = crate::leanh::lean_ctor_get(v_p_971_, 0);
                    crate::leanh::lean_inc(v_k_980_);
                    v_v_981_ = crate::leanh::lean_ctor_get(v_p_971_, 1);
                    crate::leanh::lean_inc(v_v_981_);
                    v_p_982_ = crate::leanh::lean_ctor_get(v_p_971_, 2);
                    crate::leanh::lean_inc_ref(v_p_982_);
                    crate::leanh::lean_dec_ref_known(v_p_971_, 3);
                    v___x_983_ = l___private_Lean_Meta_Sym_Arith_Poly_0__Lean_Grind_CommRing_Poly_toExpr_goTerm(v_k_980_, v_v_981_);
                    v___x_984_ =
                        l___private_Lean_Meta_Sym_Arith_Poly_0__Lean_Grind_CommRing_Poly_toExpr_go(
                            v_p_982_, v___x_983_,
                        );
                    return v___x_984_;
                }
            }
            1 => {
                if v_isShared_975_ == 0 {
                    v___x_977_ = v___x_974_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_978_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_978_, 0, v_k_972_);
                    v___x_977_ = v_reuseFailAlloc_978_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_977_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Sym_Arith_Poly_0__Lean_Grind_CommRing_Poly_maxDegreeOf_go(
    mut v_x_985_: *mut crate::leanh::LeanObject,
    mut v_p_986_: *mut crate::leanh::LeanObject,
    mut v_max_987_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_v_988_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_p_989_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_990_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_991_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_p_986_) == 0 {
                    return v_max_987_;
                } else {
                    v_v_988_ = crate::leanh::lean_ctor_get(v_p_986_, 1);
                    v_p_989_ = crate::leanh::lean_ctor_get(v_p_986_, 2);
                    v___x_990_ = l_Lean_Grind_CommRing_Mon_degreeOf(v_v_988_, v_x_985_);
                    v___x_991_ = lean_nat_dec_le(v_max_987_, v___x_990_);
                    if v___x_991_ == 0 {
                        crate::leanh::lean_dec(v___x_990_);
                        v_p_986_ = v_p_989_;
                        state = 0;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v_max_987_);
                        v_p_986_ = v_p_989_;
                        v_max_987_ = v___x_990_;
                        state = 0;
                        continue;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Sym_Arith_Poly_0__Lean_Grind_CommRing_Poly_maxDegreeOf_go___boxed(
    mut v_x_994_: *mut crate::leanh::LeanObject,
    mut v_p_995_: *mut crate::leanh::LeanObject,
    mut v_max_996_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_997_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_997_ = l___private_Lean_Meta_Sym_Arith_Poly_0__Lean_Grind_CommRing_Poly_maxDegreeOf_go(
        v_x_994_, v_p_995_, v_max_996_,
    );
    crate::leanh::lean_dec_ref(v_p_995_);
    crate::leanh::lean_dec(v_x_994_);
    return v_res_997_;
}
pub unsafe fn l_Lean_Grind_CommRing_Poly_maxDegreeOf(
    mut v_p_998_: *mut crate::leanh::LeanObject,
    mut v_x_999_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1000_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1001_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1000_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_1001_ = l___private_Lean_Meta_Sym_Arith_Poly_0__Lean_Grind_CommRing_Poly_maxDegreeOf_go(
        v_x_999_,
        v_p_998_,
        v___x_1000_,
    );
    return v___x_1001_;
}
pub unsafe fn l_Lean_Grind_CommRing_Poly_maxDegreeOf___boxed(
    mut v_p_1002_: *mut crate::leanh::LeanObject,
    mut v_x_1003_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1004_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1004_ = l_Lean_Grind_CommRing_Poly_maxDegreeOf(v_p_1002_, v_x_1003_);
    crate::leanh::lean_dec(v_x_1003_);
    crate::leanh::lean_dec_ref(v_p_1002_);
    return v_res_1004_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Meta_Sym_Arith_Poly(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Init_Grind_Ring_CommSolver(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Nat_Gcd(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Nat_Lemmas(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Nat_Linear(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_WFTactics(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Meta_Sym_Arith_Poly(
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
pub unsafe fn initialize_Lean_Meta_Sym_Arith_Poly(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Init_Grind_Ring_CommSolver(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Nat_Gcd(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Nat_Lemmas(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Nat_Linear(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_WFTactics(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Sym_Arith_Poly(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_Meta_Sym_Arith_Poly(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Lean_Meta_Sym_Arith_Poly(builtin);
}
