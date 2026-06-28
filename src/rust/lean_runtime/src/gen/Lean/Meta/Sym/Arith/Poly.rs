// Lean compiler output
// Module: Lean.Meta.Sym.Arith.Poly
// Imports: Init.Grind.Ring.CommSolver Init.Data.Nat.Gcd Init.Data.Nat.Lemmas Init.Data.Nat.Linear Init.WFTactics
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
use crate::lean_imports_rs::Init::Data::Int::Basic::{
    lean_int_dec_eq, lean_int_neg, lean_nat_abs, lean_nat_to_int,
};
use crate::lean_imports_rs::Init::Data::Int::DivMod::Basic::lean_int_ediv;
use crate::lean_imports_rs::Init::Data::Nat::Gcd::lean_nat_gcd;
use crate::lean_imports_rs::Init::Prelude::{
    lean_nat_add, lean_nat_dec_eq, lean_nat_dec_le, lean_nat_dec_lt, lean_nat_sub,
};
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_alloc_ctor, lean_apply_1, lean_apply_2, lean_apply_4,
    lean_box, lean_ctor_get, lean_ctor_set, lean_ctor_set_tag, lean_dec, lean_dec_ref,
    lean_dec_ref_known, lean_del_object, lean_inc, lean_inc_n, lean_inc_ref,
    lean_io_result_is_error, lean_io_result_mk_ok, lean_is_exclusive, lean_obj_once, lean_obj_tag,
    lean_unbox, lean_unsigned_to_nat,
};
static mut l_Lean_Grind_CommRing_Poly_spol___closed__0_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Grind_CommRing_Poly_spol___closed__0: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_Grind_CommRing_Poly_spol___closed__1_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Grind_CommRing_Poly_spol___closed__1: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_Grind_CommRing_Poly_spol___closed__2_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Grind_CommRing_Poly_spol___closed__2: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_Grind_CommRing_Mon_toExpr___closed__0_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Grind_CommRing_Mon_toExpr___closed__0: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_Grind_CommRing_Mon_toExpr___closed__1_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Grind_CommRing_Mon_toExpr___closed__1: *mut LeanObject = core::ptr::null_mut();
pub unsafe fn l_Lean_Grind_CommRing_Mon_sharesVar(
    mut v_x_503_: *mut LeanObject,
    mut v_x_504_: *mut LeanObject,
) -> u8 {
    let mut v___x_505_: u8 = 0;
    let mut v___x_506_: u8 = 0;
    let mut v_p_507_: *mut LeanObject = core::ptr::null_mut();
    let mut v_p_508_: *mut LeanObject = core::ptr::null_mut();
    let mut v_m_509_: *mut LeanObject = core::ptr::null_mut();
    let mut v_m_510_: *mut LeanObject = core::ptr::null_mut();
    let mut v_x_511_: *mut LeanObject = core::ptr::null_mut();
    let mut v_x_512_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_513_: u8 = 0;
    let mut v___x_514_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_503_) == 0 {
                    v___x_505_ = 0;
                    return v___x_505_;
                } else {
                    if lean_obj_tag(v_x_504_) == 0 {
                        v___x_506_ = 0;
                        return v___x_506_;
                    } else {
                        v_p_507_ = lean_ctor_get(v_x_503_, 0);
                        v_p_508_ = lean_ctor_get(v_x_504_, 0);
                        v_m_509_ = lean_ctor_get(v_x_503_, 1);
                        v_m_510_ = lean_ctor_get(v_x_504_, 1);
                        v_x_511_ = lean_ctor_get(v_p_507_, 0);
                        v_x_512_ = lean_ctor_get(v_p_508_, 0);
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
    mut v_x_517_: *mut LeanObject,
    mut v_x_518_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_519_: u8 = 0;
    let mut v_r_520_: *mut LeanObject = core::ptr::null_mut();
    v_res_519_ = l_Lean_Grind_CommRing_Mon_sharesVar(v_x_517_, v_x_518_);
    lean_dec(v_x_518_);
    lean_dec(v_x_517_);
    v_r_520_ = lean_box((v_res_519_) as usize);
    return v_r_520_;
}
pub unsafe fn l___private_Lean_Meta_Sym_Arith_Poly_0__Lean_Grind_CommRing_Mon_sharesVar_match__3_splitter___redArg(
    mut v_x_521_: *mut LeanObject,
    mut v_x_522_: *mut LeanObject,
    mut v_h__1_523_: *mut LeanObject,
    mut v_h__2_524_: *mut LeanObject,
    mut v_h__3_525_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_521_) == 0 {
        let mut v___x_526_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__3_525_);
        lean_dec(v_h__2_524_);
        v___x_526_ = lean_apply_1(v_h__1_523_, v_x_522_);
        return v___x_526_;
    } else {
        lean_dec(v_h__1_523_);
        if lean_obj_tag(v_x_522_) == 0 {
            let mut v___x_527_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__3_525_);
            v___x_527_ = lean_apply_2(v_h__2_524_, v_x_521_, lean_box(0));
            return v___x_527_;
        } else {
            let mut v_p_528_: *mut LeanObject = core::ptr::null_mut();
            let mut v_m_529_: *mut LeanObject = core::ptr::null_mut();
            let mut v_p_530_: *mut LeanObject = core::ptr::null_mut();
            let mut v_m_531_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_532_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__2_524_);
            v_p_528_ = lean_ctor_get(v_x_521_, 0);
            lean_inc_ref(v_p_528_);
            v_m_529_ = lean_ctor_get(v_x_521_, 1);
            lean_inc(v_m_529_);
            lean_dec_ref_known(v_x_521_, 2);
            v_p_530_ = lean_ctor_get(v_x_522_, 0);
            lean_inc_ref(v_p_530_);
            v_m_531_ = lean_ctor_get(v_x_522_, 1);
            lean_inc(v_m_531_);
            lean_dec_ref_known(v_x_522_, 2);
            v___x_532_ = lean_apply_4(v_h__3_525_, v_p_528_, v_m_529_, v_p_530_, v_m_531_);
            return v___x_532_;
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Sym_Arith_Poly_0__Lean_Grind_CommRing_Mon_sharesVar_match__3_splitter(
    mut v_motive_533_: *mut LeanObject,
    mut v_x_534_: *mut LeanObject,
    mut v_x_535_: *mut LeanObject,
    mut v_h__1_536_: *mut LeanObject,
    mut v_h__2_537_: *mut LeanObject,
    mut v_h__3_538_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_534_) == 0 {
        let mut v___x_539_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__3_538_);
        lean_dec(v_h__2_537_);
        v___x_539_ = lean_apply_1(v_h__1_536_, v_x_535_);
        return v___x_539_;
    } else {
        lean_dec(v_h__1_536_);
        if lean_obj_tag(v_x_535_) == 0 {
            let mut v___x_540_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__3_538_);
            v___x_540_ = lean_apply_2(v_h__2_537_, v_x_534_, lean_box(0));
            return v___x_540_;
        } else {
            let mut v_p_541_: *mut LeanObject = core::ptr::null_mut();
            let mut v_m_542_: *mut LeanObject = core::ptr::null_mut();
            let mut v_p_543_: *mut LeanObject = core::ptr::null_mut();
            let mut v_m_544_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_545_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__2_537_);
            v_p_541_ = lean_ctor_get(v_x_534_, 0);
            lean_inc_ref(v_p_541_);
            v_m_542_ = lean_ctor_get(v_x_534_, 1);
            lean_inc(v_m_542_);
            lean_dec_ref_known(v_x_534_, 2);
            v_p_543_ = lean_ctor_get(v_x_535_, 0);
            lean_inc_ref(v_p_543_);
            v_m_544_ = lean_ctor_get(v_x_535_, 1);
            lean_inc(v_m_544_);
            lean_dec_ref_known(v_x_535_, 2);
            v___x_545_ = lean_apply_4(v_h__3_538_, v_p_541_, v_m_542_, v_p_543_, v_m_544_);
            return v___x_545_;
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Sym_Arith_Poly_0__Lean_Grind_CommRing_Mon_sharesVar_match__1_splitter___redArg(
    mut v_x_546_: u8,
    mut v_h__1_547_: *mut LeanObject,
    mut v_h__2_548_: *mut LeanObject,
    mut v_h__3_549_: *mut LeanObject,
) -> *mut LeanObject {
    match v_x_546_ {
        0 => {
            let mut v___x_550_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_551_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__3_549_);
            lean_dec(v_h__1_547_);
            v___x_550_ = lean_box(0);
            v___x_551_ = lean_apply_1(v_h__2_548_, v___x_550_);
            return v___x_551_;
        }
        1 => {
            let mut v___x_552_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_553_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__3_549_);
            lean_dec(v_h__2_548_);
            v___x_552_ = lean_box(0);
            v___x_553_ = lean_apply_1(v_h__1_547_, v___x_552_);
            return v___x_553_;
        }
        _ => {
            let mut v___x_554_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_555_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__2_548_);
            lean_dec(v_h__1_547_);
            v___x_554_ = lean_box(0);
            v___x_555_ = lean_apply_1(v_h__3_549_, v___x_554_);
            return v___x_555_;
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Sym_Arith_Poly_0__Lean_Grind_CommRing_Mon_sharesVar_match__1_splitter___redArg___boxed(
    mut v_x_556_: *mut LeanObject,
    mut v_h__1_557_: *mut LeanObject,
    mut v_h__2_558_: *mut LeanObject,
    mut v_h__3_559_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_x_36__boxed_560_: u8 = 0;
    let mut v_res_561_: *mut LeanObject = core::ptr::null_mut();
    v_x_36__boxed_560_ = (lean_unbox(v_x_556_) as u8);
    v_res_561_ = l___private_Lean_Meta_Sym_Arith_Poly_0__Lean_Grind_CommRing_Mon_sharesVar_match__1_splitter___redArg(v_x_36__boxed_560_, v_h__1_557_, v_h__2_558_, v_h__3_559_);
    return v_res_561_;
}
pub unsafe fn l___private_Lean_Meta_Sym_Arith_Poly_0__Lean_Grind_CommRing_Mon_sharesVar_match__1_splitter(
    mut v_motive_562_: *mut LeanObject,
    mut v_x_563_: u8,
    mut v_h__1_564_: *mut LeanObject,
    mut v_h__2_565_: *mut LeanObject,
    mut v_h__3_566_: *mut LeanObject,
) -> *mut LeanObject {
    match v_x_563_ {
        0 => {
            let mut v___x_567_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_568_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__3_566_);
            lean_dec(v_h__1_564_);
            v___x_567_ = lean_box(0);
            v___x_568_ = lean_apply_1(v_h__2_565_, v___x_567_);
            return v___x_568_;
        }
        1 => {
            let mut v___x_569_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_570_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__3_566_);
            lean_dec(v_h__2_565_);
            v___x_569_ = lean_box(0);
            v___x_570_ = lean_apply_1(v_h__1_564_, v___x_569_);
            return v___x_570_;
        }
        _ => {
            let mut v___x_571_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_572_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__2_565_);
            lean_dec(v_h__1_564_);
            v___x_571_ = lean_box(0);
            v___x_572_ = lean_apply_1(v_h__3_566_, v___x_571_);
            return v___x_572_;
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Sym_Arith_Poly_0__Lean_Grind_CommRing_Mon_sharesVar_match__1_splitter___boxed(
    mut v_motive_573_: *mut LeanObject,
    mut v_x_574_: *mut LeanObject,
    mut v_h__1_575_: *mut LeanObject,
    mut v_h__2_576_: *mut LeanObject,
    mut v_h__3_577_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_x_51__boxed_578_: u8 = 0;
    let mut v_res_579_: *mut LeanObject = core::ptr::null_mut();
    v_x_51__boxed_578_ = (lean_unbox(v_x_574_) as u8);
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
    mut v_x_580_: *mut LeanObject,
    mut v_x_581_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_p_582_: *mut LeanObject = core::ptr::null_mut();
    let mut v_m_583_: *mut LeanObject = core::ptr::null_mut();
    let mut v_p_584_: *mut LeanObject = core::ptr::null_mut();
    let mut v_m_585_: *mut LeanObject = core::ptr::null_mut();
    let mut v_x_586_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_587_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_589_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_590_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_591_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_592_: *mut LeanObject = core::ptr::null_mut();
    let mut v_x_593_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_594_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_595_: u8 = 0;
    let mut v___x_597_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_598_: u8 = 0;
    let mut v___x_599_: u8 = 0;
    let mut v___x_600_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_602_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_603_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_604_: u8 = 0;
    let mut v_isSharedCheck_605_: u8 = 0;
    let mut v_unused_606_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_607_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_609_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_610_: u8 = 0;
    let mut v___x_611_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_613_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_614_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_615_: u8 = 0;
    let mut v_unused_616_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_617_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_580_) == 0 {
                    return v_x_581_;
                } else {
                    if lean_obj_tag(v_x_581_) == 0 {
                        return v_x_580_;
                    } else {
                        v_p_582_ = lean_ctor_get(v_x_580_, 0);
                        v_m_583_ = lean_ctor_get(v_x_580_, 1);
                        v_p_584_ = lean_ctor_get(v_x_581_, 0);
                        v_m_585_ = lean_ctor_get(v_x_581_, 1);
                        v_x_586_ = lean_ctor_get(v_p_582_, 0);
                        v_k_587_ = lean_ctor_get(v_p_582_, 1);
                        v_x_593_ = lean_ctor_get(v_p_584_, 0);
                        v_k_594_ = lean_ctor_get(v_p_584_, 1);
                        v___x_595_ = lean_nat_dec_lt(v_x_586_, v_x_593_);
                        if v___x_595_ == 0 {
                            lean_inc(v_m_585_);
                            lean_inc_ref(v_p_584_);
                            v_isSharedCheck_605_ = (!lean_is_exclusive(v_x_581_)) as u8;
                            if v_isSharedCheck_605_ == 0 {
                                v_unused_606_ = lean_ctor_get(v_x_581_, 1);
                                lean_dec(v_unused_606_);
                                v_unused_607_ = lean_ctor_get(v_x_581_, 0);
                                lean_dec(v_unused_607_);
                                v___x_597_ = v_x_581_;
                                v_isShared_598_ = v_isSharedCheck_605_;
                                state = 2;
                                continue;
                            } else {
                                lean_dec(v_x_581_);
                                v___x_597_ = lean_box(0);
                                v_isShared_598_ = v_isSharedCheck_605_;
                                state = 2;
                                continue;
                            }
                        } else {
                            lean_inc(v_m_583_);
                            lean_inc_ref(v_p_582_);
                            v_isSharedCheck_615_ = (!lean_is_exclusive(v_x_580_)) as u8;
                            if v_isSharedCheck_615_ == 0 {
                                v_unused_616_ = lean_ctor_get(v_x_580_, 1);
                                lean_dec(v_unused_616_);
                                v_unused_617_ = lean_ctor_get(v_x_580_, 0);
                                lean_dec(v_unused_617_);
                                v___x_609_ = v_x_580_;
                                v_isShared_610_ = v_isSharedCheck_615_;
                                state = 4;
                                continue;
                            } else {
                                lean_dec(v_x_580_);
                                v___x_609_ = lean_box(0);
                                v_isShared_610_ = v_isSharedCheck_615_;
                                state = 4;
                                continue;
                            }
                        }
                    }
                }
            }
            1 => {
                v___x_590_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_590_, 0, v_x_586_);
                lean_ctor_set(v___x_590_, 1, v___y_589_);
                v___x_591_ = l_Lean_Grind_CommRing_Mon_lcm(v_m_583_, v_m_585_);
                v___x_592_ = lean_alloc_ctor(1, 2, (0) as u32);
                lean_ctor_set(v___x_592_, 0, v___x_590_);
                lean_ctor_set(v___x_592_, 1, v___x_591_);
                return v___x_592_;
            }
            2 => {
                v___x_599_ = lean_nat_dec_eq(v_x_586_, v_x_593_);
                if v___x_599_ == 0 {
                    v___x_600_ = l_Lean_Grind_CommRing_Mon_lcm(v_x_580_, v_m_585_);
                    if v_isShared_598_ == 0 {
                        lean_ctor_set(v___x_597_, 1, v___x_600_);
                        v___x_602_ = v___x_597_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_603_ = lean_alloc_ctor(1, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_603_, 0, v_p_584_);
                        lean_ctor_set(v_reuseFailAlloc_603_, 1, v___x_600_);
                        v___x_602_ = v_reuseFailAlloc_603_;
                        state = 3;
                        continue;
                    }
                } else {
                    lean_inc(v_k_594_);
                    lean_inc(v_k_587_);
                    lean_inc(v_x_586_);
                    lean_inc(v_m_583_);
                    lean_del_object(v___x_597_);
                    lean_dec_ref(v_p_584_);
                    lean_dec_ref_known(v_x_580_, 2);
                    v___x_604_ = lean_nat_dec_le(v_k_587_, v_k_594_);
                    if v___x_604_ == 0 {
                        lean_dec(v_k_594_);
                        v___y_589_ = v_k_587_;
                        state = 1;
                        continue;
                    } else {
                        lean_dec(v_k_587_);
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
                    lean_ctor_set(v___x_609_, 1, v___x_611_);
                    v___x_613_ = v___x_609_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_614_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_614_, 0, v_p_582_);
                    lean_ctor_set(v_reuseFailAlloc_614_, 1, v___x_611_);
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
    mut v_x_618_: *mut LeanObject,
    mut v_x_619_: *mut LeanObject,
) -> u8 {
    let mut v___x_620_: u8 = 0;
    let mut v___x_621_: u8 = 0;
    let mut v_p_622_: *mut LeanObject = core::ptr::null_mut();
    let mut v_p_623_: *mut LeanObject = core::ptr::null_mut();
    let mut v_m_624_: *mut LeanObject = core::ptr::null_mut();
    let mut v_m_625_: *mut LeanObject = core::ptr::null_mut();
    let mut v_x_626_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_627_: *mut LeanObject = core::ptr::null_mut();
    let mut v_x_628_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_629_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_630_: u8 = 0;
    let mut v___x_631_: u8 = 0;
    let mut v___x_633_: u8 = 0;
    let mut v___x_635_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_618_) == 0 {
                    v___x_620_ = 1;
                    return v___x_620_;
                } else {
                    if lean_obj_tag(v_x_619_) == 0 {
                        v___x_621_ = 0;
                        return v___x_621_;
                    } else {
                        v_p_622_ = lean_ctor_get(v_x_618_, 0);
                        v_p_623_ = lean_ctor_get(v_x_619_, 0);
                        v_m_624_ = lean_ctor_get(v_x_618_, 1);
                        v_m_625_ = lean_ctor_get(v_x_619_, 1);
                        v_x_626_ = lean_ctor_get(v_p_622_, 0);
                        v_k_627_ = lean_ctor_get(v_p_622_, 1);
                        v_x_628_ = lean_ctor_get(v_p_623_, 0);
                        v_k_629_ = lean_ctor_get(v_p_623_, 1);
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
    mut v_x_636_: *mut LeanObject,
    mut v_x_637_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_638_: u8 = 0;
    let mut v_r_639_: *mut LeanObject = core::ptr::null_mut();
    v_res_638_ = l_Lean_Grind_CommRing_Mon_divides(v_x_636_, v_x_637_);
    lean_dec(v_x_637_);
    lean_dec(v_x_636_);
    v_r_639_ = lean_box((v_res_638_) as usize);
    return v_r_639_;
}
pub unsafe fn l_Lean_Grind_CommRing_Mon_div(
    mut v_x_640_: *mut LeanObject,
    mut v_x_641_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_p_642_: *mut LeanObject = core::ptr::null_mut();
    let mut v_p_643_: *mut LeanObject = core::ptr::null_mut();
    let mut v_m_644_: *mut LeanObject = core::ptr::null_mut();
    let mut v_m_645_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_647_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_648_: u8 = 0;
    let mut v_x_649_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_650_: *mut LeanObject = core::ptr::null_mut();
    let mut v_x_651_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_652_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_654_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_655_: u8 = 0;
    let mut v___x_656_: u8 = 0;
    let mut v___x_657_: u8 = 0;
    let mut v___x_658_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_659_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_660_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_661_: u8 = 0;
    let mut v___x_663_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_664_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_666_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_667_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_668_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_670_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_672_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_673_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_674_: u8 = 0;
    let mut v_isSharedCheck_675_: u8 = 0;
    let mut v_unused_676_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_641_) == 0 {
                    return v_x_640_;
                } else {
                    if lean_obj_tag(v_x_640_) == 0 {
                        lean_dec_ref_known(v_x_641_, 2);
                        return v_x_640_;
                    } else {
                        v_p_642_ = lean_ctor_get(v_x_640_, 0);
                        lean_inc_ref(v_p_642_);
                        v_p_643_ = lean_ctor_get(v_x_641_, 0);
                        lean_inc_ref(v_p_643_);
                        v_m_644_ = lean_ctor_get(v_x_641_, 1);
                        v_m_645_ = lean_ctor_get(v_x_640_, 1);
                        v_isSharedCheck_675_ = (!lean_is_exclusive(v_x_640_)) as u8;
                        if v_isSharedCheck_675_ == 0 {
                            v_unused_676_ = lean_ctor_get(v_x_640_, 0);
                            lean_dec(v_unused_676_);
                            v___x_647_ = v_x_640_;
                            v_isShared_648_ = v_isSharedCheck_675_;
                            state = 1;
                            continue;
                        } else {
                            lean_inc(v_m_645_);
                            lean_dec(v_x_640_);
                            v___x_647_ = lean_box(0);
                            v_isShared_648_ = v_isSharedCheck_675_;
                            state = 1;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v_x_649_ = lean_ctor_get(v_p_642_, 0);
                v_k_650_ = lean_ctor_get(v_p_642_, 1);
                v_x_651_ = lean_ctor_get(v_p_643_, 0);
                v_k_652_ = lean_ctor_get(v_p_643_, 1);
                v_isSharedCheck_674_ = (!lean_is_exclusive(v_p_643_)) as u8;
                if v_isSharedCheck_674_ == 0 {
                    v___x_654_ = v_p_643_;
                    v_isShared_655_ = v_isSharedCheck_674_;
                    state = 2;
                    continue;
                } else {
                    lean_inc(v_k_652_);
                    lean_inc(v_x_651_);
                    lean_dec(v_p_643_);
                    v___x_654_ = lean_box(0);
                    v_isShared_655_ = v_isSharedCheck_674_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_656_ = lean_nat_dec_lt(v_x_649_, v_x_651_);
                if v___x_656_ == 0 {
                    lean_inc(v_k_650_);
                    lean_inc(v_x_649_);
                    lean_inc(v_m_644_);
                    lean_dec_ref(v_p_642_);
                    lean_dec_ref_known(v_x_641_, 2);
                    v___x_657_ = lean_nat_dec_eq(v_x_649_, v_x_651_);
                    lean_dec(v_x_651_);
                    if v___x_657_ == 0 {
                        lean_del_object(v___x_654_);
                        lean_dec(v_k_652_);
                        lean_dec(v_k_650_);
                        lean_dec(v_x_649_);
                        lean_del_object(v___x_647_);
                        lean_dec(v_m_645_);
                        lean_dec(v_m_644_);
                        v___x_658_ = lean_box(0);
                        return v___x_658_;
                    } else {
                        v_k_659_ = lean_nat_sub(v_k_650_, v_k_652_);
                        lean_dec(v_k_652_);
                        lean_dec(v_k_650_);
                        v___x_660_ = lean_unsigned_to_nat(0);
                        v___x_661_ = lean_nat_dec_eq(v_k_659_, v___x_660_);
                        if v___x_661_ == 0 {
                            if v_isShared_655_ == 0 {
                                lean_ctor_set(v___x_654_, 1, v_k_659_);
                                lean_ctor_set(v___x_654_, 0, v_x_649_);
                                v___x_663_ = v___x_654_;
                                state = 3;
                                continue;
                            } else {
                                v_reuseFailAlloc_668_ = lean_alloc_ctor(0, 2, (0) as u32);
                                lean_ctor_set(v_reuseFailAlloc_668_, 0, v_x_649_);
                                lean_ctor_set(v_reuseFailAlloc_668_, 1, v_k_659_);
                                v___x_663_ = v_reuseFailAlloc_668_;
                                state = 3;
                                continue;
                            }
                        } else {
                            lean_dec(v_k_659_);
                            lean_del_object(v___x_654_);
                            lean_dec(v_x_649_);
                            lean_del_object(v___x_647_);
                            v_x_640_ = v_m_645_;
                            v_x_641_ = v_m_644_;
                            state = 0;
                            continue;
                        }
                    }
                } else {
                    lean_del_object(v___x_654_);
                    lean_dec(v_k_652_);
                    lean_dec(v_x_651_);
                    v___x_670_ = l_Lean_Grind_CommRing_Mon_div(v_m_645_, v_x_641_);
                    if v_isShared_648_ == 0 {
                        lean_ctor_set(v___x_647_, 1, v___x_670_);
                        v___x_672_ = v___x_647_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_673_ = lean_alloc_ctor(1, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_673_, 0, v_p_642_);
                        lean_ctor_set(v_reuseFailAlloc_673_, 1, v___x_670_);
                        v___x_672_ = v_reuseFailAlloc_673_;
                        state = 5;
                        continue;
                    }
                }
            }
            3 => {
                v___x_664_ = l_Lean_Grind_CommRing_Mon_div(v_m_645_, v_m_644_);
                if v_isShared_648_ == 0 {
                    lean_ctor_set(v___x_647_, 1, v___x_664_);
                    lean_ctor_set(v___x_647_, 0, v___x_663_);
                    v___x_666_ = v___x_647_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_667_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_667_, 0, v___x_663_);
                    lean_ctor_set(v_reuseFailAlloc_667_, 1, v___x_664_);
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
    mut v_x_677_: *mut LeanObject,
    mut v_x_678_: *mut LeanObject,
) -> u8 {
    let mut v___x_679_: u8 = 0;
    let mut v___x_680_: u8 = 0;
    let mut v_p_681_: *mut LeanObject = core::ptr::null_mut();
    let mut v_p_682_: *mut LeanObject = core::ptr::null_mut();
    let mut v_m_683_: *mut LeanObject = core::ptr::null_mut();
    let mut v_m_684_: *mut LeanObject = core::ptr::null_mut();
    let mut v_x_685_: *mut LeanObject = core::ptr::null_mut();
    let mut v_x_686_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_687_: u8 = 0;
    let mut v___x_688_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_677_) == 0 {
                    v___x_679_ = 1;
                    return v___x_679_;
                } else {
                    if lean_obj_tag(v_x_678_) == 0 {
                        v___x_680_ = 1;
                        return v___x_680_;
                    } else {
                        v_p_681_ = lean_ctor_get(v_x_677_, 0);
                        v_p_682_ = lean_ctor_get(v_x_678_, 0);
                        v_m_683_ = lean_ctor_get(v_x_677_, 1);
                        v_m_684_ = lean_ctor_get(v_x_678_, 1);
                        v_x_685_ = lean_ctor_get(v_p_681_, 0);
                        v_x_686_ = lean_ctor_get(v_p_682_, 0);
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
    mut v_x_691_: *mut LeanObject,
    mut v_x_692_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_693_: u8 = 0;
    let mut v_r_694_: *mut LeanObject = core::ptr::null_mut();
    v_res_693_ = l_Lean_Grind_CommRing_Mon_coprime(v_x_691_, v_x_692_);
    lean_dec(v_x_692_);
    lean_dec(v_x_691_);
    v_r_694_ = lean_box((v_res_693_) as usize);
    return v_r_694_;
}
pub unsafe fn l_Lean_Grind_CommRing_Poly_mulConst_x27(
    mut v_p_695_: *mut LeanObject,
    mut v_k_696_: *mut LeanObject,
    mut v_char_x3f_697_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_char_x3f_697_) == 1 {
        let mut v_val_698_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_699_: *mut LeanObject = core::ptr::null_mut();
        v_val_698_ = lean_ctor_get(v_char_x3f_697_, 0);
        lean_inc(v_val_698_);
        lean_dec_ref_known(v_char_x3f_697_, 1);
        v___x_699_ = l_Lean_Grind_CommRing_Poly_mulConstC(v_k_696_, v_p_695_, v_val_698_);
        return v___x_699_;
    } else {
        let mut v___x_700_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_char_x3f_697_);
        v___x_700_ = l_Lean_Grind_CommRing_Poly_mulConst(v_k_696_, v_p_695_);
        return v___x_700_;
    }
}
pub unsafe fn l_Lean_Grind_CommRing_Poly_mulConst_x27___boxed(
    mut v_p_701_: *mut LeanObject,
    mut v_k_702_: *mut LeanObject,
    mut v_char_x3f_703_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_704_: *mut LeanObject = core::ptr::null_mut();
    v_res_704_ = l_Lean_Grind_CommRing_Poly_mulConst_x27(v_p_701_, v_k_702_, v_char_x3f_703_);
    lean_dec(v_k_702_);
    return v_res_704_;
}
pub unsafe fn l_Lean_Grind_CommRing_Poly_mulMon_x27(
    mut v_p_705_: *mut LeanObject,
    mut v_k_706_: *mut LeanObject,
    mut v_m_707_: *mut LeanObject,
    mut v_char_x3f_708_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_char_x3f_708_) == 1 {
        let mut v_val_709_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_710_: *mut LeanObject = core::ptr::null_mut();
        v_val_709_ = lean_ctor_get(v_char_x3f_708_, 0);
        lean_inc(v_val_709_);
        lean_dec_ref_known(v_char_x3f_708_, 1);
        v___x_710_ = l_Lean_Grind_CommRing_Poly_mulMonC(v_k_706_, v_m_707_, v_p_705_, v_val_709_);
        return v___x_710_;
    } else {
        let mut v___x_711_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_char_x3f_708_);
        v___x_711_ = l_Lean_Grind_CommRing_Poly_mulMon(v_k_706_, v_m_707_, v_p_705_);
        return v___x_711_;
    }
}
pub unsafe fn l_Lean_Grind_CommRing_Poly_mulMon_x27___boxed(
    mut v_p_712_: *mut LeanObject,
    mut v_k_713_: *mut LeanObject,
    mut v_m_714_: *mut LeanObject,
    mut v_char_x3f_715_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_716_: *mut LeanObject = core::ptr::null_mut();
    v_res_716_ =
        l_Lean_Grind_CommRing_Poly_mulMon_x27(v_p_712_, v_k_713_, v_m_714_, v_char_x3f_715_);
    lean_dec(v_k_713_);
    return v_res_716_;
}
pub unsafe fn l_Lean_Grind_CommRing_Poly_combine_x27(
    mut v_p_u2081_717_: *mut LeanObject,
    mut v_p_u2082_718_: *mut LeanObject,
    mut v_char_x3f_719_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_char_x3f_719_) == 1 {
        let mut v_val_720_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_721_: *mut LeanObject = core::ptr::null_mut();
        v_val_720_ = lean_ctor_get(v_char_x3f_719_, 0);
        lean_inc(v_val_720_);
        lean_dec_ref_known(v_char_x3f_719_, 1);
        v___x_721_ =
            l_Lean_Grind_CommRing_Poly_combineC(v_p_u2081_717_, v_p_u2082_718_, v_val_720_);
        return v___x_721_;
    } else {
        let mut v___x_722_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_char_x3f_719_);
        v___x_722_ = l_Lean_Grind_CommRing_Poly_combine(v_p_u2081_717_, v_p_u2082_718_);
        return v___x_722_;
    }
}
pub unsafe fn l_Nat_cast___at___00Lean_Grind_CommRing_Poly_spol_spec__0(
    mut v_a_723_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_724_: *mut LeanObject = core::ptr::null_mut();
    v___x_724_ = lean_nat_to_int(v_a_723_);
    return v___x_724_;
}
pub unsafe fn _init_l_Lean_Grind_CommRing_Poly_spol___closed__0() -> *mut LeanObject {
    let mut v___x_725_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_726_: *mut LeanObject = core::ptr::null_mut();
    v___x_725_ = lean_unsigned_to_nat(0);
    v___x_726_ = lean_nat_to_int(v___x_725_);
    return v___x_726_;
}
pub unsafe fn _init_l_Lean_Grind_CommRing_Poly_spol___closed__1() -> *mut LeanObject {
    let mut v___x_727_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_728_: *mut LeanObject = core::ptr::null_mut();
    v___x_727_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Grind_CommRing_Poly_spol___closed__0),
        core::ptr::addr_of_mut!(l_Lean_Grind_CommRing_Poly_spol___closed__0_once),
        _init_l_Lean_Grind_CommRing_Poly_spol___closed__0,
    );
    v___x_728_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_728_, 0, v___x_727_);
    return v___x_728_;
}
pub unsafe fn _init_l_Lean_Grind_CommRing_Poly_spol___closed__2() -> *mut LeanObject {
    let mut v___x_729_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_730_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_731_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_732_: *mut LeanObject = core::ptr::null_mut();
    v___x_729_ = lean_box(0);
    v___x_730_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Grind_CommRing_Poly_spol___closed__0),
        core::ptr::addr_of_mut!(l_Lean_Grind_CommRing_Poly_spol___closed__0_once),
        _init_l_Lean_Grind_CommRing_Poly_spol___closed__0,
    );
    v___x_731_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Grind_CommRing_Poly_spol___closed__1),
        core::ptr::addr_of_mut!(l_Lean_Grind_CommRing_Poly_spol___closed__1_once),
        _init_l_Lean_Grind_CommRing_Poly_spol___closed__1,
    );
    v___x_732_ = lean_alloc_ctor(0, 5, (0) as u32);
    lean_ctor_set(v___x_732_, 0, v___x_731_);
    lean_ctor_set(v___x_732_, 1, v___x_730_);
    lean_ctor_set(v___x_732_, 2, v___x_729_);
    lean_ctor_set(v___x_732_, 3, v___x_730_);
    lean_ctor_set(v___x_732_, 4, v___x_729_);
    return v___x_732_;
}
pub unsafe fn l_Lean_Grind_CommRing_Poly_spol(
    mut v_p_u2081_733_: *mut LeanObject,
    mut v_p_u2082_734_: *mut LeanObject,
    mut v_char_x3f_735_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_737_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_738_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v_739_: *mut LeanObject = core::ptr::null_mut();
    let mut v_p_740_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_741_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v_742_: *mut LeanObject = core::ptr::null_mut();
    let mut v_p_743_: *mut LeanObject = core::ptr::null_mut();
    let mut v_m_744_: *mut LeanObject = core::ptr::null_mut();
    let mut v_m_u2081_745_: *mut LeanObject = core::ptr::null_mut();
    let mut v_m_u2082_746_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_747_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_748_: *mut LeanObject = core::ptr::null_mut();
    let mut v_g_749_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_750_: *mut LeanObject = core::ptr::null_mut();
    let mut v_c_u2081_751_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_752_: *mut LeanObject = core::ptr::null_mut();
    let mut v_c_u2082_753_: *mut LeanObject = core::ptr::null_mut();
    let mut v_p_u2081_754_: *mut LeanObject = core::ptr::null_mut();
    let mut v_p_u2082_755_: *mut LeanObject = core::ptr::null_mut();
    let mut v_spol_756_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_757_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_p_u2081_733_) == 1 {
                    if lean_obj_tag(v_p_u2082_734_) == 1 {
                        v_k_738_ = lean_ctor_get(v_p_u2081_733_, 0);
                        lean_inc(v_k_738_);
                        v_v_739_ = lean_ctor_get(v_p_u2081_733_, 1);
                        lean_inc_n(v_v_739_, 2);
                        v_p_740_ = lean_ctor_get(v_p_u2081_733_, 2);
                        lean_inc_ref(v_p_740_);
                        lean_dec_ref_known(v_p_u2081_733_, 3);
                        v_k_741_ = lean_ctor_get(v_p_u2082_734_, 0);
                        lean_inc(v_k_741_);
                        v_v_742_ = lean_ctor_get(v_p_u2082_734_, 1);
                        lean_inc_n(v_v_742_, 2);
                        v_p_743_ = lean_ctor_get(v_p_u2082_734_, 2);
                        lean_inc_ref(v_p_743_);
                        lean_dec_ref_known(v_p_u2082_734_, 3);
                        v_m_744_ = l_Lean_Grind_CommRing_Mon_lcm(v_v_739_, v_v_742_);
                        lean_inc(v_m_744_);
                        v_m_u2081_745_ = l_Lean_Grind_CommRing_Mon_div(v_m_744_, v_v_739_);
                        v_m_u2082_746_ = l_Lean_Grind_CommRing_Mon_div(v_m_744_, v_v_742_);
                        v___x_747_ = lean_nat_abs(v_k_738_);
                        v___x_748_ = lean_nat_abs(v_k_741_);
                        v_g_749_ = lean_nat_gcd(v___x_747_, v___x_748_);
                        lean_dec(v___x_748_);
                        lean_dec(v___x_747_);
                        v___x_750_ = lean_nat_to_int(v_g_749_);
                        v_c_u2081_751_ = lean_int_ediv(v_k_741_, v___x_750_);
                        lean_dec(v_k_741_);
                        v___x_752_ = lean_int_neg(v_k_738_);
                        lean_dec(v_k_738_);
                        v_c_u2082_753_ = lean_int_ediv(v___x_752_, v___x_750_);
                        lean_dec(v___x_750_);
                        lean_dec(v___x_752_);
                        lean_inc_n(v_char_x3f_735_, 2);
                        lean_inc(v_m_u2081_745_);
                        v_p_u2081_754_ = l_Lean_Grind_CommRing_Poly_mulMon_x27(
                            v_p_740_,
                            v_c_u2081_751_,
                            v_m_u2081_745_,
                            v_char_x3f_735_,
                        );
                        lean_inc(v_m_u2082_746_);
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
                        v___x_757_ = lean_alloc_ctor(0, 5, (0) as u32);
                        lean_ctor_set(v___x_757_, 0, v_spol_756_);
                        lean_ctor_set(v___x_757_, 1, v_c_u2081_751_);
                        lean_ctor_set(v___x_757_, 2, v_m_u2081_745_);
                        lean_ctor_set(v___x_757_, 3, v_c_u2082_753_);
                        lean_ctor_set(v___x_757_, 4, v_m_u2082_746_);
                        return v___x_757_;
                    } else {
                        lean_dec_ref_known(v_p_u2081_733_, 3);
                        lean_dec(v_char_x3f_735_);
                        lean_dec_ref(v_p_u2082_734_);
                        state = 1;
                        continue;
                    }
                } else {
                    lean_dec(v_char_x3f_735_);
                    lean_dec_ref(v_p_u2082_734_);
                    lean_dec_ref(v_p_u2081_733_);
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_737_ = lean_obj_once(
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
pub unsafe fn l_Lean_Grind_CommRing_Poly_degree(mut v_x_758_: *mut LeanObject) -> *mut LeanObject {
    if lean_obj_tag(v_x_758_) == 0 {
        let mut v___x_759_: *mut LeanObject = core::ptr::null_mut();
        v___x_759_ = lean_unsigned_to_nat(0);
        return v___x_759_;
    } else {
        let mut v_v_760_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_761_: *mut LeanObject = core::ptr::null_mut();
        v_v_760_ = lean_ctor_get(v_x_758_, 1);
        v___x_761_ = l_Lean_Grind_CommRing_Mon_degree(v_v_760_);
        return v___x_761_;
    }
}
pub unsafe fn l_Lean_Grind_CommRing_Poly_degree___boxed(
    mut v_x_762_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_763_: *mut LeanObject = core::ptr::null_mut();
    v_res_763_ = l_Lean_Grind_CommRing_Poly_degree(v_x_762_);
    lean_dec_ref(v_x_762_);
    return v_res_763_;
}
pub unsafe fn l___private_Lean_Meta_Sym_Arith_Poly_0__Lean_Grind_CommRing_Poly_numTerms_go(
    mut v_p_764_: *mut LeanObject,
    mut v_acc_765_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_p_766_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_767_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_768_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_p_764_) == 0 {
                    return v_acc_765_;
                } else {
                    v_p_766_ = lean_ctor_get(v_p_764_, 2);
                    v___x_767_ = lean_unsigned_to_nat(1);
                    v___x_768_ = lean_nat_add(v_acc_765_, v___x_767_);
                    lean_dec(v_acc_765_);
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
    mut v_p_770_: *mut LeanObject,
    mut v_acc_771_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_772_: *mut LeanObject = core::ptr::null_mut();
    v_res_772_ = l___private_Lean_Meta_Sym_Arith_Poly_0__Lean_Grind_CommRing_Poly_numTerms_go(
        v_p_770_, v_acc_771_,
    );
    lean_dec_ref(v_p_770_);
    return v_res_772_;
}
pub unsafe fn l_Lean_Grind_CommRing_Poly_numTerms(
    mut v_p_773_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_774_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_775_: *mut LeanObject = core::ptr::null_mut();
    v___x_774_ = lean_unsigned_to_nat(0);
    v___x_775_ = l___private_Lean_Meta_Sym_Arith_Poly_0__Lean_Grind_CommRing_Poly_numTerms_go(
        v_p_773_, v___x_774_,
    );
    return v___x_775_;
}
pub unsafe fn l_Lean_Grind_CommRing_Poly_numTerms___boxed(
    mut v_p_776_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_777_: *mut LeanObject = core::ptr::null_mut();
    v_res_777_ = l_Lean_Grind_CommRing_Poly_numTerms(v_p_776_);
    lean_dec_ref(v_p_776_);
    return v_res_777_;
}
pub unsafe fn l_Lean_Grind_CommRing_Poly_divides(
    mut v_p_778_: *mut LeanObject,
    mut v_m_779_: *mut LeanObject,
) -> u8 {
    if lean_obj_tag(v_p_778_) == 0 {
        let mut v___x_780_: u8 = 0;
        v___x_780_ = 1;
        return v___x_780_;
    } else {
        let mut v_v_781_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_782_: u8 = 0;
        v_v_781_ = lean_ctor_get(v_p_778_, 1);
        v___x_782_ = l_Lean_Grind_CommRing_Mon_divides(v_v_781_, v_m_779_);
        return v___x_782_;
    }
}
pub unsafe fn l_Lean_Grind_CommRing_Poly_divides___boxed(
    mut v_p_783_: *mut LeanObject,
    mut v_m_784_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_785_: u8 = 0;
    let mut v_r_786_: *mut LeanObject = core::ptr::null_mut();
    v_res_785_ = l_Lean_Grind_CommRing_Poly_divides(v_p_783_, v_m_784_);
    lean_dec(v_m_784_);
    lean_dec_ref(v_p_783_);
    v_r_786_ = lean_box((v_res_785_) as usize);
    return v_r_786_;
}
pub unsafe fn l_Lean_Grind_CommRing_Poly_lc(mut v_x_787_: *mut LeanObject) -> *mut LeanObject {
    let mut v_k_788_: *mut LeanObject = core::ptr::null_mut();
    v_k_788_ = lean_ctor_get(v_x_787_, 0);
    lean_inc(v_k_788_);
    return v_k_788_;
}
pub unsafe fn l_Lean_Grind_CommRing_Poly_lc___boxed(
    mut v_x_789_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_790_: *mut LeanObject = core::ptr::null_mut();
    v_res_790_ = l_Lean_Grind_CommRing_Poly_lc(v_x_789_);
    lean_dec_ref(v_x_789_);
    return v_res_790_;
}
pub unsafe fn l_Lean_Grind_CommRing_Poly_lm(mut v_x_791_: *mut LeanObject) -> *mut LeanObject {
    if lean_obj_tag(v_x_791_) == 0 {
        let mut v___x_792_: *mut LeanObject = core::ptr::null_mut();
        v___x_792_ = lean_box(0);
        return v___x_792_;
    } else {
        let mut v_v_793_: *mut LeanObject = core::ptr::null_mut();
        v_v_793_ = lean_ctor_get(v_x_791_, 1);
        lean_inc(v_v_793_);
        return v_v_793_;
    }
}
pub unsafe fn l_Lean_Grind_CommRing_Poly_lm___boxed(
    mut v_x_794_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_795_: *mut LeanObject = core::ptr::null_mut();
    v_res_795_ = l_Lean_Grind_CommRing_Poly_lm(v_x_794_);
    lean_dec_ref(v_x_794_);
    return v_res_795_;
}
pub unsafe fn l_Lean_Grind_CommRing_Poly_isZero(mut v_x_796_: *mut LeanObject) -> u8 {
    if lean_obj_tag(v_x_796_) == 0 {
        let mut v_k_797_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_798_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_799_: u8 = 0;
        v_k_797_ = lean_ctor_get(v_x_796_, 0);
        v___x_798_ = lean_obj_once(
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
    mut v_x_801_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_802_: u8 = 0;
    let mut v_r_803_: *mut LeanObject = core::ptr::null_mut();
    v_res_802_ = l_Lean_Grind_CommRing_Poly_isZero(v_x_801_);
    lean_dec_ref(v_x_801_);
    v_r_803_ = lean_box((v_res_802_) as usize);
    return v_r_803_;
}
pub unsafe fn l_Lean_Grind_CommRing_Poly_getConst(
    mut v_x_804_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_k_805_: *mut LeanObject = core::ptr::null_mut();
    let mut v_p_806_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_804_) == 0 {
                    v_k_805_ = lean_ctor_get(v_x_804_, 0);
                    lean_inc(v_k_805_);
                    return v_k_805_;
                } else {
                    v_p_806_ = lean_ctor_get(v_x_804_, 2);
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
    mut v_x_808_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_809_: *mut LeanObject = core::ptr::null_mut();
    v_res_809_ = l_Lean_Grind_CommRing_Poly_getConst(v_x_808_);
    lean_dec_ref(v_x_808_);
    return v_res_809_;
}
pub unsafe fn l_Lean_Grind_CommRing_Poly_checkCoeffs(mut v_x_810_: *mut LeanObject) -> u8 {
    let mut v___x_811_: u8 = 0;
    let mut v_k_812_: *mut LeanObject = core::ptr::null_mut();
    let mut v_p_813_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_814_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_815_: u8 = 0;
    let mut v___x_817_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_810_) == 0 {
                    v___x_811_ = 1;
                    return v___x_811_;
                } else {
                    v_k_812_ = lean_ctor_get(v_x_810_, 0);
                    v_p_813_ = lean_ctor_get(v_x_810_, 2);
                    v___x_814_ = lean_obj_once(
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
    mut v_x_818_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_819_: u8 = 0;
    let mut v_r_820_: *mut LeanObject = core::ptr::null_mut();
    v_res_819_ = l_Lean_Grind_CommRing_Poly_checkCoeffs(v_x_818_);
    lean_dec_ref(v_x_818_);
    v_r_820_ = lean_box((v_res_819_) as usize);
    return v_r_820_;
}
pub unsafe fn l_Lean_Grind_CommRing_Poly_checkNoUnitMon(mut v_x_821_: *mut LeanObject) -> u8 {
    let mut v___x_822_: u8 = 0;
    let mut v_v_823_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_824_: u8 = 0;
    let mut v_p_825_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_821_) == 0 {
                    v___x_822_ = 1;
                    return v___x_822_;
                } else {
                    v_v_823_ = lean_ctor_get(v_x_821_, 1);
                    if lean_obj_tag(v_v_823_) == 0 {
                        v___x_824_ = 0;
                        return v___x_824_;
                    } else {
                        v_p_825_ = lean_ctor_get(v_x_821_, 2);
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
    mut v_x_827_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_828_: u8 = 0;
    let mut v_r_829_: *mut LeanObject = core::ptr::null_mut();
    v_res_828_ = l_Lean_Grind_CommRing_Poly_checkNoUnitMon(v_x_827_);
    lean_dec_ref(v_x_827_);
    v_r_829_ = lean_box((v_res_828_) as usize);
    return v_r_829_;
}
pub unsafe fn l___private_Lean_Meta_Sym_Arith_Poly_0__Lean_Grind_CommRing_Poly_gcdCoeffs_go(
    mut v_p_830_: *mut LeanObject,
    mut v_acc_831_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_832_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_833_: u8 = 0;
    let mut v_k_834_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_835_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_836_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_837_: *mut LeanObject = core::ptr::null_mut();
    let mut v_p_838_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_839_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_840_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_832_ = lean_unsigned_to_nat(1);
                v___x_833_ = lean_nat_dec_eq(v_acc_831_, v___x_832_);
                if v___x_833_ == 0 {
                    if lean_obj_tag(v_p_830_) == 0 {
                        v_k_834_ = lean_ctor_get(v_p_830_, 0);
                        v___x_835_ = lean_nat_abs(v_k_834_);
                        v___x_836_ = lean_nat_gcd(v_acc_831_, v___x_835_);
                        lean_dec(v___x_835_);
                        lean_dec(v_acc_831_);
                        return v___x_836_;
                    } else {
                        v_k_837_ = lean_ctor_get(v_p_830_, 0);
                        v_p_838_ = lean_ctor_get(v_p_830_, 2);
                        v___x_839_ = lean_nat_abs(v_k_837_);
                        v___x_840_ = lean_nat_gcd(v_acc_831_, v___x_839_);
                        lean_dec(v___x_839_);
                        lean_dec(v_acc_831_);
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
    mut v_p_842_: *mut LeanObject,
    mut v_acc_843_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_844_: *mut LeanObject = core::ptr::null_mut();
    v_res_844_ = l___private_Lean_Meta_Sym_Arith_Poly_0__Lean_Grind_CommRing_Poly_gcdCoeffs_go(
        v_p_842_, v_acc_843_,
    );
    lean_dec_ref(v_p_842_);
    return v_res_844_;
}
pub unsafe fn l_Lean_Grind_CommRing_Poly_gcdCoeffs(
    mut v_x_845_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_845_) == 0 {
        let mut v_k_846_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_847_: *mut LeanObject = core::ptr::null_mut();
        v_k_846_ = lean_ctor_get(v_x_845_, 0);
        v___x_847_ = lean_nat_abs(v_k_846_);
        return v___x_847_;
    } else {
        let mut v_k_848_: *mut LeanObject = core::ptr::null_mut();
        let mut v_p_849_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_850_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_851_: *mut LeanObject = core::ptr::null_mut();
        v_k_848_ = lean_ctor_get(v_x_845_, 0);
        v_p_849_ = lean_ctor_get(v_x_845_, 2);
        v___x_850_ = lean_nat_abs(v_k_848_);
        v___x_851_ = l___private_Lean_Meta_Sym_Arith_Poly_0__Lean_Grind_CommRing_Poly_gcdCoeffs_go(
            v_p_849_, v___x_850_,
        );
        return v___x_851_;
    }
}
pub unsafe fn l_Lean_Grind_CommRing_Poly_gcdCoeffs___boxed(
    mut v_x_852_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_853_: *mut LeanObject = core::ptr::null_mut();
    v_res_853_ = l_Lean_Grind_CommRing_Poly_gcdCoeffs(v_x_852_);
    lean_dec_ref(v_x_852_);
    return v_res_853_;
}
pub unsafe fn l_Lean_Grind_CommRing_Poly_divConst(
    mut v_p_854_: *mut LeanObject,
    mut v_a_855_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_k_856_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_858_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_859_: u8 = 0;
    let mut v___x_860_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_862_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_863_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_864_: u8 = 0;
    let mut v_k_865_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v_866_: *mut LeanObject = core::ptr::null_mut();
    let mut v_p_867_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_869_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_870_: u8 = 0;
    let mut v___x_871_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_872_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_874_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_875_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_876_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_p_854_) == 0 {
                    v_k_856_ = lean_ctor_get(v_p_854_, 0);
                    v_isSharedCheck_864_ = (!lean_is_exclusive(v_p_854_)) as u8;
                    if v_isSharedCheck_864_ == 0 {
                        v___x_858_ = v_p_854_;
                        v_isShared_859_ = v_isSharedCheck_864_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_k_856_);
                        lean_dec(v_p_854_);
                        v___x_858_ = lean_box(0);
                        v_isShared_859_ = v_isSharedCheck_864_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_k_865_ = lean_ctor_get(v_p_854_, 0);
                    v_v_866_ = lean_ctor_get(v_p_854_, 1);
                    v_p_867_ = lean_ctor_get(v_p_854_, 2);
                    v_isSharedCheck_876_ = (!lean_is_exclusive(v_p_854_)) as u8;
                    if v_isSharedCheck_876_ == 0 {
                        v___x_869_ = v_p_854_;
                        v_isShared_870_ = v_isSharedCheck_876_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_p_867_);
                        lean_inc(v_v_866_);
                        lean_inc(v_k_865_);
                        lean_dec(v_p_854_);
                        v___x_869_ = lean_box(0);
                        v_isShared_870_ = v_isSharedCheck_876_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v___x_860_ = lean_int_ediv(v_k_856_, v_a_855_);
                lean_dec(v_k_856_);
                if v_isShared_859_ == 0 {
                    lean_ctor_set(v___x_858_, 0, v___x_860_);
                    v___x_862_ = v___x_858_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_863_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_863_, 0, v___x_860_);
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
                lean_dec(v_k_865_);
                v___x_872_ = l_Lean_Grind_CommRing_Poly_divConst(v_p_867_, v_a_855_);
                if v_isShared_870_ == 0 {
                    lean_ctor_set(v___x_869_, 2, v___x_872_);
                    lean_ctor_set(v___x_869_, 0, v___x_871_);
                    v___x_874_ = v___x_869_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_875_ = lean_alloc_ctor(1, 3, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_875_, 0, v___x_871_);
                    lean_ctor_set(v_reuseFailAlloc_875_, 1, v_v_866_);
                    lean_ctor_set(v_reuseFailAlloc_875_, 2, v___x_872_);
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
    mut v_p_877_: *mut LeanObject,
    mut v_a_878_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_879_: *mut LeanObject = core::ptr::null_mut();
    v_res_879_ = l_Lean_Grind_CommRing_Poly_divConst(v_p_877_, v_a_878_);
    lean_dec(v_a_878_);
    return v_res_879_;
}
pub unsafe fn l_Lean_Grind_CommRing_Mon_size(mut v_x_880_: *mut LeanObject) -> *mut LeanObject {
    if lean_obj_tag(v_x_880_) == 0 {
        let mut v___x_881_: *mut LeanObject = core::ptr::null_mut();
        v___x_881_ = lean_unsigned_to_nat(0);
        return v___x_881_;
    } else {
        let mut v_m_882_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_883_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_884_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_885_: *mut LeanObject = core::ptr::null_mut();
        v_m_882_ = lean_ctor_get(v_x_880_, 1);
        v___x_883_ = l_Lean_Grind_CommRing_Mon_size(v_m_882_);
        v___x_884_ = lean_unsigned_to_nat(1);
        v___x_885_ = lean_nat_add(v___x_883_, v___x_884_);
        lean_dec(v___x_883_);
        return v___x_885_;
    }
}
pub unsafe fn l_Lean_Grind_CommRing_Mon_size___boxed(
    mut v_x_886_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_887_: *mut LeanObject = core::ptr::null_mut();
    v_res_887_ = l_Lean_Grind_CommRing_Mon_size(v_x_886_);
    lean_dec(v_x_886_);
    return v_res_887_;
}
pub unsafe fn l_Lean_Grind_CommRing_Poly_size(mut v_x_888_: *mut LeanObject) -> *mut LeanObject {
    if lean_obj_tag(v_x_888_) == 0 {
        let mut v___x_889_: *mut LeanObject = core::ptr::null_mut();
        v___x_889_ = lean_unsigned_to_nat(1);
        return v___x_889_;
    } else {
        let mut v_v_890_: *mut LeanObject = core::ptr::null_mut();
        let mut v_p_891_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_892_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_893_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_894_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_895_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_896_: *mut LeanObject = core::ptr::null_mut();
        v_v_890_ = lean_ctor_get(v_x_888_, 1);
        v_p_891_ = lean_ctor_get(v_x_888_, 2);
        v___x_892_ = l_Lean_Grind_CommRing_Mon_size(v_v_890_);
        v___x_893_ = lean_unsigned_to_nat(1);
        v___x_894_ = lean_nat_add(v___x_892_, v___x_893_);
        lean_dec(v___x_892_);
        v___x_895_ = l_Lean_Grind_CommRing_Poly_size(v_p_891_);
        v___x_896_ = lean_nat_add(v___x_894_, v___x_895_);
        lean_dec(v___x_895_);
        lean_dec(v___x_894_);
        return v___x_896_;
    }
}
pub unsafe fn l_Lean_Grind_CommRing_Poly_size___boxed(
    mut v_x_897_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_898_: *mut LeanObject = core::ptr::null_mut();
    v_res_898_ = l_Lean_Grind_CommRing_Poly_size(v_x_897_);
    lean_dec_ref(v_x_897_);
    return v_res_898_;
}
pub unsafe fn l_Lean_Grind_CommRing_Poly_length(mut v_x_899_: *mut LeanObject) -> *mut LeanObject {
    if lean_obj_tag(v_x_899_) == 0 {
        let mut v___x_900_: *mut LeanObject = core::ptr::null_mut();
        v___x_900_ = lean_unsigned_to_nat(0);
        return v___x_900_;
    } else {
        let mut v_p_901_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_902_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_903_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_904_: *mut LeanObject = core::ptr::null_mut();
        v_p_901_ = lean_ctor_get(v_x_899_, 2);
        v___x_902_ = lean_unsigned_to_nat(1);
        v___x_903_ = l_Lean_Grind_CommRing_Poly_length(v_p_901_);
        v___x_904_ = lean_nat_add(v___x_902_, v___x_903_);
        lean_dec(v___x_903_);
        return v___x_904_;
    }
}
pub unsafe fn l_Lean_Grind_CommRing_Poly_length___boxed(
    mut v_x_905_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_906_: *mut LeanObject = core::ptr::null_mut();
    v_res_906_ = l_Lean_Grind_CommRing_Poly_length(v_x_905_);
    lean_dec_ref(v_x_905_);
    return v_res_906_;
}
pub unsafe fn l_Lean_Grind_CommRing_Power_toExpr(
    mut v_pw_907_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_x_908_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_909_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_911_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_912_: u8 = 0;
    let mut v___x_913_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_914_: u8 = 0;
    let mut v___x_915_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_917_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_918_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_919_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_920_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_x_908_ = lean_ctor_get(v_pw_907_, 0);
                v_k_909_ = lean_ctor_get(v_pw_907_, 1);
                v_isSharedCheck_920_ = (!lean_is_exclusive(v_pw_907_)) as u8;
                if v_isSharedCheck_920_ == 0 {
                    v___x_911_ = v_pw_907_;
                    v_isShared_912_ = v_isSharedCheck_920_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_k_909_);
                    lean_inc(v_x_908_);
                    lean_dec(v_pw_907_);
                    v___x_911_ = lean_box(0);
                    v_isShared_912_ = v_isSharedCheck_920_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_913_ = lean_unsigned_to_nat(1);
                v___x_914_ = lean_nat_dec_eq(v_k_909_, v___x_913_);
                if v___x_914_ == 0 {
                    v___x_915_ = lean_alloc_ctor(3, 1, (0) as u32);
                    lean_ctor_set(v___x_915_, 0, v_x_908_);
                    if v_isShared_912_ == 0 {
                        lean_ctor_set_tag(v___x_911_, 8);
                        lean_ctor_set(v___x_911_, 0, v___x_915_);
                        v___x_917_ = v___x_911_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_918_ = lean_alloc_ctor(8, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_918_, 0, v___x_915_);
                        lean_ctor_set(v_reuseFailAlloc_918_, 1, v_k_909_);
                        v___x_917_ = v_reuseFailAlloc_918_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_911_);
                    lean_dec(v_k_909_);
                    v___x_919_ = lean_alloc_ctor(3, 1, (0) as u32);
                    lean_ctor_set(v___x_919_, 0, v_x_908_);
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
    mut v_m_921_: *mut LeanObject,
    mut v_acc_922_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_p_923_: *mut LeanObject = core::ptr::null_mut();
    let mut v_m_924_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_926_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_927_: u8 = 0;
    let mut v___x_928_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_930_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_932_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_933_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_m_921_) == 0 {
                    return v_acc_922_;
                } else {
                    v_p_923_ = lean_ctor_get(v_m_921_, 0);
                    v_m_924_ = lean_ctor_get(v_m_921_, 1);
                    v_isSharedCheck_933_ = (!lean_is_exclusive(v_m_921_)) as u8;
                    if v_isSharedCheck_933_ == 0 {
                        v___x_926_ = v_m_921_;
                        v_isShared_927_ = v_isSharedCheck_933_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_m_924_);
                        lean_inc(v_p_923_);
                        lean_dec(v_m_921_);
                        v___x_926_ = lean_box(0);
                        v_isShared_927_ = v_isSharedCheck_933_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_928_ = l_Lean_Grind_CommRing_Power_toExpr(v_p_923_);
                if v_isShared_927_ == 0 {
                    lean_ctor_set_tag(v___x_926_, 7);
                    lean_ctor_set(v___x_926_, 1, v___x_928_);
                    lean_ctor_set(v___x_926_, 0, v_acc_922_);
                    v___x_930_ = v___x_926_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_932_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_932_, 0, v_acc_922_);
                    lean_ctor_set(v_reuseFailAlloc_932_, 1, v___x_928_);
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
pub unsafe fn _init_l_Lean_Grind_CommRing_Mon_toExpr___closed__0() -> *mut LeanObject {
    let mut v___x_934_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_935_: *mut LeanObject = core::ptr::null_mut();
    v___x_934_ = lean_unsigned_to_nat(1);
    v___x_935_ = lean_nat_to_int(v___x_934_);
    return v___x_935_;
}
pub unsafe fn _init_l_Lean_Grind_CommRing_Mon_toExpr___closed__1() -> *mut LeanObject {
    let mut v___x_936_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_937_: *mut LeanObject = core::ptr::null_mut();
    v___x_936_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Grind_CommRing_Mon_toExpr___closed__0),
        core::ptr::addr_of_mut!(l_Lean_Grind_CommRing_Mon_toExpr___closed__0_once),
        _init_l_Lean_Grind_CommRing_Mon_toExpr___closed__0,
    );
    v___x_937_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_937_, 0, v___x_936_);
    return v___x_937_;
}
pub unsafe fn l_Lean_Grind_CommRing_Mon_toExpr(mut v_m_938_: *mut LeanObject) -> *mut LeanObject {
    if lean_obj_tag(v_m_938_) == 0 {
        let mut v___x_939_: *mut LeanObject = core::ptr::null_mut();
        v___x_939_ = lean_obj_once(
            core::ptr::addr_of_mut!(l_Lean_Grind_CommRing_Mon_toExpr___closed__1),
            core::ptr::addr_of_mut!(l_Lean_Grind_CommRing_Mon_toExpr___closed__1_once),
            _init_l_Lean_Grind_CommRing_Mon_toExpr___closed__1,
        );
        return v___x_939_;
    } else {
        let mut v_p_940_: *mut LeanObject = core::ptr::null_mut();
        let mut v_m_941_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_942_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_943_: *mut LeanObject = core::ptr::null_mut();
        v_p_940_ = lean_ctor_get(v_m_938_, 0);
        lean_inc_ref(v_p_940_);
        v_m_941_ = lean_ctor_get(v_m_938_, 1);
        lean_inc(v_m_941_);
        lean_dec_ref_known(v_m_938_, 2);
        v___x_942_ = l_Lean_Grind_CommRing_Power_toExpr(v_p_940_);
        v___x_943_ = l___private_Lean_Meta_Sym_Arith_Poly_0__Lean_Grind_CommRing_Mon_toExpr_go(
            v_m_941_, v___x_942_,
        );
        return v___x_943_;
    }
}
pub unsafe fn l___private_Lean_Meta_Sym_Arith_Poly_0__Lean_Grind_CommRing_Poly_toExpr_goTerm(
    mut v_k_944_: *mut LeanObject,
    mut v_m_945_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_946_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_947_: u8 = 0;
    v___x_946_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Grind_CommRing_Mon_toExpr___closed__0),
        core::ptr::addr_of_mut!(l_Lean_Grind_CommRing_Mon_toExpr___closed__0_once),
        _init_l_Lean_Grind_CommRing_Mon_toExpr___closed__0,
    );
    v___x_947_ = lean_int_dec_eq(v_k_944_, v___x_946_);
    if v___x_947_ == 0 {
        let mut v___x_948_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_949_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_950_: *mut LeanObject = core::ptr::null_mut();
        v___x_948_ = lean_alloc_ctor(0, 1, (0) as u32);
        lean_ctor_set(v___x_948_, 0, v_k_944_);
        v___x_949_ = l_Lean_Grind_CommRing_Mon_toExpr(v_m_945_);
        v___x_950_ = lean_alloc_ctor(7, 2, (0) as u32);
        lean_ctor_set(v___x_950_, 0, v___x_948_);
        lean_ctor_set(v___x_950_, 1, v___x_949_);
        return v___x_950_;
    } else {
        let mut v___x_951_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_k_944_);
        v___x_951_ = l_Lean_Grind_CommRing_Mon_toExpr(v_m_945_);
        return v___x_951_;
    }
}
pub unsafe fn l___private_Lean_Meta_Sym_Arith_Poly_0__Lean_Grind_CommRing_Poly_toExpr_go(
    mut v_p_952_: *mut LeanObject,
    mut v_acc_953_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_k_954_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_956_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_957_: u8 = 0;
    let mut v___x_958_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_959_: u8 = 0;
    let mut v___x_961_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_962_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_963_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_964_: u8 = 0;
    let mut v_k_965_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v_966_: *mut LeanObject = core::ptr::null_mut();
    let mut v_p_967_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_968_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_969_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_p_952_) == 0 {
                    v_k_954_ = lean_ctor_get(v_p_952_, 0);
                    v_isSharedCheck_964_ = (!lean_is_exclusive(v_p_952_)) as u8;
                    if v_isSharedCheck_964_ == 0 {
                        v___x_956_ = v_p_952_;
                        v_isShared_957_ = v_isSharedCheck_964_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_k_954_);
                        lean_dec(v_p_952_);
                        v___x_956_ = lean_box(0);
                        v_isShared_957_ = v_isSharedCheck_964_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_k_965_ = lean_ctor_get(v_p_952_, 0);
                    lean_inc(v_k_965_);
                    v_v_966_ = lean_ctor_get(v_p_952_, 1);
                    lean_inc(v_v_966_);
                    v_p_967_ = lean_ctor_get(v_p_952_, 2);
                    lean_inc_ref(v_p_967_);
                    lean_dec_ref_known(v_p_952_, 3);
                    v___x_968_ = l___private_Lean_Meta_Sym_Arith_Poly_0__Lean_Grind_CommRing_Poly_toExpr_goTerm(v_k_965_, v_v_966_);
                    v___x_969_ = lean_alloc_ctor(5, 2, (0) as u32);
                    lean_ctor_set(v___x_969_, 0, v_acc_953_);
                    lean_ctor_set(v___x_969_, 1, v___x_968_);
                    v_p_952_ = v_p_967_;
                    v_acc_953_ = v___x_969_;
                    state = 0;
                    continue;
                }
            }
            1 => {
                v___x_958_ = lean_obj_once(
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
                        v_reuseFailAlloc_963_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_963_, 0, v_k_954_);
                        v___x_961_ = v_reuseFailAlloc_963_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_956_);
                    lean_dec(v_k_954_);
                    return v_acc_953_;
                }
            }
            2 => {
                v___x_962_ = lean_alloc_ctor(5, 2, (0) as u32);
                lean_ctor_set(v___x_962_, 0, v_acc_953_);
                lean_ctor_set(v___x_962_, 1, v___x_961_);
                return v___x_962_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Grind_CommRing_Poly_toExpr(mut v_p_971_: *mut LeanObject) -> *mut LeanObject {
    let mut v_k_972_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_974_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_975_: u8 = 0;
    let mut v___x_977_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_978_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_979_: u8 = 0;
    let mut v_k_980_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v_981_: *mut LeanObject = core::ptr::null_mut();
    let mut v_p_982_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_983_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_984_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_p_971_) == 0 {
                    v_k_972_ = lean_ctor_get(v_p_971_, 0);
                    v_isSharedCheck_979_ = (!lean_is_exclusive(v_p_971_)) as u8;
                    if v_isSharedCheck_979_ == 0 {
                        v___x_974_ = v_p_971_;
                        v_isShared_975_ = v_isSharedCheck_979_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_k_972_);
                        lean_dec(v_p_971_);
                        v___x_974_ = lean_box(0);
                        v_isShared_975_ = v_isSharedCheck_979_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_k_980_ = lean_ctor_get(v_p_971_, 0);
                    lean_inc(v_k_980_);
                    v_v_981_ = lean_ctor_get(v_p_971_, 1);
                    lean_inc(v_v_981_);
                    v_p_982_ = lean_ctor_get(v_p_971_, 2);
                    lean_inc_ref(v_p_982_);
                    lean_dec_ref_known(v_p_971_, 3);
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
                    v_reuseFailAlloc_978_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_978_, 0, v_k_972_);
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
    mut v_x_985_: *mut LeanObject,
    mut v_p_986_: *mut LeanObject,
    mut v_max_987_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_v_988_: *mut LeanObject = core::ptr::null_mut();
    let mut v_p_989_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_990_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_991_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_p_986_) == 0 {
                    return v_max_987_;
                } else {
                    v_v_988_ = lean_ctor_get(v_p_986_, 1);
                    v_p_989_ = lean_ctor_get(v_p_986_, 2);
                    v___x_990_ = l_Lean_Grind_CommRing_Mon_degreeOf(v_v_988_, v_x_985_);
                    v___x_991_ = lean_nat_dec_le(v_max_987_, v___x_990_);
                    if v___x_991_ == 0 {
                        lean_dec(v___x_990_);
                        v_p_986_ = v_p_989_;
                        state = 0;
                        continue;
                    } else {
                        lean_dec(v_max_987_);
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
    mut v_x_994_: *mut LeanObject,
    mut v_p_995_: *mut LeanObject,
    mut v_max_996_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_997_: *mut LeanObject = core::ptr::null_mut();
    v_res_997_ = l___private_Lean_Meta_Sym_Arith_Poly_0__Lean_Grind_CommRing_Poly_maxDegreeOf_go(
        v_x_994_, v_p_995_, v_max_996_,
    );
    lean_dec_ref(v_p_995_);
    lean_dec(v_x_994_);
    return v_res_997_;
}
pub unsafe fn l_Lean_Grind_CommRing_Poly_maxDegreeOf(
    mut v_p_998_: *mut LeanObject,
    mut v_x_999_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1000_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1001_: *mut LeanObject = core::ptr::null_mut();
    v___x_1000_ = lean_unsigned_to_nat(0);
    v___x_1001_ = l___private_Lean_Meta_Sym_Arith_Poly_0__Lean_Grind_CommRing_Poly_maxDegreeOf_go(
        v_x_999_,
        v_p_998_,
        v___x_1000_,
    );
    return v___x_1001_;
}
pub unsafe fn l_Lean_Grind_CommRing_Poly_maxDegreeOf___boxed(
    mut v_p_1002_: *mut LeanObject,
    mut v_x_1003_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1004_: *mut LeanObject = core::ptr::null_mut();
    v_res_1004_ = l_Lean_Grind_CommRing_Poly_maxDegreeOf(v_p_1002_, v_x_1003_);
    lean_dec(v_x_1003_);
    lean_dec_ref(v_p_1002_);
    return v_res_1004_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Meta_Sym_Arith_Poly(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Init_Grind_Ring_CommSolver(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Nat_Gcd(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Nat_Lemmas(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Nat_Linear(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_WFTactics(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Meta_Sym_Arith_Poly(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_meta_initialized = true;
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lean_Meta_Sym_Arith_Poly(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Init_Grind_Ring_CommSolver(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Data_Nat_Gcd(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Data_Nat_Lemmas(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Data_Nat_Linear(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_WFTactics(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Sym_Arith_Poly(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Lean_Meta_Sym_Arith_Poly(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Lean_Meta_Sym_Arith_Poly(builtin);
}
