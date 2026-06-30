// Lean compiler output
// Module: Init.Grind.Ring.CommSemiringAdapter
// Imports: Init.Grind.Ring.Envelope Init.Grind.Ring.CommSolver Init.Data.Int.LemmasAux Init.Omega
use crate::ffi::{lean_int_dec_lt, lean_nat_abs, lean_nat_to_int};
use crate::r#gen::Init::Data::Int::Basic::l_Int_pow;
use crate::r#gen::Init::Data::Int::LemmasAux::{
    initialize_Init_Data_Int_LemmasAux, runtime_initialize_Init_Data_Int_LemmasAux,
};
use crate::r#gen::Init::Data::RArray::l_Lean_RArray_getImpl___redArg;
use crate::r#gen::Init::Grind::Ring::CommSolver::{
    initialize_Init_Grind_Ring_CommSolver, l_Lean_Grind_CommRing_Mon_denote___redArg,
    l_Lean_Grind_CommRing_Poly_combine, l_Lean_Grind_CommRing_Poly_mul,
    l_Lean_Grind_CommRing_Poly_mul__nc, l_Lean_Grind_CommRing_Poly_ofMon,
    l_Lean_Grind_CommRing_Poly_ofVar, l_Lean_Grind_CommRing_Poly_pow,
    l_Lean_Grind_CommRing_Poly_pow__nc, l_Lean_Grind_CommRing_instBEqPoly_beq,
    runtime_initialize_Init_Grind_Ring_CommSolver,
};
use crate::r#gen::Init::Grind::Ring::Envelope::{
    initialize_Init_Grind_Ring_Envelope, l_Lean_Grind_Ring_OfSemiring_add___redArg,
    l_Lean_Grind_Ring_OfSemiring_mul___redArg, l_Lean_Grind_Ring_OfSemiring_natCast___redArg,
    l_Lean_Grind_Ring_OfSemiring_npow___redArg, l_Lean_Grind_Ring_OfSemiring_toQ___redArg,
    runtime_initialize_Init_Grind_Ring_Envelope,
};
use crate::r#gen::Init::Omega::{initialize_Init_Omega, runtime_initialize_Init_Omega};
static mut l_Lean_Grind_CommRing_Expr_toPolyS___closed__0_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Grind_CommRing_Expr_toPolyS___closed__0: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Grind_CommRing_Expr_toPolyS___closed__1_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Grind_CommRing_Expr_toPolyS___closed__1: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub unsafe fn l_Lean_Grind_CommRing_Expr_denoteS___redArg(
    mut v_inst_454_: *mut leanh::LeanObject,
    mut v_ctx_455_: *mut leanh::LeanObject,
    mut v_x_456_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    match leanh::lean_obj_tag(v_x_456_) {
        0 => {
            let mut v_ofNat_457_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_k_458_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_459_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_460_: *mut leanh::LeanObject = core::ptr::null_mut();
            v_ofNat_457_ = leanh::lean_ctor_get(v_inst_454_, 3);
            leanh::lean_inc(v_ofNat_457_);
            leanh::lean_dec_ref(v_inst_454_);
            v_k_458_ = leanh::lean_ctor_get(v_x_456_, 0);
            leanh::lean_inc(v_k_458_);
            leanh::lean_dec_ref_known(v_x_456_, 1);
            v___x_459_ = lean_nat_abs(v_k_458_);
            leanh::lean_dec(v_k_458_);
            v___x_460_ = leanh::lean_apply_1(v_ofNat_457_, v___x_459_);
            return v___x_460_;
        }
        1 => {
            let mut v_ofNat_461_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_k_462_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_463_: *mut leanh::LeanObject = core::ptr::null_mut();
            v_ofNat_461_ = leanh::lean_ctor_get(v_inst_454_, 3);
            leanh::lean_inc(v_ofNat_461_);
            leanh::lean_dec_ref(v_inst_454_);
            v_k_462_ = leanh::lean_ctor_get(v_x_456_, 0);
            leanh::lean_inc(v_k_462_);
            leanh::lean_dec_ref_known(v_x_456_, 1);
            v___x_463_ = leanh::lean_apply_1(v_ofNat_461_, v_k_462_);
            return v___x_463_;
        }
        3 => {
            let mut v_i_464_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_465_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec_ref(v_inst_454_);
            v_i_464_ = leanh::lean_ctor_get(v_x_456_, 0);
            leanh::lean_inc(v_i_464_);
            leanh::lean_dec_ref_known(v_x_456_, 1);
            v___x_465_ = l_Lean_RArray_getImpl___redArg(v_ctx_455_, v_i_464_);
            leanh::lean_dec(v_i_464_);
            return v___x_465_;
        }
        5 => {
            let mut v_toAdd_466_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_a_467_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_b_468_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_469_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_470_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_471_: *mut leanh::LeanObject = core::ptr::null_mut();
            v_toAdd_466_ = leanh::lean_ctor_get(v_inst_454_, 0);
            leanh::lean_inc(v_toAdd_466_);
            v_a_467_ = leanh::lean_ctor_get(v_x_456_, 0);
            leanh::lean_inc_ref(v_a_467_);
            v_b_468_ = leanh::lean_ctor_get(v_x_456_, 1);
            leanh::lean_inc_ref(v_b_468_);
            leanh::lean_dec_ref_known(v_x_456_, 2);
            leanh::lean_inc_ref(v_inst_454_);
            v___x_469_ =
                l_Lean_Grind_CommRing_Expr_denoteS___redArg(v_inst_454_, v_ctx_455_, v_a_467_);
            v___x_470_ =
                l_Lean_Grind_CommRing_Expr_denoteS___redArg(v_inst_454_, v_ctx_455_, v_b_468_);
            v___x_471_ = leanh::lean_apply_2(v_toAdd_466_, v___x_469_, v___x_470_);
            return v___x_471_;
        }
        7 => {
            let mut v_toMul_472_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_a_473_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_b_474_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_475_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_476_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_477_: *mut leanh::LeanObject = core::ptr::null_mut();
            v_toMul_472_ = leanh::lean_ctor_get(v_inst_454_, 1);
            leanh::lean_inc(v_toMul_472_);
            v_a_473_ = leanh::lean_ctor_get(v_x_456_, 0);
            leanh::lean_inc_ref(v_a_473_);
            v_b_474_ = leanh::lean_ctor_get(v_x_456_, 1);
            leanh::lean_inc_ref(v_b_474_);
            leanh::lean_dec_ref_known(v_x_456_, 2);
            leanh::lean_inc_ref(v_inst_454_);
            v___x_475_ =
                l_Lean_Grind_CommRing_Expr_denoteS___redArg(v_inst_454_, v_ctx_455_, v_a_473_);
            v___x_476_ =
                l_Lean_Grind_CommRing_Expr_denoteS___redArg(v_inst_454_, v_ctx_455_, v_b_474_);
            v___x_477_ = leanh::lean_apply_2(v_toMul_472_, v___x_475_, v___x_476_);
            return v___x_477_;
        }
        8 => {
            let mut v_npow_478_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_a_479_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_k_480_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_481_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_482_: *mut leanh::LeanObject = core::ptr::null_mut();
            v_npow_478_ = leanh::lean_ctor_get(v_inst_454_, 5);
            leanh::lean_inc(v_npow_478_);
            v_a_479_ = leanh::lean_ctor_get(v_x_456_, 0);
            leanh::lean_inc_ref(v_a_479_);
            v_k_480_ = leanh::lean_ctor_get(v_x_456_, 1);
            leanh::lean_inc(v_k_480_);
            leanh::lean_dec_ref_known(v_x_456_, 2);
            v___x_481_ =
                l_Lean_Grind_CommRing_Expr_denoteS___redArg(v_inst_454_, v_ctx_455_, v_a_479_);
            v___x_482_ = leanh::lean_apply_2(v_npow_478_, v___x_481_, v_k_480_);
            return v___x_482_;
        }
        _ => {
            let mut v_ofNat_483_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_484_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_485_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec_ref(v_x_456_);
            v_ofNat_483_ = leanh::lean_ctor_get(v_inst_454_, 3);
            leanh::lean_inc(v_ofNat_483_);
            leanh::lean_dec_ref(v_inst_454_);
            v___x_484_ = leanh::lean_unsigned_to_nat(0);
            v___x_485_ = leanh::lean_apply_1(v_ofNat_483_, v___x_484_);
            return v___x_485_;
        }
    }
}
pub unsafe fn l_Lean_Grind_CommRing_Expr_denoteS___redArg___boxed(
    mut v_inst_486_: *mut leanh::LeanObject,
    mut v_ctx_487_: *mut leanh::LeanObject,
    mut v_x_488_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_489_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_489_ = l_Lean_Grind_CommRing_Expr_denoteS___redArg(v_inst_486_, v_ctx_487_, v_x_488_);
    leanh::lean_dec_ref(v_ctx_487_);
    return v_res_489_;
}
pub unsafe fn l_Lean_Grind_CommRing_Expr_denoteS(
    mut v_00_u03b1_490_: *mut leanh::LeanObject,
    mut v_inst_491_: *mut leanh::LeanObject,
    mut v_ctx_492_: *mut leanh::LeanObject,
    mut v_x_493_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_494_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_494_ = l_Lean_Grind_CommRing_Expr_denoteS___redArg(v_inst_491_, v_ctx_492_, v_x_493_);
    return v___x_494_;
}
pub unsafe fn l_Lean_Grind_CommRing_Expr_denoteS___boxed(
    mut v_00_u03b1_495_: *mut leanh::LeanObject,
    mut v_inst_496_: *mut leanh::LeanObject,
    mut v_ctx_497_: *mut leanh::LeanObject,
    mut v_x_498_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_499_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_499_ =
        l_Lean_Grind_CommRing_Expr_denoteS(v_00_u03b1_495_, v_inst_496_, v_ctx_497_, v_x_498_);
    leanh::lean_dec_ref(v_ctx_497_);
    return v_res_499_;
}
pub unsafe fn l_Lean_Grind_CommRing_Expr_denoteSAsRing___redArg(
    mut v_inst_500_: *mut leanh::LeanObject,
    mut v_ctx_501_: *mut leanh::LeanObject,
    mut v_x_502_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    match leanh::lean_obj_tag(v_x_502_) {
        0 => {
            let mut v_k_503_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_504_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_505_: *mut leanh::LeanObject = core::ptr::null_mut();
            v_k_503_ = leanh::lean_ctor_get(v_x_502_, 0);
            leanh::lean_inc(v_k_503_);
            leanh::lean_dec_ref_known(v_x_502_, 1);
            v___x_504_ = lean_nat_abs(v_k_503_);
            leanh::lean_dec(v_k_503_);
            v___x_505_ = l_Lean_Grind_Ring_OfSemiring_natCast___redArg(v_inst_500_, v___x_504_);
            return v___x_505_;
        }
        1 => {
            let mut v_k_506_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_507_: *mut leanh::LeanObject = core::ptr::null_mut();
            v_k_506_ = leanh::lean_ctor_get(v_x_502_, 0);
            leanh::lean_inc(v_k_506_);
            leanh::lean_dec_ref_known(v_x_502_, 1);
            v___x_507_ = l_Lean_Grind_Ring_OfSemiring_natCast___redArg(v_inst_500_, v_k_506_);
            return v___x_507_;
        }
        3 => {
            let mut v_i_508_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_509_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_510_: *mut leanh::LeanObject = core::ptr::null_mut();
            v_i_508_ = leanh::lean_ctor_get(v_x_502_, 0);
            leanh::lean_inc(v_i_508_);
            leanh::lean_dec_ref_known(v_x_502_, 1);
            v___x_509_ = l_Lean_RArray_getImpl___redArg(v_ctx_501_, v_i_508_);
            leanh::lean_dec(v_i_508_);
            v___x_510_ = l_Lean_Grind_Ring_OfSemiring_toQ___redArg(v_inst_500_, v___x_509_);
            return v___x_510_;
        }
        5 => {
            let mut v_a_511_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_b_512_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_513_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_514_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_515_: *mut leanh::LeanObject = core::ptr::null_mut();
            v_a_511_ = leanh::lean_ctor_get(v_x_502_, 0);
            leanh::lean_inc_ref(v_a_511_);
            v_b_512_ = leanh::lean_ctor_get(v_x_502_, 1);
            leanh::lean_inc_ref(v_b_512_);
            leanh::lean_dec_ref_known(v_x_502_, 2);
            leanh::lean_inc_ref_n(v_inst_500_, 2);
            v___x_513_ = l_Lean_Grind_CommRing_Expr_denoteSAsRing___redArg(
                v_inst_500_,
                v_ctx_501_,
                v_a_511_,
            );
            v___x_514_ = l_Lean_Grind_CommRing_Expr_denoteSAsRing___redArg(
                v_inst_500_,
                v_ctx_501_,
                v_b_512_,
            );
            v___x_515_ =
                l_Lean_Grind_Ring_OfSemiring_add___redArg(v_inst_500_, v___x_513_, v___x_514_);
            return v___x_515_;
        }
        7 => {
            let mut v_a_516_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_b_517_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_518_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_519_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_520_: *mut leanh::LeanObject = core::ptr::null_mut();
            v_a_516_ = leanh::lean_ctor_get(v_x_502_, 0);
            leanh::lean_inc_ref(v_a_516_);
            v_b_517_ = leanh::lean_ctor_get(v_x_502_, 1);
            leanh::lean_inc_ref(v_b_517_);
            leanh::lean_dec_ref_known(v_x_502_, 2);
            leanh::lean_inc_ref_n(v_inst_500_, 2);
            v___x_518_ = l_Lean_Grind_CommRing_Expr_denoteSAsRing___redArg(
                v_inst_500_,
                v_ctx_501_,
                v_a_516_,
            );
            v___x_519_ = l_Lean_Grind_CommRing_Expr_denoteSAsRing___redArg(
                v_inst_500_,
                v_ctx_501_,
                v_b_517_,
            );
            v___x_520_ =
                l_Lean_Grind_Ring_OfSemiring_mul___redArg(v_inst_500_, v___x_518_, v___x_519_);
            return v___x_520_;
        }
        8 => {
            let mut v_a_521_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_k_522_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_523_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_524_: *mut leanh::LeanObject = core::ptr::null_mut();
            v_a_521_ = leanh::lean_ctor_get(v_x_502_, 0);
            leanh::lean_inc_ref(v_a_521_);
            v_k_522_ = leanh::lean_ctor_get(v_x_502_, 1);
            leanh::lean_inc(v_k_522_);
            leanh::lean_dec_ref_known(v_x_502_, 2);
            leanh::lean_inc_ref(v_inst_500_);
            v___x_523_ = l_Lean_Grind_CommRing_Expr_denoteSAsRing___redArg(
                v_inst_500_,
                v_ctx_501_,
                v_a_521_,
            );
            v___x_524_ =
                l_Lean_Grind_Ring_OfSemiring_npow___redArg(v_inst_500_, v___x_523_, v_k_522_);
            leanh::lean_dec(v_k_522_);
            return v___x_524_;
        }
        _ => {
            let mut v___x_525_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_526_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec_ref(v_x_502_);
            v___x_525_ = leanh::lean_unsigned_to_nat(0);
            v___x_526_ = l_Lean_Grind_Ring_OfSemiring_natCast___redArg(v_inst_500_, v___x_525_);
            return v___x_526_;
        }
    }
}
pub unsafe fn l_Lean_Grind_CommRing_Expr_denoteSAsRing___redArg___boxed(
    mut v_inst_527_: *mut leanh::LeanObject,
    mut v_ctx_528_: *mut leanh::LeanObject,
    mut v_x_529_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_530_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_530_ =
        l_Lean_Grind_CommRing_Expr_denoteSAsRing___redArg(v_inst_527_, v_ctx_528_, v_x_529_);
    leanh::lean_dec_ref(v_ctx_528_);
    return v_res_530_;
}
pub unsafe fn l_Lean_Grind_CommRing_Expr_denoteSAsRing(
    mut v_00_u03b1_531_: *mut leanh::LeanObject,
    mut v_inst_532_: *mut leanh::LeanObject,
    mut v_ctx_533_: *mut leanh::LeanObject,
    mut v_x_534_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_535_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_535_ =
        l_Lean_Grind_CommRing_Expr_denoteSAsRing___redArg(v_inst_532_, v_ctx_533_, v_x_534_);
    return v___x_535_;
}
pub unsafe fn l_Lean_Grind_CommRing_Expr_denoteSAsRing___boxed(
    mut v_00_u03b1_536_: *mut leanh::LeanObject,
    mut v_inst_537_: *mut leanh::LeanObject,
    mut v_ctx_538_: *mut leanh::LeanObject,
    mut v_x_539_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_540_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_540_ = l_Lean_Grind_CommRing_Expr_denoteSAsRing(
        v_00_u03b1_536_,
        v_inst_537_,
        v_ctx_538_,
        v_x_539_,
    );
    leanh::lean_dec_ref(v_ctx_538_);
    return v_res_540_;
}
pub unsafe fn l___private_Init_Grind_Ring_CommSemiringAdapter_0__Lean_Grind_CommRing_Expr_denoteS_match__1_splitter___redArg(
    mut v_x_541_: *mut leanh::LeanObject,
    mut v_h__1_542_: *mut leanh::LeanObject,
    mut v_h__2_543_: *mut leanh::LeanObject,
    mut v_h__3_544_: *mut leanh::LeanObject,
    mut v_h__4_545_: *mut leanh::LeanObject,
    mut v_h__5_546_: *mut leanh::LeanObject,
    mut v_h__6_547_: *mut leanh::LeanObject,
    mut v_h__7_548_: *mut leanh::LeanObject,
    mut v_h__8_549_: *mut leanh::LeanObject,
    mut v_h__9_550_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    match leanh::lean_obj_tag(v_x_541_) {
        0 => {
            let mut v_k_551_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_552_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__9_550_);
            leanh::lean_dec(v_h__8_549_);
            leanh::lean_dec(v_h__7_548_);
            leanh::lean_dec(v_h__6_547_);
            leanh::lean_dec(v_h__5_546_);
            leanh::lean_dec(v_h__4_545_);
            leanh::lean_dec(v_h__3_544_);
            leanh::lean_dec(v_h__2_543_);
            v_k_551_ = leanh::lean_ctor_get(v_x_541_, 0);
            leanh::lean_inc(v_k_551_);
            leanh::lean_dec_ref_known(v_x_541_, 1);
            v___x_552_ = leanh::lean_apply_1(v_h__1_542_, v_k_551_);
            return v___x_552_;
        }
        1 => {
            let mut v_k_553_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_554_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__9_550_);
            leanh::lean_dec(v_h__8_549_);
            leanh::lean_dec(v_h__7_548_);
            leanh::lean_dec(v_h__6_547_);
            leanh::lean_dec(v_h__5_546_);
            leanh::lean_dec(v_h__4_545_);
            leanh::lean_dec(v_h__3_544_);
            leanh::lean_dec(v_h__1_542_);
            v_k_553_ = leanh::lean_ctor_get(v_x_541_, 0);
            leanh::lean_inc(v_k_553_);
            leanh::lean_dec_ref_known(v_x_541_, 1);
            v___x_554_ = leanh::lean_apply_1(v_h__2_543_, v_k_553_);
            return v___x_554_;
        }
        2 => {
            let mut v_k_555_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_556_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__8_549_);
            leanh::lean_dec(v_h__7_548_);
            leanh::lean_dec(v_h__6_547_);
            leanh::lean_dec(v_h__5_546_);
            leanh::lean_dec(v_h__4_545_);
            leanh::lean_dec(v_h__3_544_);
            leanh::lean_dec(v_h__2_543_);
            leanh::lean_dec(v_h__1_542_);
            v_k_555_ = leanh::lean_ctor_get(v_x_541_, 0);
            leanh::lean_inc(v_k_555_);
            leanh::lean_dec_ref_known(v_x_541_, 1);
            v___x_556_ = leanh::lean_apply_1(v_h__9_550_, v_k_555_);
            return v___x_556_;
        }
        3 => {
            let mut v_i_557_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_558_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__9_550_);
            leanh::lean_dec(v_h__8_549_);
            leanh::lean_dec(v_h__7_548_);
            leanh::lean_dec(v_h__6_547_);
            leanh::lean_dec(v_h__5_546_);
            leanh::lean_dec(v_h__4_545_);
            leanh::lean_dec(v_h__2_543_);
            leanh::lean_dec(v_h__1_542_);
            v_i_557_ = leanh::lean_ctor_get(v_x_541_, 0);
            leanh::lean_inc(v_i_557_);
            leanh::lean_dec_ref_known(v_x_541_, 1);
            v___x_558_ = leanh::lean_apply_1(v_h__3_544_, v_i_557_);
            return v___x_558_;
        }
        4 => {
            let mut v_a_559_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_560_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__9_550_);
            leanh::lean_dec(v_h__7_548_);
            leanh::lean_dec(v_h__6_547_);
            leanh::lean_dec(v_h__5_546_);
            leanh::lean_dec(v_h__4_545_);
            leanh::lean_dec(v_h__3_544_);
            leanh::lean_dec(v_h__2_543_);
            leanh::lean_dec(v_h__1_542_);
            v_a_559_ = leanh::lean_ctor_get(v_x_541_, 0);
            leanh::lean_inc_ref(v_a_559_);
            leanh::lean_dec_ref_known(v_x_541_, 1);
            v___x_560_ = leanh::lean_apply_1(v_h__8_549_, v_a_559_);
            return v___x_560_;
        }
        5 => {
            let mut v_a_561_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_b_562_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_563_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__9_550_);
            leanh::lean_dec(v_h__8_549_);
            leanh::lean_dec(v_h__7_548_);
            leanh::lean_dec(v_h__6_547_);
            leanh::lean_dec(v_h__5_546_);
            leanh::lean_dec(v_h__3_544_);
            leanh::lean_dec(v_h__2_543_);
            leanh::lean_dec(v_h__1_542_);
            v_a_561_ = leanh::lean_ctor_get(v_x_541_, 0);
            leanh::lean_inc_ref(v_a_561_);
            v_b_562_ = leanh::lean_ctor_get(v_x_541_, 1);
            leanh::lean_inc_ref(v_b_562_);
            leanh::lean_dec_ref_known(v_x_541_, 2);
            v___x_563_ = leanh::lean_apply_2(v_h__4_545_, v_a_561_, v_b_562_);
            return v___x_563_;
        }
        6 => {
            let mut v_a_564_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_b_565_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_566_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__9_550_);
            leanh::lean_dec(v_h__8_549_);
            leanh::lean_dec(v_h__6_547_);
            leanh::lean_dec(v_h__5_546_);
            leanh::lean_dec(v_h__4_545_);
            leanh::lean_dec(v_h__3_544_);
            leanh::lean_dec(v_h__2_543_);
            leanh::lean_dec(v_h__1_542_);
            v_a_564_ = leanh::lean_ctor_get(v_x_541_, 0);
            leanh::lean_inc_ref(v_a_564_);
            v_b_565_ = leanh::lean_ctor_get(v_x_541_, 1);
            leanh::lean_inc_ref(v_b_565_);
            leanh::lean_dec_ref_known(v_x_541_, 2);
            v___x_566_ = leanh::lean_apply_2(v_h__7_548_, v_a_564_, v_b_565_);
            return v___x_566_;
        }
        7 => {
            let mut v_a_567_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_b_568_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_569_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__9_550_);
            leanh::lean_dec(v_h__8_549_);
            leanh::lean_dec(v_h__7_548_);
            leanh::lean_dec(v_h__6_547_);
            leanh::lean_dec(v_h__4_545_);
            leanh::lean_dec(v_h__3_544_);
            leanh::lean_dec(v_h__2_543_);
            leanh::lean_dec(v_h__1_542_);
            v_a_567_ = leanh::lean_ctor_get(v_x_541_, 0);
            leanh::lean_inc_ref(v_a_567_);
            v_b_568_ = leanh::lean_ctor_get(v_x_541_, 1);
            leanh::lean_inc_ref(v_b_568_);
            leanh::lean_dec_ref_known(v_x_541_, 2);
            v___x_569_ = leanh::lean_apply_2(v_h__5_546_, v_a_567_, v_b_568_);
            return v___x_569_;
        }
        _ => {
            let mut v_a_570_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_k_571_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_572_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__9_550_);
            leanh::lean_dec(v_h__8_549_);
            leanh::lean_dec(v_h__7_548_);
            leanh::lean_dec(v_h__5_546_);
            leanh::lean_dec(v_h__4_545_);
            leanh::lean_dec(v_h__3_544_);
            leanh::lean_dec(v_h__2_543_);
            leanh::lean_dec(v_h__1_542_);
            v_a_570_ = leanh::lean_ctor_get(v_x_541_, 0);
            leanh::lean_inc_ref(v_a_570_);
            v_k_571_ = leanh::lean_ctor_get(v_x_541_, 1);
            leanh::lean_inc(v_k_571_);
            leanh::lean_dec_ref_known(v_x_541_, 2);
            v___x_572_ = leanh::lean_apply_2(v_h__6_547_, v_a_570_, v_k_571_);
            return v___x_572_;
        }
    }
}
pub unsafe fn l___private_Init_Grind_Ring_CommSemiringAdapter_0__Lean_Grind_CommRing_Expr_denoteS_match__1_splitter(
    mut v_motive_573_: *mut leanh::LeanObject,
    mut v_x_574_: *mut leanh::LeanObject,
    mut v_h__1_575_: *mut leanh::LeanObject,
    mut v_h__2_576_: *mut leanh::LeanObject,
    mut v_h__3_577_: *mut leanh::LeanObject,
    mut v_h__4_578_: *mut leanh::LeanObject,
    mut v_h__5_579_: *mut leanh::LeanObject,
    mut v_h__6_580_: *mut leanh::LeanObject,
    mut v_h__7_581_: *mut leanh::LeanObject,
    mut v_h__8_582_: *mut leanh::LeanObject,
    mut v_h__9_583_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    match leanh::lean_obj_tag(v_x_574_) {
        0 => {
            let mut v_k_584_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_585_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__9_583_);
            leanh::lean_dec(v_h__8_582_);
            leanh::lean_dec(v_h__7_581_);
            leanh::lean_dec(v_h__6_580_);
            leanh::lean_dec(v_h__5_579_);
            leanh::lean_dec(v_h__4_578_);
            leanh::lean_dec(v_h__3_577_);
            leanh::lean_dec(v_h__2_576_);
            v_k_584_ = leanh::lean_ctor_get(v_x_574_, 0);
            leanh::lean_inc(v_k_584_);
            leanh::lean_dec_ref_known(v_x_574_, 1);
            v___x_585_ = leanh::lean_apply_1(v_h__1_575_, v_k_584_);
            return v___x_585_;
        }
        1 => {
            let mut v_k_586_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_587_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__9_583_);
            leanh::lean_dec(v_h__8_582_);
            leanh::lean_dec(v_h__7_581_);
            leanh::lean_dec(v_h__6_580_);
            leanh::lean_dec(v_h__5_579_);
            leanh::lean_dec(v_h__4_578_);
            leanh::lean_dec(v_h__3_577_);
            leanh::lean_dec(v_h__1_575_);
            v_k_586_ = leanh::lean_ctor_get(v_x_574_, 0);
            leanh::lean_inc(v_k_586_);
            leanh::lean_dec_ref_known(v_x_574_, 1);
            v___x_587_ = leanh::lean_apply_1(v_h__2_576_, v_k_586_);
            return v___x_587_;
        }
        2 => {
            let mut v_k_588_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_589_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__8_582_);
            leanh::lean_dec(v_h__7_581_);
            leanh::lean_dec(v_h__6_580_);
            leanh::lean_dec(v_h__5_579_);
            leanh::lean_dec(v_h__4_578_);
            leanh::lean_dec(v_h__3_577_);
            leanh::lean_dec(v_h__2_576_);
            leanh::lean_dec(v_h__1_575_);
            v_k_588_ = leanh::lean_ctor_get(v_x_574_, 0);
            leanh::lean_inc(v_k_588_);
            leanh::lean_dec_ref_known(v_x_574_, 1);
            v___x_589_ = leanh::lean_apply_1(v_h__9_583_, v_k_588_);
            return v___x_589_;
        }
        3 => {
            let mut v_i_590_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_591_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__9_583_);
            leanh::lean_dec(v_h__8_582_);
            leanh::lean_dec(v_h__7_581_);
            leanh::lean_dec(v_h__6_580_);
            leanh::lean_dec(v_h__5_579_);
            leanh::lean_dec(v_h__4_578_);
            leanh::lean_dec(v_h__2_576_);
            leanh::lean_dec(v_h__1_575_);
            v_i_590_ = leanh::lean_ctor_get(v_x_574_, 0);
            leanh::lean_inc(v_i_590_);
            leanh::lean_dec_ref_known(v_x_574_, 1);
            v___x_591_ = leanh::lean_apply_1(v_h__3_577_, v_i_590_);
            return v___x_591_;
        }
        4 => {
            let mut v_a_592_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_593_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__9_583_);
            leanh::lean_dec(v_h__7_581_);
            leanh::lean_dec(v_h__6_580_);
            leanh::lean_dec(v_h__5_579_);
            leanh::lean_dec(v_h__4_578_);
            leanh::lean_dec(v_h__3_577_);
            leanh::lean_dec(v_h__2_576_);
            leanh::lean_dec(v_h__1_575_);
            v_a_592_ = leanh::lean_ctor_get(v_x_574_, 0);
            leanh::lean_inc_ref(v_a_592_);
            leanh::lean_dec_ref_known(v_x_574_, 1);
            v___x_593_ = leanh::lean_apply_1(v_h__8_582_, v_a_592_);
            return v___x_593_;
        }
        5 => {
            let mut v_a_594_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_b_595_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_596_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__9_583_);
            leanh::lean_dec(v_h__8_582_);
            leanh::lean_dec(v_h__7_581_);
            leanh::lean_dec(v_h__6_580_);
            leanh::lean_dec(v_h__5_579_);
            leanh::lean_dec(v_h__3_577_);
            leanh::lean_dec(v_h__2_576_);
            leanh::lean_dec(v_h__1_575_);
            v_a_594_ = leanh::lean_ctor_get(v_x_574_, 0);
            leanh::lean_inc_ref(v_a_594_);
            v_b_595_ = leanh::lean_ctor_get(v_x_574_, 1);
            leanh::lean_inc_ref(v_b_595_);
            leanh::lean_dec_ref_known(v_x_574_, 2);
            v___x_596_ = leanh::lean_apply_2(v_h__4_578_, v_a_594_, v_b_595_);
            return v___x_596_;
        }
        6 => {
            let mut v_a_597_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_b_598_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_599_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__9_583_);
            leanh::lean_dec(v_h__8_582_);
            leanh::lean_dec(v_h__6_580_);
            leanh::lean_dec(v_h__5_579_);
            leanh::lean_dec(v_h__4_578_);
            leanh::lean_dec(v_h__3_577_);
            leanh::lean_dec(v_h__2_576_);
            leanh::lean_dec(v_h__1_575_);
            v_a_597_ = leanh::lean_ctor_get(v_x_574_, 0);
            leanh::lean_inc_ref(v_a_597_);
            v_b_598_ = leanh::lean_ctor_get(v_x_574_, 1);
            leanh::lean_inc_ref(v_b_598_);
            leanh::lean_dec_ref_known(v_x_574_, 2);
            v___x_599_ = leanh::lean_apply_2(v_h__7_581_, v_a_597_, v_b_598_);
            return v___x_599_;
        }
        7 => {
            let mut v_a_600_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_b_601_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_602_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__9_583_);
            leanh::lean_dec(v_h__8_582_);
            leanh::lean_dec(v_h__7_581_);
            leanh::lean_dec(v_h__6_580_);
            leanh::lean_dec(v_h__4_578_);
            leanh::lean_dec(v_h__3_577_);
            leanh::lean_dec(v_h__2_576_);
            leanh::lean_dec(v_h__1_575_);
            v_a_600_ = leanh::lean_ctor_get(v_x_574_, 0);
            leanh::lean_inc_ref(v_a_600_);
            v_b_601_ = leanh::lean_ctor_get(v_x_574_, 1);
            leanh::lean_inc_ref(v_b_601_);
            leanh::lean_dec_ref_known(v_x_574_, 2);
            v___x_602_ = leanh::lean_apply_2(v_h__5_579_, v_a_600_, v_b_601_);
            return v___x_602_;
        }
        _ => {
            let mut v_a_603_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_k_604_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_605_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__9_583_);
            leanh::lean_dec(v_h__8_582_);
            leanh::lean_dec(v_h__7_581_);
            leanh::lean_dec(v_h__5_579_);
            leanh::lean_dec(v_h__4_578_);
            leanh::lean_dec(v_h__3_577_);
            leanh::lean_dec(v_h__2_576_);
            leanh::lean_dec(v_h__1_575_);
            v_a_603_ = leanh::lean_ctor_get(v_x_574_, 0);
            leanh::lean_inc_ref(v_a_603_);
            v_k_604_ = leanh::lean_ctor_get(v_x_574_, 1);
            leanh::lean_inc(v_k_604_);
            leanh::lean_dec_ref_known(v_x_574_, 2);
            v___x_605_ = leanh::lean_apply_2(v_h__6_580_, v_a_603_, v_k_604_);
            return v___x_605_;
        }
    }
}
pub unsafe fn l_Nat_cast___at___00Lean_Grind_CommRing_Expr_toPolyS_spec__0(
    mut v_a_606_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_607_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_607_ = lean_nat_to_int(v_a_606_);
    return v___x_607_;
}
pub unsafe fn _init_l_Lean_Grind_CommRing_Expr_toPolyS___closed__0() -> *mut leanh::LeanObject
{
    let mut v___x_608_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_609_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_608_ = leanh::lean_unsigned_to_nat(0);
    v___x_609_ = lean_nat_to_int(v___x_608_);
    return v___x_609_;
}
pub unsafe fn _init_l_Lean_Grind_CommRing_Expr_toPolyS___closed__1() -> *mut leanh::LeanObject
{
    let mut v___x_610_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_611_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_610_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Grind_CommRing_Expr_toPolyS___closed__0),
        core::ptr::addr_of_mut!(l_Lean_Grind_CommRing_Expr_toPolyS___closed__0_once),
        _init_l_Lean_Grind_CommRing_Expr_toPolyS___closed__0,
    );
    v___x_611_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_611_, 0, v___x_610_);
    return v___x_611_;
}
pub unsafe fn l_Lean_Grind_CommRing_Expr_toPolyS(
    mut v_x_612_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_k_613_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_615_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_616_: u8 = 0;
    let mut v___x_617_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_618_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_620_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_621_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_622_: u8 = 0;
    let mut v_k_623_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_625_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_626_: u8 = 0;
    let mut v___x_627_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_629_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_630_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_631_: u8 = 0;
    let mut v_i_632_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_633_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_634_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_b_635_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_636_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_637_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_638_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_639_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_b_640_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_641_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_642_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_643_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_644_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_645_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_646_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_648_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_649_: u8 = 0;
    let mut v___x_650_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_651_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_652_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_654_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_655_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_656_: u8 = 0;
    let mut v_k_657_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_659_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_660_: u8 = 0;
    let mut v_i_661_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_663_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_664_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_665_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_666_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_667_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_668_: u8 = 0;
    let mut v_unused_669_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_670_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_671_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_672_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_673_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => match leanh::lean_obj_tag(v_x_612_) {
                0 => {
                    v_k_613_ = leanh::lean_ctor_get(v_x_612_, 0);
                    v_isSharedCheck_622_ = (!leanh::lean_is_exclusive(v_x_612_)) as u8;
                    if v_isSharedCheck_622_ == 0 {
                        v___x_615_ = v_x_612_;
                        v_isShared_616_ = v_isSharedCheck_622_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_k_613_);
                        leanh::lean_dec(v_x_612_);
                        v___x_615_ = leanh::lean_box(0);
                        v_isShared_616_ = v_isSharedCheck_622_;
                        state = 1;
                        continue;
                    }
                }
                1 => {
                    v_k_623_ = leanh::lean_ctor_get(v_x_612_, 0);
                    v_isSharedCheck_631_ = (!leanh::lean_is_exclusive(v_x_612_)) as u8;
                    if v_isSharedCheck_631_ == 0 {
                        v___x_625_ = v_x_612_;
                        v_isShared_626_ = v_isSharedCheck_631_;
                        state = 3;
                        continue;
                    } else {
                        leanh::lean_inc(v_k_623_);
                        leanh::lean_dec(v_x_612_);
                        v___x_625_ = leanh::lean_box(0);
                        v_isShared_626_ = v_isSharedCheck_631_;
                        state = 3;
                        continue;
                    }
                }
                3 => {
                    v_i_632_ = leanh::lean_ctor_get(v_x_612_, 0);
                    leanh::lean_inc(v_i_632_);
                    leanh::lean_dec_ref_known(v_x_612_, 1);
                    v___x_633_ = l_Lean_Grind_CommRing_Poly_ofVar(v_i_632_);
                    return v___x_633_;
                }
                5 => {
                    v_a_634_ = leanh::lean_ctor_get(v_x_612_, 0);
                    leanh::lean_inc_ref(v_a_634_);
                    v_b_635_ = leanh::lean_ctor_get(v_x_612_, 1);
                    leanh::lean_inc_ref(v_b_635_);
                    leanh::lean_dec_ref_known(v_x_612_, 2);
                    v___x_636_ = l_Lean_Grind_CommRing_Expr_toPolyS(v_a_634_);
                    v___x_637_ = l_Lean_Grind_CommRing_Expr_toPolyS(v_b_635_);
                    v___x_638_ = l_Lean_Grind_CommRing_Poly_combine(v___x_636_, v___x_637_);
                    return v___x_638_;
                }
                7 => {
                    v_a_639_ = leanh::lean_ctor_get(v_x_612_, 0);
                    leanh::lean_inc_ref(v_a_639_);
                    v_b_640_ = leanh::lean_ctor_get(v_x_612_, 1);
                    leanh::lean_inc_ref(v_b_640_);
                    leanh::lean_dec_ref_known(v_x_612_, 2);
                    v___x_641_ = l_Lean_Grind_CommRing_Expr_toPolyS(v_a_639_);
                    v___x_642_ = l_Lean_Grind_CommRing_Expr_toPolyS(v_b_640_);
                    v___x_643_ = l_Lean_Grind_CommRing_Poly_mul(v___x_641_, v___x_642_);
                    return v___x_643_;
                }
                8 => {
                    v_a_644_ = leanh::lean_ctor_get(v_x_612_, 0);
                    leanh::lean_inc_ref(v_a_644_);
                    match leanh::lean_obj_tag(v_a_644_) {
                        0 => {
                            v_k_645_ = leanh::lean_ctor_get(v_x_612_, 1);
                            leanh::lean_inc(v_k_645_);
                            leanh::lean_dec_ref_known(v_x_612_, 2);
                            v_k_646_ = leanh::lean_ctor_get(v_a_644_, 0);
                            v_isSharedCheck_656_ =
                                (!leanh::lean_is_exclusive(v_a_644_)) as u8;
                            if v_isSharedCheck_656_ == 0 {
                                v___x_648_ = v_a_644_;
                                v_isShared_649_ = v_isSharedCheck_656_;
                                state = 5;
                                continue;
                            } else {
                                leanh::lean_inc(v_k_646_);
                                leanh::lean_dec(v_a_644_);
                                v___x_648_ = leanh::lean_box(0);
                                v_isShared_649_ = v_isSharedCheck_656_;
                                state = 5;
                                continue;
                            }
                        }
                        3 => {
                            v_k_657_ = leanh::lean_ctor_get(v_x_612_, 1);
                            v_isSharedCheck_668_ =
                                (!leanh::lean_is_exclusive(v_x_612_)) as u8;
                            if v_isSharedCheck_668_ == 0 {
                                v_unused_669_ = leanh::lean_ctor_get(v_x_612_, 0);
                                leanh::lean_dec(v_unused_669_);
                                v___x_659_ = v_x_612_;
                                v_isShared_660_ = v_isSharedCheck_668_;
                                state = 7;
                                continue;
                            } else {
                                leanh::lean_inc(v_k_657_);
                                leanh::lean_dec(v_x_612_);
                                v___x_659_ = leanh::lean_box(0);
                                v_isShared_660_ = v_isSharedCheck_668_;
                                state = 7;
                                continue;
                            }
                        }
                        _ => {
                            v_k_670_ = leanh::lean_ctor_get(v_x_612_, 1);
                            leanh::lean_inc(v_k_670_);
                            leanh::lean_dec_ref_known(v_x_612_, 2);
                            v___x_671_ = l_Lean_Grind_CommRing_Expr_toPolyS(v_a_644_);
                            v___x_672_ = l_Lean_Grind_CommRing_Poly_pow(v___x_671_, v_k_670_);
                            leanh::lean_dec(v_k_670_);
                            return v___x_672_;
                        }
                    }
                }
                _ => {
                    leanh::lean_dec_ref(v_x_612_);
                    v___x_673_ = leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(l_Lean_Grind_CommRing_Expr_toPolyS___closed__1),
                        core::ptr::addr_of_mut!(
                            l_Lean_Grind_CommRing_Expr_toPolyS___closed__1_once
                        ),
                        _init_l_Lean_Grind_CommRing_Expr_toPolyS___closed__1,
                    );
                    return v___x_673_;
                }
            },
            1 => {
                v___x_617_ = lean_nat_abs(v_k_613_);
                leanh::lean_dec(v_k_613_);
                v___x_618_ = lean_nat_to_int(v___x_617_);
                if v_isShared_616_ == 0 {
                    leanh::lean_ctor_set(v___x_615_, 0, v___x_618_);
                    v___x_620_ = v___x_615_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_621_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_621_, 0, v___x_618_);
                    v___x_620_ = v_reuseFailAlloc_621_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_620_;
            }
            3 => {
                v___x_627_ = lean_nat_to_int(v_k_623_);
                if v_isShared_626_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_625_, 0);
                    leanh::lean_ctor_set(v___x_625_, 0, v___x_627_);
                    v___x_629_ = v___x_625_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_630_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_630_, 0, v___x_627_);
                    v___x_629_ = v_reuseFailAlloc_630_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_629_;
            }
            5 => {
                v___x_650_ = lean_nat_abs(v_k_646_);
                leanh::lean_dec(v_k_646_);
                v___x_651_ = lean_nat_to_int(v___x_650_);
                v___x_652_ = l_Int_pow(v___x_651_, v_k_645_);
                leanh::lean_dec(v_k_645_);
                leanh::lean_dec(v___x_651_);
                if v_isShared_649_ == 0 {
                    leanh::lean_ctor_set(v___x_648_, 0, v___x_652_);
                    v___x_654_ = v___x_648_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_655_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_655_, 0, v___x_652_);
                    v___x_654_ = v_reuseFailAlloc_655_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_654_;
            }
            7 => {
                v_i_661_ = leanh::lean_ctor_get(v_a_644_, 0);
                leanh::lean_inc(v_i_661_);
                leanh::lean_dec_ref_known(v_a_644_, 1);
                if v_isShared_660_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_659_, 0);
                    leanh::lean_ctor_set(v___x_659_, 0, v_i_661_);
                    v___x_663_ = v___x_659_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_667_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_667_, 0, v_i_661_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_667_, 1, v_k_657_);
                    v___x_663_ = v_reuseFailAlloc_667_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                v___x_664_ = leanh::lean_box(0);
                v___x_665_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_665_, 0, v___x_663_);
                leanh::lean_ctor_set(v___x_665_, 1, v___x_664_);
                v___x_666_ = l_Lean_Grind_CommRing_Poly_ofMon(v___x_665_);
                return v___x_666_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Grind_CommRing_Expr_toPolyS__nc(
    mut v_x_674_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_k_675_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_677_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_678_: u8 = 0;
    let mut v___x_679_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_680_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_682_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_683_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_684_: u8 = 0;
    let mut v_k_685_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_687_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_688_: u8 = 0;
    let mut v___x_689_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_691_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_692_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_693_: u8 = 0;
    let mut v_i_694_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_695_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_696_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_b_697_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_698_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_699_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_700_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_701_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_b_702_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_703_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_704_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_705_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_706_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_707_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_708_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_710_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_711_: u8 = 0;
    let mut v___x_712_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_713_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_714_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_716_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_717_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_718_: u8 = 0;
    let mut v_k_719_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_721_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_722_: u8 = 0;
    let mut v_i_723_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_725_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_726_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_727_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_728_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_729_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_730_: u8 = 0;
    let mut v_unused_731_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_732_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_733_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_734_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_735_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => match leanh::lean_obj_tag(v_x_674_) {
                0 => {
                    v_k_675_ = leanh::lean_ctor_get(v_x_674_, 0);
                    v_isSharedCheck_684_ = (!leanh::lean_is_exclusive(v_x_674_)) as u8;
                    if v_isSharedCheck_684_ == 0 {
                        v___x_677_ = v_x_674_;
                        v_isShared_678_ = v_isSharedCheck_684_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_k_675_);
                        leanh::lean_dec(v_x_674_);
                        v___x_677_ = leanh::lean_box(0);
                        v_isShared_678_ = v_isSharedCheck_684_;
                        state = 1;
                        continue;
                    }
                }
                1 => {
                    v_k_685_ = leanh::lean_ctor_get(v_x_674_, 0);
                    v_isSharedCheck_693_ = (!leanh::lean_is_exclusive(v_x_674_)) as u8;
                    if v_isSharedCheck_693_ == 0 {
                        v___x_687_ = v_x_674_;
                        v_isShared_688_ = v_isSharedCheck_693_;
                        state = 3;
                        continue;
                    } else {
                        leanh::lean_inc(v_k_685_);
                        leanh::lean_dec(v_x_674_);
                        v___x_687_ = leanh::lean_box(0);
                        v_isShared_688_ = v_isSharedCheck_693_;
                        state = 3;
                        continue;
                    }
                }
                3 => {
                    v_i_694_ = leanh::lean_ctor_get(v_x_674_, 0);
                    leanh::lean_inc(v_i_694_);
                    leanh::lean_dec_ref_known(v_x_674_, 1);
                    v___x_695_ = l_Lean_Grind_CommRing_Poly_ofVar(v_i_694_);
                    return v___x_695_;
                }
                5 => {
                    v_a_696_ = leanh::lean_ctor_get(v_x_674_, 0);
                    leanh::lean_inc_ref(v_a_696_);
                    v_b_697_ = leanh::lean_ctor_get(v_x_674_, 1);
                    leanh::lean_inc_ref(v_b_697_);
                    leanh::lean_dec_ref_known(v_x_674_, 2);
                    v___x_698_ = l_Lean_Grind_CommRing_Expr_toPolyS__nc(v_a_696_);
                    v___x_699_ = l_Lean_Grind_CommRing_Expr_toPolyS__nc(v_b_697_);
                    v___x_700_ = l_Lean_Grind_CommRing_Poly_combine(v___x_698_, v___x_699_);
                    return v___x_700_;
                }
                7 => {
                    v_a_701_ = leanh::lean_ctor_get(v_x_674_, 0);
                    leanh::lean_inc_ref(v_a_701_);
                    v_b_702_ = leanh::lean_ctor_get(v_x_674_, 1);
                    leanh::lean_inc_ref(v_b_702_);
                    leanh::lean_dec_ref_known(v_x_674_, 2);
                    v___x_703_ = l_Lean_Grind_CommRing_Expr_toPolyS__nc(v_a_701_);
                    v___x_704_ = l_Lean_Grind_CommRing_Expr_toPolyS__nc(v_b_702_);
                    v___x_705_ = l_Lean_Grind_CommRing_Poly_mul__nc(v___x_703_, v___x_704_);
                    return v___x_705_;
                }
                8 => {
                    v_a_706_ = leanh::lean_ctor_get(v_x_674_, 0);
                    leanh::lean_inc_ref(v_a_706_);
                    match leanh::lean_obj_tag(v_a_706_) {
                        0 => {
                            v_k_707_ = leanh::lean_ctor_get(v_x_674_, 1);
                            leanh::lean_inc(v_k_707_);
                            leanh::lean_dec_ref_known(v_x_674_, 2);
                            v_k_708_ = leanh::lean_ctor_get(v_a_706_, 0);
                            v_isSharedCheck_718_ =
                                (!leanh::lean_is_exclusive(v_a_706_)) as u8;
                            if v_isSharedCheck_718_ == 0 {
                                v___x_710_ = v_a_706_;
                                v_isShared_711_ = v_isSharedCheck_718_;
                                state = 5;
                                continue;
                            } else {
                                leanh::lean_inc(v_k_708_);
                                leanh::lean_dec(v_a_706_);
                                v___x_710_ = leanh::lean_box(0);
                                v_isShared_711_ = v_isSharedCheck_718_;
                                state = 5;
                                continue;
                            }
                        }
                        3 => {
                            v_k_719_ = leanh::lean_ctor_get(v_x_674_, 1);
                            v_isSharedCheck_730_ =
                                (!leanh::lean_is_exclusive(v_x_674_)) as u8;
                            if v_isSharedCheck_730_ == 0 {
                                v_unused_731_ = leanh::lean_ctor_get(v_x_674_, 0);
                                leanh::lean_dec(v_unused_731_);
                                v___x_721_ = v_x_674_;
                                v_isShared_722_ = v_isSharedCheck_730_;
                                state = 7;
                                continue;
                            } else {
                                leanh::lean_inc(v_k_719_);
                                leanh::lean_dec(v_x_674_);
                                v___x_721_ = leanh::lean_box(0);
                                v_isShared_722_ = v_isSharedCheck_730_;
                                state = 7;
                                continue;
                            }
                        }
                        _ => {
                            v_k_732_ = leanh::lean_ctor_get(v_x_674_, 1);
                            leanh::lean_inc(v_k_732_);
                            leanh::lean_dec_ref_known(v_x_674_, 2);
                            v___x_733_ = l_Lean_Grind_CommRing_Expr_toPolyS__nc(v_a_706_);
                            v___x_734_ = l_Lean_Grind_CommRing_Poly_pow__nc(v___x_733_, v_k_732_);
                            leanh::lean_dec(v_k_732_);
                            return v___x_734_;
                        }
                    }
                }
                _ => {
                    leanh::lean_dec_ref(v_x_674_);
                    v___x_735_ = leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(l_Lean_Grind_CommRing_Expr_toPolyS___closed__1),
                        core::ptr::addr_of_mut!(
                            l_Lean_Grind_CommRing_Expr_toPolyS___closed__1_once
                        ),
                        _init_l_Lean_Grind_CommRing_Expr_toPolyS___closed__1,
                    );
                    return v___x_735_;
                }
            },
            1 => {
                v___x_679_ = lean_nat_abs(v_k_675_);
                leanh::lean_dec(v_k_675_);
                v___x_680_ = lean_nat_to_int(v___x_679_);
                if v_isShared_678_ == 0 {
                    leanh::lean_ctor_set(v___x_677_, 0, v___x_680_);
                    v___x_682_ = v___x_677_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_683_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_683_, 0, v___x_680_);
                    v___x_682_ = v_reuseFailAlloc_683_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_682_;
            }
            3 => {
                v___x_689_ = lean_nat_to_int(v_k_685_);
                if v_isShared_688_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_687_, 0);
                    leanh::lean_ctor_set(v___x_687_, 0, v___x_689_);
                    v___x_691_ = v___x_687_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_692_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_692_, 0, v___x_689_);
                    v___x_691_ = v_reuseFailAlloc_692_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_691_;
            }
            5 => {
                v___x_712_ = lean_nat_abs(v_k_708_);
                leanh::lean_dec(v_k_708_);
                v___x_713_ = lean_nat_to_int(v___x_712_);
                v___x_714_ = l_Int_pow(v___x_713_, v_k_707_);
                leanh::lean_dec(v_k_707_);
                leanh::lean_dec(v___x_713_);
                if v_isShared_711_ == 0 {
                    leanh::lean_ctor_set(v___x_710_, 0, v___x_714_);
                    v___x_716_ = v___x_710_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_717_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_717_, 0, v___x_714_);
                    v___x_716_ = v_reuseFailAlloc_717_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_716_;
            }
            7 => {
                v_i_723_ = leanh::lean_ctor_get(v_a_706_, 0);
                leanh::lean_inc(v_i_723_);
                leanh::lean_dec_ref_known(v_a_706_, 1);
                if v_isShared_722_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_721_, 0);
                    leanh::lean_ctor_set(v___x_721_, 0, v_i_723_);
                    v___x_725_ = v___x_721_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_729_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_729_, 0, v_i_723_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_729_, 1, v_k_719_);
                    v___x_725_ = v_reuseFailAlloc_729_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                v___x_726_ = leanh::lean_box(0);
                v___x_727_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_727_, 0, v___x_725_);
                leanh::lean_ctor_set(v___x_727_, 1, v___x_726_);
                v___x_728_ = l_Lean_Grind_CommRing_Poly_ofMon(v___x_727_);
                return v___x_728_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Grind_CommRing_denoteSInt___redArg(
    mut v_inst_736_: *mut leanh::LeanObject,
    mut v_k_737_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_738_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_739_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_740_: u8 = 0;
    v___x_738_ = leanh::lean_unsigned_to_nat(0);
    v___x_739_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Grind_CommRing_Expr_toPolyS___closed__0),
        core::ptr::addr_of_mut!(l_Lean_Grind_CommRing_Expr_toPolyS___closed__0_once),
        _init_l_Lean_Grind_CommRing_Expr_toPolyS___closed__0,
    );
    v___x_740_ = lean_int_dec_lt(v_k_737_, v___x_739_);
    if v___x_740_ == 0 {
        let mut v_ofNat_741_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_742_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_743_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_ofNat_741_ = leanh::lean_ctor_get(v_inst_736_, 3);
        leanh::lean_inc(v_ofNat_741_);
        leanh::lean_dec_ref(v_inst_736_);
        v___x_742_ = lean_nat_abs(v_k_737_);
        v___x_743_ = leanh::lean_apply_1(v_ofNat_741_, v___x_742_);
        return v___x_743_;
    } else {
        let mut v_ofNat_744_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_745_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_ofNat_744_ = leanh::lean_ctor_get(v_inst_736_, 3);
        leanh::lean_inc(v_ofNat_744_);
        leanh::lean_dec_ref(v_inst_736_);
        v___x_745_ = leanh::lean_apply_1(v_ofNat_744_, v___x_738_);
        return v___x_745_;
    }
}
pub unsafe fn l_Lean_Grind_CommRing_denoteSInt___redArg___boxed(
    mut v_inst_746_: *mut leanh::LeanObject,
    mut v_k_747_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_748_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_748_ = l_Lean_Grind_CommRing_denoteSInt___redArg(v_inst_746_, v_k_747_);
    leanh::lean_dec(v_k_747_);
    return v_res_748_;
}
pub unsafe fn l_Lean_Grind_CommRing_denoteSInt(
    mut v_00_u03b1_749_: *mut leanh::LeanObject,
    mut v_inst_750_: *mut leanh::LeanObject,
    mut v_k_751_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_752_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_752_ = l_Lean_Grind_CommRing_denoteSInt___redArg(v_inst_750_, v_k_751_);
    return v___x_752_;
}
pub unsafe fn l_Lean_Grind_CommRing_denoteSInt___boxed(
    mut v_00_u03b1_753_: *mut leanh::LeanObject,
    mut v_inst_754_: *mut leanh::LeanObject,
    mut v_k_755_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_756_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_756_ = l_Lean_Grind_CommRing_denoteSInt(v_00_u03b1_753_, v_inst_754_, v_k_755_);
    leanh::lean_dec(v_k_755_);
    return v_res_756_;
}
pub unsafe fn l_Lean_Grind_CommRing_Poly_denoteS___redArg(
    mut v_inst_757_: *mut leanh::LeanObject,
    mut v_ctx_758_: *mut leanh::LeanObject,
    mut v_p_759_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_p_759_) == 0 {
        let mut v_k_760_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_761_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_k_760_ = leanh::lean_ctor_get(v_p_759_, 0);
        leanh::lean_inc(v_k_760_);
        leanh::lean_dec_ref_known(v_p_759_, 1);
        v___x_761_ = l_Lean_Grind_CommRing_denoteSInt___redArg(v_inst_757_, v_k_760_);
        leanh::lean_dec(v_k_760_);
        return v___x_761_;
    } else {
        let mut v_toAdd_762_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_toMul_763_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_k_764_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_v_765_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_p_766_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_767_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_768_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_769_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_770_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_771_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_toAdd_762_ = leanh::lean_ctor_get(v_inst_757_, 0);
        leanh::lean_inc(v_toAdd_762_);
        v_toMul_763_ = leanh::lean_ctor_get(v_inst_757_, 1);
        v_k_764_ = leanh::lean_ctor_get(v_p_759_, 0);
        leanh::lean_inc(v_k_764_);
        v_v_765_ = leanh::lean_ctor_get(v_p_759_, 1);
        leanh::lean_inc(v_v_765_);
        v_p_766_ = leanh::lean_ctor_get(v_p_759_, 2);
        leanh::lean_inc_ref(v_p_766_);
        leanh::lean_dec_ref_known(v_p_759_, 3);
        leanh::lean_inc_ref_n(v_inst_757_, 2);
        v___x_767_ = l_Lean_Grind_CommRing_denoteSInt___redArg(v_inst_757_, v_k_764_);
        leanh::lean_dec(v_k_764_);
        v___x_768_ = l_Lean_Grind_CommRing_Mon_denote___redArg(v_inst_757_, v_ctx_758_, v_v_765_);
        leanh::lean_inc(v_toMul_763_);
        v___x_769_ = leanh::lean_apply_2(v_toMul_763_, v___x_767_, v___x_768_);
        v___x_770_ = l_Lean_Grind_CommRing_Poly_denoteS___redArg(v_inst_757_, v_ctx_758_, v_p_766_);
        v___x_771_ = leanh::lean_apply_2(v_toAdd_762_, v___x_769_, v___x_770_);
        return v___x_771_;
    }
}
pub unsafe fn l_Lean_Grind_CommRing_Poly_denoteS___redArg___boxed(
    mut v_inst_772_: *mut leanh::LeanObject,
    mut v_ctx_773_: *mut leanh::LeanObject,
    mut v_p_774_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_775_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_775_ = l_Lean_Grind_CommRing_Poly_denoteS___redArg(v_inst_772_, v_ctx_773_, v_p_774_);
    leanh::lean_dec_ref(v_ctx_773_);
    return v_res_775_;
}
pub unsafe fn l_Lean_Grind_CommRing_Poly_denoteS(
    mut v_00_u03b1_776_: *mut leanh::LeanObject,
    mut v_inst_777_: *mut leanh::LeanObject,
    mut v_ctx_778_: *mut leanh::LeanObject,
    mut v_p_779_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_780_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_780_ = l_Lean_Grind_CommRing_Poly_denoteS___redArg(v_inst_777_, v_ctx_778_, v_p_779_);
    return v___x_780_;
}
pub unsafe fn l_Lean_Grind_CommRing_Poly_denoteS___boxed(
    mut v_00_u03b1_781_: *mut leanh::LeanObject,
    mut v_inst_782_: *mut leanh::LeanObject,
    mut v_ctx_783_: *mut leanh::LeanObject,
    mut v_p_784_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_785_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_785_ =
        l_Lean_Grind_CommRing_Poly_denoteS(v_00_u03b1_781_, v_inst_782_, v_ctx_783_, v_p_784_);
    leanh::lean_dec_ref(v_ctx_783_);
    return v_res_785_;
}
pub unsafe fn l___private_Init_Grind_Ring_CommSemiringAdapter_0__Lean_Grind_CommRing_Poly_denoteS_match__1_splitter___redArg(
    mut v_p_786_: *mut leanh::LeanObject,
    mut v_h__1_787_: *mut leanh::LeanObject,
    mut v_h__2_788_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_p_786_) == 0 {
        let mut v_k_789_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_790_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__2_788_);
        v_k_789_ = leanh::lean_ctor_get(v_p_786_, 0);
        leanh::lean_inc(v_k_789_);
        leanh::lean_dec_ref_known(v_p_786_, 1);
        v___x_790_ = leanh::lean_apply_1(v_h__1_787_, v_k_789_);
        return v___x_790_;
    } else {
        let mut v_k_791_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_v_792_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_p_793_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_794_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__1_787_);
        v_k_791_ = leanh::lean_ctor_get(v_p_786_, 0);
        leanh::lean_inc(v_k_791_);
        v_v_792_ = leanh::lean_ctor_get(v_p_786_, 1);
        leanh::lean_inc(v_v_792_);
        v_p_793_ = leanh::lean_ctor_get(v_p_786_, 2);
        leanh::lean_inc_ref(v_p_793_);
        leanh::lean_dec_ref_known(v_p_786_, 3);
        v___x_794_ = leanh::lean_apply_3(v_h__2_788_, v_k_791_, v_v_792_, v_p_793_);
        return v___x_794_;
    }
}
pub unsafe fn l___private_Init_Grind_Ring_CommSemiringAdapter_0__Lean_Grind_CommRing_Poly_denoteS_match__1_splitter(
    mut v_motive_795_: *mut leanh::LeanObject,
    mut v_p_796_: *mut leanh::LeanObject,
    mut v_h__1_797_: *mut leanh::LeanObject,
    mut v_h__2_798_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_p_796_) == 0 {
        let mut v_k_799_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_800_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__2_798_);
        v_k_799_ = leanh::lean_ctor_get(v_p_796_, 0);
        leanh::lean_inc(v_k_799_);
        leanh::lean_dec_ref_known(v_p_796_, 1);
        v___x_800_ = leanh::lean_apply_1(v_h__1_797_, v_k_799_);
        return v___x_800_;
    } else {
        let mut v_k_801_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_v_802_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_p_803_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_804_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__1_797_);
        v_k_801_ = leanh::lean_ctor_get(v_p_796_, 0);
        leanh::lean_inc(v_k_801_);
        v_v_802_ = leanh::lean_ctor_get(v_p_796_, 1);
        leanh::lean_inc(v_v_802_);
        v_p_803_ = leanh::lean_ctor_get(v_p_796_, 2);
        leanh::lean_inc_ref(v_p_803_);
        leanh::lean_dec_ref_known(v_p_796_, 3);
        v___x_804_ = leanh::lean_apply_3(v_h__2_798_, v_k_801_, v_v_802_, v_p_803_);
        return v___x_804_;
    }
}
pub unsafe fn l___private_Init_Grind_Ring_CommSemiringAdapter_0__Lean_Grind_CommRing_Expr_toPolyS_match__4_splitter___redArg(
    mut v_x_805_: *mut leanh::LeanObject,
    mut v_h__1_806_: *mut leanh::LeanObject,
    mut v_h__2_807_: *mut leanh::LeanObject,
    mut v_h__3_808_: *mut leanh::LeanObject,
    mut v_h__4_809_: *mut leanh::LeanObject,
    mut v_h__5_810_: *mut leanh::LeanObject,
    mut v_h__6_811_: *mut leanh::LeanObject,
    mut v_h__7_812_: *mut leanh::LeanObject,
    mut v_h__8_813_: *mut leanh::LeanObject,
    mut v_h__9_814_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    match leanh::lean_obj_tag(v_x_805_) {
        0 => {
            let mut v_k_815_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_816_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__9_814_);
            leanh::lean_dec(v_h__8_813_);
            leanh::lean_dec(v_h__7_812_);
            leanh::lean_dec(v_h__6_811_);
            leanh::lean_dec(v_h__5_810_);
            leanh::lean_dec(v_h__4_809_);
            leanh::lean_dec(v_h__3_808_);
            leanh::lean_dec(v_h__2_807_);
            v_k_815_ = leanh::lean_ctor_get(v_x_805_, 0);
            leanh::lean_inc(v_k_815_);
            leanh::lean_dec_ref_known(v_x_805_, 1);
            v___x_816_ = leanh::lean_apply_1(v_h__1_806_, v_k_815_);
            return v___x_816_;
        }
        1 => {
            let mut v_k_817_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_818_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__9_814_);
            leanh::lean_dec(v_h__8_813_);
            leanh::lean_dec(v_h__7_812_);
            leanh::lean_dec(v_h__5_810_);
            leanh::lean_dec(v_h__4_809_);
            leanh::lean_dec(v_h__3_808_);
            leanh::lean_dec(v_h__2_807_);
            leanh::lean_dec(v_h__1_806_);
            v_k_817_ = leanh::lean_ctor_get(v_x_805_, 0);
            leanh::lean_inc(v_k_817_);
            leanh::lean_dec_ref_known(v_x_805_, 1);
            v___x_818_ = leanh::lean_apply_1(v_h__6_811_, v_k_817_);
            return v___x_818_;
        }
        2 => {
            let mut v_k_819_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_820_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__8_813_);
            leanh::lean_dec(v_h__7_812_);
            leanh::lean_dec(v_h__6_811_);
            leanh::lean_dec(v_h__5_810_);
            leanh::lean_dec(v_h__4_809_);
            leanh::lean_dec(v_h__3_808_);
            leanh::lean_dec(v_h__2_807_);
            leanh::lean_dec(v_h__1_806_);
            v_k_819_ = leanh::lean_ctor_get(v_x_805_, 0);
            leanh::lean_inc(v_k_819_);
            leanh::lean_dec_ref_known(v_x_805_, 1);
            v___x_820_ = leanh::lean_apply_1(v_h__9_814_, v_k_819_);
            return v___x_820_;
        }
        3 => {
            let mut v_i_821_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_822_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__9_814_);
            leanh::lean_dec(v_h__8_813_);
            leanh::lean_dec(v_h__7_812_);
            leanh::lean_dec(v_h__6_811_);
            leanh::lean_dec(v_h__5_810_);
            leanh::lean_dec(v_h__4_809_);
            leanh::lean_dec(v_h__3_808_);
            leanh::lean_dec(v_h__1_806_);
            v_i_821_ = leanh::lean_ctor_get(v_x_805_, 0);
            leanh::lean_inc(v_i_821_);
            leanh::lean_dec_ref_known(v_x_805_, 1);
            v___x_822_ = leanh::lean_apply_1(v_h__2_807_, v_i_821_);
            return v___x_822_;
        }
        4 => {
            let mut v_a_823_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_824_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__9_814_);
            leanh::lean_dec(v_h__7_812_);
            leanh::lean_dec(v_h__6_811_);
            leanh::lean_dec(v_h__5_810_);
            leanh::lean_dec(v_h__4_809_);
            leanh::lean_dec(v_h__3_808_);
            leanh::lean_dec(v_h__2_807_);
            leanh::lean_dec(v_h__1_806_);
            v_a_823_ = leanh::lean_ctor_get(v_x_805_, 0);
            leanh::lean_inc_ref(v_a_823_);
            leanh::lean_dec_ref_known(v_x_805_, 1);
            v___x_824_ = leanh::lean_apply_1(v_h__8_813_, v_a_823_);
            return v___x_824_;
        }
        5 => {
            let mut v_a_825_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_b_826_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_827_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__9_814_);
            leanh::lean_dec(v_h__8_813_);
            leanh::lean_dec(v_h__7_812_);
            leanh::lean_dec(v_h__6_811_);
            leanh::lean_dec(v_h__5_810_);
            leanh::lean_dec(v_h__4_809_);
            leanh::lean_dec(v_h__2_807_);
            leanh::lean_dec(v_h__1_806_);
            v_a_825_ = leanh::lean_ctor_get(v_x_805_, 0);
            leanh::lean_inc_ref(v_a_825_);
            v_b_826_ = leanh::lean_ctor_get(v_x_805_, 1);
            leanh::lean_inc_ref(v_b_826_);
            leanh::lean_dec_ref_known(v_x_805_, 2);
            v___x_827_ = leanh::lean_apply_2(v_h__3_808_, v_a_825_, v_b_826_);
            return v___x_827_;
        }
        6 => {
            let mut v_a_828_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_b_829_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_830_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__9_814_);
            leanh::lean_dec(v_h__8_813_);
            leanh::lean_dec(v_h__6_811_);
            leanh::lean_dec(v_h__5_810_);
            leanh::lean_dec(v_h__4_809_);
            leanh::lean_dec(v_h__3_808_);
            leanh::lean_dec(v_h__2_807_);
            leanh::lean_dec(v_h__1_806_);
            v_a_828_ = leanh::lean_ctor_get(v_x_805_, 0);
            leanh::lean_inc_ref(v_a_828_);
            v_b_829_ = leanh::lean_ctor_get(v_x_805_, 1);
            leanh::lean_inc_ref(v_b_829_);
            leanh::lean_dec_ref_known(v_x_805_, 2);
            v___x_830_ = leanh::lean_apply_2(v_h__7_812_, v_a_828_, v_b_829_);
            return v___x_830_;
        }
        7 => {
            let mut v_a_831_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_b_832_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_833_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__9_814_);
            leanh::lean_dec(v_h__8_813_);
            leanh::lean_dec(v_h__7_812_);
            leanh::lean_dec(v_h__6_811_);
            leanh::lean_dec(v_h__5_810_);
            leanh::lean_dec(v_h__3_808_);
            leanh::lean_dec(v_h__2_807_);
            leanh::lean_dec(v_h__1_806_);
            v_a_831_ = leanh::lean_ctor_get(v_x_805_, 0);
            leanh::lean_inc_ref(v_a_831_);
            v_b_832_ = leanh::lean_ctor_get(v_x_805_, 1);
            leanh::lean_inc_ref(v_b_832_);
            leanh::lean_dec_ref_known(v_x_805_, 2);
            v___x_833_ = leanh::lean_apply_2(v_h__4_809_, v_a_831_, v_b_832_);
            return v___x_833_;
        }
        _ => {
            let mut v_a_834_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_k_835_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_836_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__9_814_);
            leanh::lean_dec(v_h__8_813_);
            leanh::lean_dec(v_h__7_812_);
            leanh::lean_dec(v_h__6_811_);
            leanh::lean_dec(v_h__4_809_);
            leanh::lean_dec(v_h__3_808_);
            leanh::lean_dec(v_h__2_807_);
            leanh::lean_dec(v_h__1_806_);
            v_a_834_ = leanh::lean_ctor_get(v_x_805_, 0);
            leanh::lean_inc_ref(v_a_834_);
            v_k_835_ = leanh::lean_ctor_get(v_x_805_, 1);
            leanh::lean_inc(v_k_835_);
            leanh::lean_dec_ref_known(v_x_805_, 2);
            v___x_836_ = leanh::lean_apply_2(v_h__5_810_, v_a_834_, v_k_835_);
            return v___x_836_;
        }
    }
}
pub unsafe fn l___private_Init_Grind_Ring_CommSemiringAdapter_0__Lean_Grind_CommRing_Expr_toPolyS_match__4_splitter(
    mut v_motive_837_: *mut leanh::LeanObject,
    mut v_x_838_: *mut leanh::LeanObject,
    mut v_h__1_839_: *mut leanh::LeanObject,
    mut v_h__2_840_: *mut leanh::LeanObject,
    mut v_h__3_841_: *mut leanh::LeanObject,
    mut v_h__4_842_: *mut leanh::LeanObject,
    mut v_h__5_843_: *mut leanh::LeanObject,
    mut v_h__6_844_: *mut leanh::LeanObject,
    mut v_h__7_845_: *mut leanh::LeanObject,
    mut v_h__8_846_: *mut leanh::LeanObject,
    mut v_h__9_847_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    match leanh::lean_obj_tag(v_x_838_) {
        0 => {
            let mut v_k_848_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_849_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__9_847_);
            leanh::lean_dec(v_h__8_846_);
            leanh::lean_dec(v_h__7_845_);
            leanh::lean_dec(v_h__6_844_);
            leanh::lean_dec(v_h__5_843_);
            leanh::lean_dec(v_h__4_842_);
            leanh::lean_dec(v_h__3_841_);
            leanh::lean_dec(v_h__2_840_);
            v_k_848_ = leanh::lean_ctor_get(v_x_838_, 0);
            leanh::lean_inc(v_k_848_);
            leanh::lean_dec_ref_known(v_x_838_, 1);
            v___x_849_ = leanh::lean_apply_1(v_h__1_839_, v_k_848_);
            return v___x_849_;
        }
        1 => {
            let mut v_k_850_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_851_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__9_847_);
            leanh::lean_dec(v_h__8_846_);
            leanh::lean_dec(v_h__7_845_);
            leanh::lean_dec(v_h__5_843_);
            leanh::lean_dec(v_h__4_842_);
            leanh::lean_dec(v_h__3_841_);
            leanh::lean_dec(v_h__2_840_);
            leanh::lean_dec(v_h__1_839_);
            v_k_850_ = leanh::lean_ctor_get(v_x_838_, 0);
            leanh::lean_inc(v_k_850_);
            leanh::lean_dec_ref_known(v_x_838_, 1);
            v___x_851_ = leanh::lean_apply_1(v_h__6_844_, v_k_850_);
            return v___x_851_;
        }
        2 => {
            let mut v_k_852_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_853_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__8_846_);
            leanh::lean_dec(v_h__7_845_);
            leanh::lean_dec(v_h__6_844_);
            leanh::lean_dec(v_h__5_843_);
            leanh::lean_dec(v_h__4_842_);
            leanh::lean_dec(v_h__3_841_);
            leanh::lean_dec(v_h__2_840_);
            leanh::lean_dec(v_h__1_839_);
            v_k_852_ = leanh::lean_ctor_get(v_x_838_, 0);
            leanh::lean_inc(v_k_852_);
            leanh::lean_dec_ref_known(v_x_838_, 1);
            v___x_853_ = leanh::lean_apply_1(v_h__9_847_, v_k_852_);
            return v___x_853_;
        }
        3 => {
            let mut v_i_854_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_855_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__9_847_);
            leanh::lean_dec(v_h__8_846_);
            leanh::lean_dec(v_h__7_845_);
            leanh::lean_dec(v_h__6_844_);
            leanh::lean_dec(v_h__5_843_);
            leanh::lean_dec(v_h__4_842_);
            leanh::lean_dec(v_h__3_841_);
            leanh::lean_dec(v_h__1_839_);
            v_i_854_ = leanh::lean_ctor_get(v_x_838_, 0);
            leanh::lean_inc(v_i_854_);
            leanh::lean_dec_ref_known(v_x_838_, 1);
            v___x_855_ = leanh::lean_apply_1(v_h__2_840_, v_i_854_);
            return v___x_855_;
        }
        4 => {
            let mut v_a_856_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_857_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__9_847_);
            leanh::lean_dec(v_h__7_845_);
            leanh::lean_dec(v_h__6_844_);
            leanh::lean_dec(v_h__5_843_);
            leanh::lean_dec(v_h__4_842_);
            leanh::lean_dec(v_h__3_841_);
            leanh::lean_dec(v_h__2_840_);
            leanh::lean_dec(v_h__1_839_);
            v_a_856_ = leanh::lean_ctor_get(v_x_838_, 0);
            leanh::lean_inc_ref(v_a_856_);
            leanh::lean_dec_ref_known(v_x_838_, 1);
            v___x_857_ = leanh::lean_apply_1(v_h__8_846_, v_a_856_);
            return v___x_857_;
        }
        5 => {
            let mut v_a_858_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_b_859_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_860_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__9_847_);
            leanh::lean_dec(v_h__8_846_);
            leanh::lean_dec(v_h__7_845_);
            leanh::lean_dec(v_h__6_844_);
            leanh::lean_dec(v_h__5_843_);
            leanh::lean_dec(v_h__4_842_);
            leanh::lean_dec(v_h__2_840_);
            leanh::lean_dec(v_h__1_839_);
            v_a_858_ = leanh::lean_ctor_get(v_x_838_, 0);
            leanh::lean_inc_ref(v_a_858_);
            v_b_859_ = leanh::lean_ctor_get(v_x_838_, 1);
            leanh::lean_inc_ref(v_b_859_);
            leanh::lean_dec_ref_known(v_x_838_, 2);
            v___x_860_ = leanh::lean_apply_2(v_h__3_841_, v_a_858_, v_b_859_);
            return v___x_860_;
        }
        6 => {
            let mut v_a_861_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_b_862_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_863_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__9_847_);
            leanh::lean_dec(v_h__8_846_);
            leanh::lean_dec(v_h__6_844_);
            leanh::lean_dec(v_h__5_843_);
            leanh::lean_dec(v_h__4_842_);
            leanh::lean_dec(v_h__3_841_);
            leanh::lean_dec(v_h__2_840_);
            leanh::lean_dec(v_h__1_839_);
            v_a_861_ = leanh::lean_ctor_get(v_x_838_, 0);
            leanh::lean_inc_ref(v_a_861_);
            v_b_862_ = leanh::lean_ctor_get(v_x_838_, 1);
            leanh::lean_inc_ref(v_b_862_);
            leanh::lean_dec_ref_known(v_x_838_, 2);
            v___x_863_ = leanh::lean_apply_2(v_h__7_845_, v_a_861_, v_b_862_);
            return v___x_863_;
        }
        7 => {
            let mut v_a_864_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_b_865_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_866_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__9_847_);
            leanh::lean_dec(v_h__8_846_);
            leanh::lean_dec(v_h__7_845_);
            leanh::lean_dec(v_h__6_844_);
            leanh::lean_dec(v_h__5_843_);
            leanh::lean_dec(v_h__3_841_);
            leanh::lean_dec(v_h__2_840_);
            leanh::lean_dec(v_h__1_839_);
            v_a_864_ = leanh::lean_ctor_get(v_x_838_, 0);
            leanh::lean_inc_ref(v_a_864_);
            v_b_865_ = leanh::lean_ctor_get(v_x_838_, 1);
            leanh::lean_inc_ref(v_b_865_);
            leanh::lean_dec_ref_known(v_x_838_, 2);
            v___x_866_ = leanh::lean_apply_2(v_h__4_842_, v_a_864_, v_b_865_);
            return v___x_866_;
        }
        _ => {
            let mut v_a_867_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_k_868_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_869_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__9_847_);
            leanh::lean_dec(v_h__8_846_);
            leanh::lean_dec(v_h__7_845_);
            leanh::lean_dec(v_h__6_844_);
            leanh::lean_dec(v_h__4_842_);
            leanh::lean_dec(v_h__3_841_);
            leanh::lean_dec(v_h__2_840_);
            leanh::lean_dec(v_h__1_839_);
            v_a_867_ = leanh::lean_ctor_get(v_x_838_, 0);
            leanh::lean_inc_ref(v_a_867_);
            v_k_868_ = leanh::lean_ctor_get(v_x_838_, 1);
            leanh::lean_inc(v_k_868_);
            leanh::lean_dec_ref_known(v_x_838_, 2);
            v___x_869_ = leanh::lean_apply_2(v_h__5_843_, v_a_867_, v_k_868_);
            return v___x_869_;
        }
    }
}
pub unsafe fn l___private_Init_Grind_Ring_CommSemiringAdapter_0__Lean_Grind_CommRing_Expr_toPolyS_match__1_splitter___redArg(
    mut v_a_870_: *mut leanh::LeanObject,
    mut v_h__1_871_: *mut leanh::LeanObject,
    mut v_h__2_872_: *mut leanh::LeanObject,
    mut v_h__3_873_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    match leanh::lean_obj_tag(v_a_870_) {
        0 => {
            let mut v_k_874_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_875_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__3_873_);
            leanh::lean_dec(v_h__2_872_);
            v_k_874_ = leanh::lean_ctor_get(v_a_870_, 0);
            leanh::lean_inc(v_k_874_);
            leanh::lean_dec_ref_known(v_a_870_, 1);
            v___x_875_ = leanh::lean_apply_1(v_h__1_871_, v_k_874_);
            return v___x_875_;
        }
        3 => {
            let mut v_i_876_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_877_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__3_873_);
            leanh::lean_dec(v_h__1_871_);
            v_i_876_ = leanh::lean_ctor_get(v_a_870_, 0);
            leanh::lean_inc(v_i_876_);
            leanh::lean_dec_ref_known(v_a_870_, 1);
            v___x_877_ = leanh::lean_apply_1(v_h__2_872_, v_i_876_);
            return v___x_877_;
        }
        _ => {
            let mut v___x_878_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__2_872_);
            leanh::lean_dec(v_h__1_871_);
            v___x_878_ = leanh::lean_apply_3(
                v_h__3_873_,
                v_a_870_,
                leanh::lean_box(0),
                leanh::lean_box(0),
            );
            return v___x_878_;
        }
    }
}
pub unsafe fn l___private_Init_Grind_Ring_CommSemiringAdapter_0__Lean_Grind_CommRing_Expr_toPolyS_match__1_splitter(
    mut v_motive_879_: *mut leanh::LeanObject,
    mut v_a_880_: *mut leanh::LeanObject,
    mut v_h__1_881_: *mut leanh::LeanObject,
    mut v_h__2_882_: *mut leanh::LeanObject,
    mut v_h__3_883_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    match leanh::lean_obj_tag(v_a_880_) {
        0 => {
            let mut v_k_884_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_885_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__3_883_);
            leanh::lean_dec(v_h__2_882_);
            v_k_884_ = leanh::lean_ctor_get(v_a_880_, 0);
            leanh::lean_inc(v_k_884_);
            leanh::lean_dec_ref_known(v_a_880_, 1);
            v___x_885_ = leanh::lean_apply_1(v_h__1_881_, v_k_884_);
            return v___x_885_;
        }
        3 => {
            let mut v_i_886_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_887_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__3_883_);
            leanh::lean_dec(v_h__1_881_);
            v_i_886_ = leanh::lean_ctor_get(v_a_880_, 0);
            leanh::lean_inc(v_i_886_);
            leanh::lean_dec_ref_known(v_a_880_, 1);
            v___x_887_ = leanh::lean_apply_1(v_h__2_882_, v_i_886_);
            return v___x_887_;
        }
        _ => {
            let mut v___x_888_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__2_882_);
            leanh::lean_dec(v_h__1_881_);
            v___x_888_ = leanh::lean_apply_3(
                v_h__3_883_,
                v_a_880_,
                leanh::lean_box(0),
                leanh::lean_box(0),
            );
            return v___x_888_;
        }
    }
}
pub unsafe fn l_Lean_Grind_CommRing_eq__normS__cert(
    mut v_lhs_889_: *mut leanh::LeanObject,
    mut v_rhs_890_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_891_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_892_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_893_: u8 = 0;
    v___x_891_ = l_Lean_Grind_CommRing_Expr_toPolyS(v_lhs_889_);
    v___x_892_ = l_Lean_Grind_CommRing_Expr_toPolyS(v_rhs_890_);
    v___x_893_ = l_Lean_Grind_CommRing_instBEqPoly_beq(v___x_891_, v___x_892_);
    leanh::lean_dec_ref(v___x_892_);
    leanh::lean_dec_ref(v___x_891_);
    return v___x_893_;
}
pub unsafe fn l_Lean_Grind_CommRing_eq__normS__cert___boxed(
    mut v_lhs_894_: *mut leanh::LeanObject,
    mut v_rhs_895_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_896_: u8 = 0;
    let mut v_r_897_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_896_ = l_Lean_Grind_CommRing_eq__normS__cert(v_lhs_894_, v_rhs_895_);
    v_r_897_ = leanh::lean_box((v_res_896_) as usize);
    return v_r_897_;
}
pub unsafe fn l_Lean_Grind_CommRing_eq__normS__nc__cert(
    mut v_lhs_898_: *mut leanh::LeanObject,
    mut v_rhs_899_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_900_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_901_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_902_: u8 = 0;
    v___x_900_ = l_Lean_Grind_CommRing_Expr_toPolyS__nc(v_lhs_898_);
    v___x_901_ = l_Lean_Grind_CommRing_Expr_toPolyS__nc(v_rhs_899_);
    v___x_902_ = l_Lean_Grind_CommRing_instBEqPoly_beq(v___x_900_, v___x_901_);
    leanh::lean_dec_ref(v___x_901_);
    leanh::lean_dec_ref(v___x_900_);
    return v___x_902_;
}
pub unsafe fn l_Lean_Grind_CommRing_eq__normS__nc__cert___boxed(
    mut v_lhs_903_: *mut leanh::LeanObject,
    mut v_rhs_904_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_905_: u8 = 0;
    let mut v_r_906_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_905_ = l_Lean_Grind_CommRing_eq__normS__nc__cert(v_lhs_903_, v_rhs_904_);
    v_r_906_ = leanh::lean_box((v_res_905_) as usize);
    return v_r_906_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Init_Grind_Ring_CommSemiringAdapter(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Init_Grind_Ring_Envelope(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Grind_Ring_CommSolver(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Int_LemmasAux(builtin);
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
pub unsafe fn meta_initialize_Init_Grind_Ring_CommSemiringAdapter(
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
pub unsafe fn initialize_Init_Grind_Ring_CommSemiringAdapter(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Init_Grind_Ring_Envelope(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_Grind_Ring_CommSolver(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Int_LemmasAux(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_Omega(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Grind_Ring_CommSemiringAdapter(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = meta_initialize_Init_Grind_Ring_CommSemiringAdapter(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return initialize_Init_Grind_Ring_CommSemiringAdapter(builtin);
}