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
static mut l_Lean_Grind_CommRing_Expr_toPolyS___closed__0_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Grind_CommRing_Expr_toPolyS___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Grind_CommRing_Expr_toPolyS___closed__1_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Grind_CommRing_Expr_toPolyS___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub unsafe fn l_Lean_Grind_CommRing_Expr_denoteS___redArg(
    mut v_inst_454_: *mut crate::leanh::LeanObject,
    mut v_ctx_455_: *mut crate::leanh::LeanObject,
    mut v_x_456_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    match crate::leanh::lean_obj_tag(v_x_456_) {
        0 => {
            let mut v_ofNat_457_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_k_458_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_459_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_460_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v_ofNat_457_ = crate::leanh::lean_ctor_get(v_inst_454_, 3);
            crate::leanh::lean_inc(v_ofNat_457_);
            crate::leanh::lean_dec_ref(v_inst_454_);
            v_k_458_ = crate::leanh::lean_ctor_get(v_x_456_, 0);
            crate::leanh::lean_inc(v_k_458_);
            crate::leanh::lean_dec_ref_known(v_x_456_, 1);
            v___x_459_ = lean_nat_abs(v_k_458_);
            crate::leanh::lean_dec(v_k_458_);
            v___x_460_ = crate::leanh::lean_apply_1(v_ofNat_457_, v___x_459_);
            return v___x_460_;
        }
        1 => {
            let mut v_ofNat_461_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_k_462_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_463_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v_ofNat_461_ = crate::leanh::lean_ctor_get(v_inst_454_, 3);
            crate::leanh::lean_inc(v_ofNat_461_);
            crate::leanh::lean_dec_ref(v_inst_454_);
            v_k_462_ = crate::leanh::lean_ctor_get(v_x_456_, 0);
            crate::leanh::lean_inc(v_k_462_);
            crate::leanh::lean_dec_ref_known(v_x_456_, 1);
            v___x_463_ = crate::leanh::lean_apply_1(v_ofNat_461_, v_k_462_);
            return v___x_463_;
        }
        3 => {
            let mut v_i_464_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_465_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec_ref(v_inst_454_);
            v_i_464_ = crate::leanh::lean_ctor_get(v_x_456_, 0);
            crate::leanh::lean_inc(v_i_464_);
            crate::leanh::lean_dec_ref_known(v_x_456_, 1);
            v___x_465_ = l_Lean_RArray_getImpl___redArg(v_ctx_455_, v_i_464_);
            crate::leanh::lean_dec(v_i_464_);
            return v___x_465_;
        }
        5 => {
            let mut v_toAdd_466_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_a_467_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_b_468_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_469_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_470_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_471_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v_toAdd_466_ = crate::leanh::lean_ctor_get(v_inst_454_, 0);
            crate::leanh::lean_inc(v_toAdd_466_);
            v_a_467_ = crate::leanh::lean_ctor_get(v_x_456_, 0);
            crate::leanh::lean_inc_ref(v_a_467_);
            v_b_468_ = crate::leanh::lean_ctor_get(v_x_456_, 1);
            crate::leanh::lean_inc_ref(v_b_468_);
            crate::leanh::lean_dec_ref_known(v_x_456_, 2);
            crate::leanh::lean_inc_ref(v_inst_454_);
            v___x_469_ =
                l_Lean_Grind_CommRing_Expr_denoteS___redArg(v_inst_454_, v_ctx_455_, v_a_467_);
            v___x_470_ =
                l_Lean_Grind_CommRing_Expr_denoteS___redArg(v_inst_454_, v_ctx_455_, v_b_468_);
            v___x_471_ = crate::leanh::lean_apply_2(v_toAdd_466_, v___x_469_, v___x_470_);
            return v___x_471_;
        }
        7 => {
            let mut v_toMul_472_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_a_473_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_b_474_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_475_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_476_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_477_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v_toMul_472_ = crate::leanh::lean_ctor_get(v_inst_454_, 1);
            crate::leanh::lean_inc(v_toMul_472_);
            v_a_473_ = crate::leanh::lean_ctor_get(v_x_456_, 0);
            crate::leanh::lean_inc_ref(v_a_473_);
            v_b_474_ = crate::leanh::lean_ctor_get(v_x_456_, 1);
            crate::leanh::lean_inc_ref(v_b_474_);
            crate::leanh::lean_dec_ref_known(v_x_456_, 2);
            crate::leanh::lean_inc_ref(v_inst_454_);
            v___x_475_ =
                l_Lean_Grind_CommRing_Expr_denoteS___redArg(v_inst_454_, v_ctx_455_, v_a_473_);
            v___x_476_ =
                l_Lean_Grind_CommRing_Expr_denoteS___redArg(v_inst_454_, v_ctx_455_, v_b_474_);
            v___x_477_ = crate::leanh::lean_apply_2(v_toMul_472_, v___x_475_, v___x_476_);
            return v___x_477_;
        }
        8 => {
            let mut v_npow_478_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_a_479_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_k_480_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_481_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_482_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v_npow_478_ = crate::leanh::lean_ctor_get(v_inst_454_, 5);
            crate::leanh::lean_inc(v_npow_478_);
            v_a_479_ = crate::leanh::lean_ctor_get(v_x_456_, 0);
            crate::leanh::lean_inc_ref(v_a_479_);
            v_k_480_ = crate::leanh::lean_ctor_get(v_x_456_, 1);
            crate::leanh::lean_inc(v_k_480_);
            crate::leanh::lean_dec_ref_known(v_x_456_, 2);
            v___x_481_ =
                l_Lean_Grind_CommRing_Expr_denoteS___redArg(v_inst_454_, v_ctx_455_, v_a_479_);
            v___x_482_ = crate::leanh::lean_apply_2(v_npow_478_, v___x_481_, v_k_480_);
            return v___x_482_;
        }
        _ => {
            let mut v_ofNat_483_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_484_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_485_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec_ref(v_x_456_);
            v_ofNat_483_ = crate::leanh::lean_ctor_get(v_inst_454_, 3);
            crate::leanh::lean_inc(v_ofNat_483_);
            crate::leanh::lean_dec_ref(v_inst_454_);
            v___x_484_ = crate::leanh::lean_unsigned_to_nat(0);
            v___x_485_ = crate::leanh::lean_apply_1(v_ofNat_483_, v___x_484_);
            return v___x_485_;
        }
    }
}
pub unsafe fn l_Lean_Grind_CommRing_Expr_denoteS___redArg___boxed(
    mut v_inst_486_: *mut crate::leanh::LeanObject,
    mut v_ctx_487_: *mut crate::leanh::LeanObject,
    mut v_x_488_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_489_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_489_ = l_Lean_Grind_CommRing_Expr_denoteS___redArg(v_inst_486_, v_ctx_487_, v_x_488_);
    crate::leanh::lean_dec_ref(v_ctx_487_);
    return v_res_489_;
}
pub unsafe fn l_Lean_Grind_CommRing_Expr_denoteS(
    mut v_00_u03b1_490_: *mut crate::leanh::LeanObject,
    mut v_inst_491_: *mut crate::leanh::LeanObject,
    mut v_ctx_492_: *mut crate::leanh::LeanObject,
    mut v_x_493_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_494_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_494_ = l_Lean_Grind_CommRing_Expr_denoteS___redArg(v_inst_491_, v_ctx_492_, v_x_493_);
    return v___x_494_;
}
pub unsafe fn l_Lean_Grind_CommRing_Expr_denoteS___boxed(
    mut v_00_u03b1_495_: *mut crate::leanh::LeanObject,
    mut v_inst_496_: *mut crate::leanh::LeanObject,
    mut v_ctx_497_: *mut crate::leanh::LeanObject,
    mut v_x_498_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_499_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_499_ =
        l_Lean_Grind_CommRing_Expr_denoteS(v_00_u03b1_495_, v_inst_496_, v_ctx_497_, v_x_498_);
    crate::leanh::lean_dec_ref(v_ctx_497_);
    return v_res_499_;
}
pub unsafe fn l_Lean_Grind_CommRing_Expr_denoteSAsRing___redArg(
    mut v_inst_500_: *mut crate::leanh::LeanObject,
    mut v_ctx_501_: *mut crate::leanh::LeanObject,
    mut v_x_502_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    match crate::leanh::lean_obj_tag(v_x_502_) {
        0 => {
            let mut v_k_503_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_504_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_505_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v_k_503_ = crate::leanh::lean_ctor_get(v_x_502_, 0);
            crate::leanh::lean_inc(v_k_503_);
            crate::leanh::lean_dec_ref_known(v_x_502_, 1);
            v___x_504_ = lean_nat_abs(v_k_503_);
            crate::leanh::lean_dec(v_k_503_);
            v___x_505_ = l_Lean_Grind_Ring_OfSemiring_natCast___redArg(v_inst_500_, v___x_504_);
            return v___x_505_;
        }
        1 => {
            let mut v_k_506_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_507_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v_k_506_ = crate::leanh::lean_ctor_get(v_x_502_, 0);
            crate::leanh::lean_inc(v_k_506_);
            crate::leanh::lean_dec_ref_known(v_x_502_, 1);
            v___x_507_ = l_Lean_Grind_Ring_OfSemiring_natCast___redArg(v_inst_500_, v_k_506_);
            return v___x_507_;
        }
        3 => {
            let mut v_i_508_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_509_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_510_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v_i_508_ = crate::leanh::lean_ctor_get(v_x_502_, 0);
            crate::leanh::lean_inc(v_i_508_);
            crate::leanh::lean_dec_ref_known(v_x_502_, 1);
            v___x_509_ = l_Lean_RArray_getImpl___redArg(v_ctx_501_, v_i_508_);
            crate::leanh::lean_dec(v_i_508_);
            v___x_510_ = l_Lean_Grind_Ring_OfSemiring_toQ___redArg(v_inst_500_, v___x_509_);
            return v___x_510_;
        }
        5 => {
            let mut v_a_511_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_b_512_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_513_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_514_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_515_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v_a_511_ = crate::leanh::lean_ctor_get(v_x_502_, 0);
            crate::leanh::lean_inc_ref(v_a_511_);
            v_b_512_ = crate::leanh::lean_ctor_get(v_x_502_, 1);
            crate::leanh::lean_inc_ref(v_b_512_);
            crate::leanh::lean_dec_ref_known(v_x_502_, 2);
            crate::leanh::lean_inc_ref_n(v_inst_500_, 2);
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
            let mut v_a_516_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_b_517_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_518_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_519_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_520_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v_a_516_ = crate::leanh::lean_ctor_get(v_x_502_, 0);
            crate::leanh::lean_inc_ref(v_a_516_);
            v_b_517_ = crate::leanh::lean_ctor_get(v_x_502_, 1);
            crate::leanh::lean_inc_ref(v_b_517_);
            crate::leanh::lean_dec_ref_known(v_x_502_, 2);
            crate::leanh::lean_inc_ref_n(v_inst_500_, 2);
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
            let mut v_a_521_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_k_522_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_523_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_524_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v_a_521_ = crate::leanh::lean_ctor_get(v_x_502_, 0);
            crate::leanh::lean_inc_ref(v_a_521_);
            v_k_522_ = crate::leanh::lean_ctor_get(v_x_502_, 1);
            crate::leanh::lean_inc(v_k_522_);
            crate::leanh::lean_dec_ref_known(v_x_502_, 2);
            crate::leanh::lean_inc_ref(v_inst_500_);
            v___x_523_ = l_Lean_Grind_CommRing_Expr_denoteSAsRing___redArg(
                v_inst_500_,
                v_ctx_501_,
                v_a_521_,
            );
            v___x_524_ =
                l_Lean_Grind_Ring_OfSemiring_npow___redArg(v_inst_500_, v___x_523_, v_k_522_);
            crate::leanh::lean_dec(v_k_522_);
            return v___x_524_;
        }
        _ => {
            let mut v___x_525_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_526_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec_ref(v_x_502_);
            v___x_525_ = crate::leanh::lean_unsigned_to_nat(0);
            v___x_526_ = l_Lean_Grind_Ring_OfSemiring_natCast___redArg(v_inst_500_, v___x_525_);
            return v___x_526_;
        }
    }
}
pub unsafe fn l_Lean_Grind_CommRing_Expr_denoteSAsRing___redArg___boxed(
    mut v_inst_527_: *mut crate::leanh::LeanObject,
    mut v_ctx_528_: *mut crate::leanh::LeanObject,
    mut v_x_529_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_530_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_530_ =
        l_Lean_Grind_CommRing_Expr_denoteSAsRing___redArg(v_inst_527_, v_ctx_528_, v_x_529_);
    crate::leanh::lean_dec_ref(v_ctx_528_);
    return v_res_530_;
}
pub unsafe fn l_Lean_Grind_CommRing_Expr_denoteSAsRing(
    mut v_00_u03b1_531_: *mut crate::leanh::LeanObject,
    mut v_inst_532_: *mut crate::leanh::LeanObject,
    mut v_ctx_533_: *mut crate::leanh::LeanObject,
    mut v_x_534_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_535_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_535_ =
        l_Lean_Grind_CommRing_Expr_denoteSAsRing___redArg(v_inst_532_, v_ctx_533_, v_x_534_);
    return v___x_535_;
}
pub unsafe fn l_Lean_Grind_CommRing_Expr_denoteSAsRing___boxed(
    mut v_00_u03b1_536_: *mut crate::leanh::LeanObject,
    mut v_inst_537_: *mut crate::leanh::LeanObject,
    mut v_ctx_538_: *mut crate::leanh::LeanObject,
    mut v_x_539_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_540_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_540_ = l_Lean_Grind_CommRing_Expr_denoteSAsRing(
        v_00_u03b1_536_,
        v_inst_537_,
        v_ctx_538_,
        v_x_539_,
    );
    crate::leanh::lean_dec_ref(v_ctx_538_);
    return v_res_540_;
}
pub unsafe fn l___private_Init_Grind_Ring_CommSemiringAdapter_0__Lean_Grind_CommRing_Expr_denoteS_match__1_splitter___redArg(
    mut v_x_541_: *mut crate::leanh::LeanObject,
    mut v_h__1_542_: *mut crate::leanh::LeanObject,
    mut v_h__2_543_: *mut crate::leanh::LeanObject,
    mut v_h__3_544_: *mut crate::leanh::LeanObject,
    mut v_h__4_545_: *mut crate::leanh::LeanObject,
    mut v_h__5_546_: *mut crate::leanh::LeanObject,
    mut v_h__6_547_: *mut crate::leanh::LeanObject,
    mut v_h__7_548_: *mut crate::leanh::LeanObject,
    mut v_h__8_549_: *mut crate::leanh::LeanObject,
    mut v_h__9_550_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    match crate::leanh::lean_obj_tag(v_x_541_) {
        0 => {
            let mut v_k_551_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_552_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__9_550_);
            crate::leanh::lean_dec(v_h__8_549_);
            crate::leanh::lean_dec(v_h__7_548_);
            crate::leanh::lean_dec(v_h__6_547_);
            crate::leanh::lean_dec(v_h__5_546_);
            crate::leanh::lean_dec(v_h__4_545_);
            crate::leanh::lean_dec(v_h__3_544_);
            crate::leanh::lean_dec(v_h__2_543_);
            v_k_551_ = crate::leanh::lean_ctor_get(v_x_541_, 0);
            crate::leanh::lean_inc(v_k_551_);
            crate::leanh::lean_dec_ref_known(v_x_541_, 1);
            v___x_552_ = crate::leanh::lean_apply_1(v_h__1_542_, v_k_551_);
            return v___x_552_;
        }
        1 => {
            let mut v_k_553_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_554_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__9_550_);
            crate::leanh::lean_dec(v_h__8_549_);
            crate::leanh::lean_dec(v_h__7_548_);
            crate::leanh::lean_dec(v_h__6_547_);
            crate::leanh::lean_dec(v_h__5_546_);
            crate::leanh::lean_dec(v_h__4_545_);
            crate::leanh::lean_dec(v_h__3_544_);
            crate::leanh::lean_dec(v_h__1_542_);
            v_k_553_ = crate::leanh::lean_ctor_get(v_x_541_, 0);
            crate::leanh::lean_inc(v_k_553_);
            crate::leanh::lean_dec_ref_known(v_x_541_, 1);
            v___x_554_ = crate::leanh::lean_apply_1(v_h__2_543_, v_k_553_);
            return v___x_554_;
        }
        2 => {
            let mut v_k_555_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_556_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__8_549_);
            crate::leanh::lean_dec(v_h__7_548_);
            crate::leanh::lean_dec(v_h__6_547_);
            crate::leanh::lean_dec(v_h__5_546_);
            crate::leanh::lean_dec(v_h__4_545_);
            crate::leanh::lean_dec(v_h__3_544_);
            crate::leanh::lean_dec(v_h__2_543_);
            crate::leanh::lean_dec(v_h__1_542_);
            v_k_555_ = crate::leanh::lean_ctor_get(v_x_541_, 0);
            crate::leanh::lean_inc(v_k_555_);
            crate::leanh::lean_dec_ref_known(v_x_541_, 1);
            v___x_556_ = crate::leanh::lean_apply_1(v_h__9_550_, v_k_555_);
            return v___x_556_;
        }
        3 => {
            let mut v_i_557_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_558_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__9_550_);
            crate::leanh::lean_dec(v_h__8_549_);
            crate::leanh::lean_dec(v_h__7_548_);
            crate::leanh::lean_dec(v_h__6_547_);
            crate::leanh::lean_dec(v_h__5_546_);
            crate::leanh::lean_dec(v_h__4_545_);
            crate::leanh::lean_dec(v_h__2_543_);
            crate::leanh::lean_dec(v_h__1_542_);
            v_i_557_ = crate::leanh::lean_ctor_get(v_x_541_, 0);
            crate::leanh::lean_inc(v_i_557_);
            crate::leanh::lean_dec_ref_known(v_x_541_, 1);
            v___x_558_ = crate::leanh::lean_apply_1(v_h__3_544_, v_i_557_);
            return v___x_558_;
        }
        4 => {
            let mut v_a_559_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_560_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__9_550_);
            crate::leanh::lean_dec(v_h__7_548_);
            crate::leanh::lean_dec(v_h__6_547_);
            crate::leanh::lean_dec(v_h__5_546_);
            crate::leanh::lean_dec(v_h__4_545_);
            crate::leanh::lean_dec(v_h__3_544_);
            crate::leanh::lean_dec(v_h__2_543_);
            crate::leanh::lean_dec(v_h__1_542_);
            v_a_559_ = crate::leanh::lean_ctor_get(v_x_541_, 0);
            crate::leanh::lean_inc_ref(v_a_559_);
            crate::leanh::lean_dec_ref_known(v_x_541_, 1);
            v___x_560_ = crate::leanh::lean_apply_1(v_h__8_549_, v_a_559_);
            return v___x_560_;
        }
        5 => {
            let mut v_a_561_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_b_562_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_563_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__9_550_);
            crate::leanh::lean_dec(v_h__8_549_);
            crate::leanh::lean_dec(v_h__7_548_);
            crate::leanh::lean_dec(v_h__6_547_);
            crate::leanh::lean_dec(v_h__5_546_);
            crate::leanh::lean_dec(v_h__3_544_);
            crate::leanh::lean_dec(v_h__2_543_);
            crate::leanh::lean_dec(v_h__1_542_);
            v_a_561_ = crate::leanh::lean_ctor_get(v_x_541_, 0);
            crate::leanh::lean_inc_ref(v_a_561_);
            v_b_562_ = crate::leanh::lean_ctor_get(v_x_541_, 1);
            crate::leanh::lean_inc_ref(v_b_562_);
            crate::leanh::lean_dec_ref_known(v_x_541_, 2);
            v___x_563_ = crate::leanh::lean_apply_2(v_h__4_545_, v_a_561_, v_b_562_);
            return v___x_563_;
        }
        6 => {
            let mut v_a_564_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_b_565_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_566_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__9_550_);
            crate::leanh::lean_dec(v_h__8_549_);
            crate::leanh::lean_dec(v_h__6_547_);
            crate::leanh::lean_dec(v_h__5_546_);
            crate::leanh::lean_dec(v_h__4_545_);
            crate::leanh::lean_dec(v_h__3_544_);
            crate::leanh::lean_dec(v_h__2_543_);
            crate::leanh::lean_dec(v_h__1_542_);
            v_a_564_ = crate::leanh::lean_ctor_get(v_x_541_, 0);
            crate::leanh::lean_inc_ref(v_a_564_);
            v_b_565_ = crate::leanh::lean_ctor_get(v_x_541_, 1);
            crate::leanh::lean_inc_ref(v_b_565_);
            crate::leanh::lean_dec_ref_known(v_x_541_, 2);
            v___x_566_ = crate::leanh::lean_apply_2(v_h__7_548_, v_a_564_, v_b_565_);
            return v___x_566_;
        }
        7 => {
            let mut v_a_567_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_b_568_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_569_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__9_550_);
            crate::leanh::lean_dec(v_h__8_549_);
            crate::leanh::lean_dec(v_h__7_548_);
            crate::leanh::lean_dec(v_h__6_547_);
            crate::leanh::lean_dec(v_h__4_545_);
            crate::leanh::lean_dec(v_h__3_544_);
            crate::leanh::lean_dec(v_h__2_543_);
            crate::leanh::lean_dec(v_h__1_542_);
            v_a_567_ = crate::leanh::lean_ctor_get(v_x_541_, 0);
            crate::leanh::lean_inc_ref(v_a_567_);
            v_b_568_ = crate::leanh::lean_ctor_get(v_x_541_, 1);
            crate::leanh::lean_inc_ref(v_b_568_);
            crate::leanh::lean_dec_ref_known(v_x_541_, 2);
            v___x_569_ = crate::leanh::lean_apply_2(v_h__5_546_, v_a_567_, v_b_568_);
            return v___x_569_;
        }
        _ => {
            let mut v_a_570_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_k_571_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_572_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__9_550_);
            crate::leanh::lean_dec(v_h__8_549_);
            crate::leanh::lean_dec(v_h__7_548_);
            crate::leanh::lean_dec(v_h__5_546_);
            crate::leanh::lean_dec(v_h__4_545_);
            crate::leanh::lean_dec(v_h__3_544_);
            crate::leanh::lean_dec(v_h__2_543_);
            crate::leanh::lean_dec(v_h__1_542_);
            v_a_570_ = crate::leanh::lean_ctor_get(v_x_541_, 0);
            crate::leanh::lean_inc_ref(v_a_570_);
            v_k_571_ = crate::leanh::lean_ctor_get(v_x_541_, 1);
            crate::leanh::lean_inc(v_k_571_);
            crate::leanh::lean_dec_ref_known(v_x_541_, 2);
            v___x_572_ = crate::leanh::lean_apply_2(v_h__6_547_, v_a_570_, v_k_571_);
            return v___x_572_;
        }
    }
}
pub unsafe fn l___private_Init_Grind_Ring_CommSemiringAdapter_0__Lean_Grind_CommRing_Expr_denoteS_match__1_splitter(
    mut v_motive_573_: *mut crate::leanh::LeanObject,
    mut v_x_574_: *mut crate::leanh::LeanObject,
    mut v_h__1_575_: *mut crate::leanh::LeanObject,
    mut v_h__2_576_: *mut crate::leanh::LeanObject,
    mut v_h__3_577_: *mut crate::leanh::LeanObject,
    mut v_h__4_578_: *mut crate::leanh::LeanObject,
    mut v_h__5_579_: *mut crate::leanh::LeanObject,
    mut v_h__6_580_: *mut crate::leanh::LeanObject,
    mut v_h__7_581_: *mut crate::leanh::LeanObject,
    mut v_h__8_582_: *mut crate::leanh::LeanObject,
    mut v_h__9_583_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    match crate::leanh::lean_obj_tag(v_x_574_) {
        0 => {
            let mut v_k_584_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_585_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__9_583_);
            crate::leanh::lean_dec(v_h__8_582_);
            crate::leanh::lean_dec(v_h__7_581_);
            crate::leanh::lean_dec(v_h__6_580_);
            crate::leanh::lean_dec(v_h__5_579_);
            crate::leanh::lean_dec(v_h__4_578_);
            crate::leanh::lean_dec(v_h__3_577_);
            crate::leanh::lean_dec(v_h__2_576_);
            v_k_584_ = crate::leanh::lean_ctor_get(v_x_574_, 0);
            crate::leanh::lean_inc(v_k_584_);
            crate::leanh::lean_dec_ref_known(v_x_574_, 1);
            v___x_585_ = crate::leanh::lean_apply_1(v_h__1_575_, v_k_584_);
            return v___x_585_;
        }
        1 => {
            let mut v_k_586_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_587_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__9_583_);
            crate::leanh::lean_dec(v_h__8_582_);
            crate::leanh::lean_dec(v_h__7_581_);
            crate::leanh::lean_dec(v_h__6_580_);
            crate::leanh::lean_dec(v_h__5_579_);
            crate::leanh::lean_dec(v_h__4_578_);
            crate::leanh::lean_dec(v_h__3_577_);
            crate::leanh::lean_dec(v_h__1_575_);
            v_k_586_ = crate::leanh::lean_ctor_get(v_x_574_, 0);
            crate::leanh::lean_inc(v_k_586_);
            crate::leanh::lean_dec_ref_known(v_x_574_, 1);
            v___x_587_ = crate::leanh::lean_apply_1(v_h__2_576_, v_k_586_);
            return v___x_587_;
        }
        2 => {
            let mut v_k_588_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_589_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__8_582_);
            crate::leanh::lean_dec(v_h__7_581_);
            crate::leanh::lean_dec(v_h__6_580_);
            crate::leanh::lean_dec(v_h__5_579_);
            crate::leanh::lean_dec(v_h__4_578_);
            crate::leanh::lean_dec(v_h__3_577_);
            crate::leanh::lean_dec(v_h__2_576_);
            crate::leanh::lean_dec(v_h__1_575_);
            v_k_588_ = crate::leanh::lean_ctor_get(v_x_574_, 0);
            crate::leanh::lean_inc(v_k_588_);
            crate::leanh::lean_dec_ref_known(v_x_574_, 1);
            v___x_589_ = crate::leanh::lean_apply_1(v_h__9_583_, v_k_588_);
            return v___x_589_;
        }
        3 => {
            let mut v_i_590_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_591_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__9_583_);
            crate::leanh::lean_dec(v_h__8_582_);
            crate::leanh::lean_dec(v_h__7_581_);
            crate::leanh::lean_dec(v_h__6_580_);
            crate::leanh::lean_dec(v_h__5_579_);
            crate::leanh::lean_dec(v_h__4_578_);
            crate::leanh::lean_dec(v_h__2_576_);
            crate::leanh::lean_dec(v_h__1_575_);
            v_i_590_ = crate::leanh::lean_ctor_get(v_x_574_, 0);
            crate::leanh::lean_inc(v_i_590_);
            crate::leanh::lean_dec_ref_known(v_x_574_, 1);
            v___x_591_ = crate::leanh::lean_apply_1(v_h__3_577_, v_i_590_);
            return v___x_591_;
        }
        4 => {
            let mut v_a_592_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_593_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__9_583_);
            crate::leanh::lean_dec(v_h__7_581_);
            crate::leanh::lean_dec(v_h__6_580_);
            crate::leanh::lean_dec(v_h__5_579_);
            crate::leanh::lean_dec(v_h__4_578_);
            crate::leanh::lean_dec(v_h__3_577_);
            crate::leanh::lean_dec(v_h__2_576_);
            crate::leanh::lean_dec(v_h__1_575_);
            v_a_592_ = crate::leanh::lean_ctor_get(v_x_574_, 0);
            crate::leanh::lean_inc_ref(v_a_592_);
            crate::leanh::lean_dec_ref_known(v_x_574_, 1);
            v___x_593_ = crate::leanh::lean_apply_1(v_h__8_582_, v_a_592_);
            return v___x_593_;
        }
        5 => {
            let mut v_a_594_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_b_595_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_596_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__9_583_);
            crate::leanh::lean_dec(v_h__8_582_);
            crate::leanh::lean_dec(v_h__7_581_);
            crate::leanh::lean_dec(v_h__6_580_);
            crate::leanh::lean_dec(v_h__5_579_);
            crate::leanh::lean_dec(v_h__3_577_);
            crate::leanh::lean_dec(v_h__2_576_);
            crate::leanh::lean_dec(v_h__1_575_);
            v_a_594_ = crate::leanh::lean_ctor_get(v_x_574_, 0);
            crate::leanh::lean_inc_ref(v_a_594_);
            v_b_595_ = crate::leanh::lean_ctor_get(v_x_574_, 1);
            crate::leanh::lean_inc_ref(v_b_595_);
            crate::leanh::lean_dec_ref_known(v_x_574_, 2);
            v___x_596_ = crate::leanh::lean_apply_2(v_h__4_578_, v_a_594_, v_b_595_);
            return v___x_596_;
        }
        6 => {
            let mut v_a_597_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_b_598_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_599_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__9_583_);
            crate::leanh::lean_dec(v_h__8_582_);
            crate::leanh::lean_dec(v_h__6_580_);
            crate::leanh::lean_dec(v_h__5_579_);
            crate::leanh::lean_dec(v_h__4_578_);
            crate::leanh::lean_dec(v_h__3_577_);
            crate::leanh::lean_dec(v_h__2_576_);
            crate::leanh::lean_dec(v_h__1_575_);
            v_a_597_ = crate::leanh::lean_ctor_get(v_x_574_, 0);
            crate::leanh::lean_inc_ref(v_a_597_);
            v_b_598_ = crate::leanh::lean_ctor_get(v_x_574_, 1);
            crate::leanh::lean_inc_ref(v_b_598_);
            crate::leanh::lean_dec_ref_known(v_x_574_, 2);
            v___x_599_ = crate::leanh::lean_apply_2(v_h__7_581_, v_a_597_, v_b_598_);
            return v___x_599_;
        }
        7 => {
            let mut v_a_600_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_b_601_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_602_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__9_583_);
            crate::leanh::lean_dec(v_h__8_582_);
            crate::leanh::lean_dec(v_h__7_581_);
            crate::leanh::lean_dec(v_h__6_580_);
            crate::leanh::lean_dec(v_h__4_578_);
            crate::leanh::lean_dec(v_h__3_577_);
            crate::leanh::lean_dec(v_h__2_576_);
            crate::leanh::lean_dec(v_h__1_575_);
            v_a_600_ = crate::leanh::lean_ctor_get(v_x_574_, 0);
            crate::leanh::lean_inc_ref(v_a_600_);
            v_b_601_ = crate::leanh::lean_ctor_get(v_x_574_, 1);
            crate::leanh::lean_inc_ref(v_b_601_);
            crate::leanh::lean_dec_ref_known(v_x_574_, 2);
            v___x_602_ = crate::leanh::lean_apply_2(v_h__5_579_, v_a_600_, v_b_601_);
            return v___x_602_;
        }
        _ => {
            let mut v_a_603_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_k_604_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_605_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__9_583_);
            crate::leanh::lean_dec(v_h__8_582_);
            crate::leanh::lean_dec(v_h__7_581_);
            crate::leanh::lean_dec(v_h__5_579_);
            crate::leanh::lean_dec(v_h__4_578_);
            crate::leanh::lean_dec(v_h__3_577_);
            crate::leanh::lean_dec(v_h__2_576_);
            crate::leanh::lean_dec(v_h__1_575_);
            v_a_603_ = crate::leanh::lean_ctor_get(v_x_574_, 0);
            crate::leanh::lean_inc_ref(v_a_603_);
            v_k_604_ = crate::leanh::lean_ctor_get(v_x_574_, 1);
            crate::leanh::lean_inc(v_k_604_);
            crate::leanh::lean_dec_ref_known(v_x_574_, 2);
            v___x_605_ = crate::leanh::lean_apply_2(v_h__6_580_, v_a_603_, v_k_604_);
            return v___x_605_;
        }
    }
}
pub unsafe fn l_Nat_cast___at___00Lean_Grind_CommRing_Expr_toPolyS_spec__0(
    mut v_a_606_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_607_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_607_ = lean_nat_to_int(v_a_606_);
    return v___x_607_;
}
pub unsafe fn _init_l_Lean_Grind_CommRing_Expr_toPolyS___closed__0() -> *mut crate::leanh::LeanObject
{
    let mut v___x_608_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_609_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_608_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_609_ = lean_nat_to_int(v___x_608_);
    return v___x_609_;
}
pub unsafe fn _init_l_Lean_Grind_CommRing_Expr_toPolyS___closed__1() -> *mut crate::leanh::LeanObject
{
    let mut v___x_610_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_611_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_610_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Grind_CommRing_Expr_toPolyS___closed__0),
        core::ptr::addr_of_mut!(l_Lean_Grind_CommRing_Expr_toPolyS___closed__0_once),
        _init_l_Lean_Grind_CommRing_Expr_toPolyS___closed__0,
    );
    v___x_611_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_611_, 0, v___x_610_);
    return v___x_611_;
}
pub unsafe fn l_Lean_Grind_CommRing_Expr_toPolyS(
    mut v_x_612_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_k_613_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_615_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_616_: u8 = 0;
    let mut v___x_617_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_618_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_620_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_621_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_622_: u8 = 0;
    let mut v_k_623_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_625_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_626_: u8 = 0;
    let mut v___x_627_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_629_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_630_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_631_: u8 = 0;
    let mut v_i_632_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_633_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_634_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_b_635_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_636_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_637_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_638_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_639_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_b_640_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_641_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_642_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_643_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_644_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_645_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_646_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_648_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_649_: u8 = 0;
    let mut v___x_650_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_651_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_652_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_654_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_655_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_656_: u8 = 0;
    let mut v_k_657_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_659_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_660_: u8 = 0;
    let mut v_i_661_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_663_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_664_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_665_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_666_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_667_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_668_: u8 = 0;
    let mut v_unused_669_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_670_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_671_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_672_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_673_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => match crate::leanh::lean_obj_tag(v_x_612_) {
                0 => {
                    v_k_613_ = crate::leanh::lean_ctor_get(v_x_612_, 0);
                    v_isSharedCheck_622_ = (!crate::leanh::lean_is_exclusive(v_x_612_)) as u8;
                    if v_isSharedCheck_622_ == 0 {
                        v___x_615_ = v_x_612_;
                        v_isShared_616_ = v_isSharedCheck_622_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_k_613_);
                        crate::leanh::lean_dec(v_x_612_);
                        v___x_615_ = crate::leanh::lean_box(0);
                        v_isShared_616_ = v_isSharedCheck_622_;
                        state = 1;
                        continue;
                    }
                }
                1 => {
                    v_k_623_ = crate::leanh::lean_ctor_get(v_x_612_, 0);
                    v_isSharedCheck_631_ = (!crate::leanh::lean_is_exclusive(v_x_612_)) as u8;
                    if v_isSharedCheck_631_ == 0 {
                        v___x_625_ = v_x_612_;
                        v_isShared_626_ = v_isSharedCheck_631_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_k_623_);
                        crate::leanh::lean_dec(v_x_612_);
                        v___x_625_ = crate::leanh::lean_box(0);
                        v_isShared_626_ = v_isSharedCheck_631_;
                        state = 3;
                        continue;
                    }
                }
                3 => {
                    v_i_632_ = crate::leanh::lean_ctor_get(v_x_612_, 0);
                    crate::leanh::lean_inc(v_i_632_);
                    crate::leanh::lean_dec_ref_known(v_x_612_, 1);
                    v___x_633_ = l_Lean_Grind_CommRing_Poly_ofVar(v_i_632_);
                    return v___x_633_;
                }
                5 => {
                    v_a_634_ = crate::leanh::lean_ctor_get(v_x_612_, 0);
                    crate::leanh::lean_inc_ref(v_a_634_);
                    v_b_635_ = crate::leanh::lean_ctor_get(v_x_612_, 1);
                    crate::leanh::lean_inc_ref(v_b_635_);
                    crate::leanh::lean_dec_ref_known(v_x_612_, 2);
                    v___x_636_ = l_Lean_Grind_CommRing_Expr_toPolyS(v_a_634_);
                    v___x_637_ = l_Lean_Grind_CommRing_Expr_toPolyS(v_b_635_);
                    v___x_638_ = l_Lean_Grind_CommRing_Poly_combine(v___x_636_, v___x_637_);
                    return v___x_638_;
                }
                7 => {
                    v_a_639_ = crate::leanh::lean_ctor_get(v_x_612_, 0);
                    crate::leanh::lean_inc_ref(v_a_639_);
                    v_b_640_ = crate::leanh::lean_ctor_get(v_x_612_, 1);
                    crate::leanh::lean_inc_ref(v_b_640_);
                    crate::leanh::lean_dec_ref_known(v_x_612_, 2);
                    v___x_641_ = l_Lean_Grind_CommRing_Expr_toPolyS(v_a_639_);
                    v___x_642_ = l_Lean_Grind_CommRing_Expr_toPolyS(v_b_640_);
                    v___x_643_ = l_Lean_Grind_CommRing_Poly_mul(v___x_641_, v___x_642_);
                    return v___x_643_;
                }
                8 => {
                    v_a_644_ = crate::leanh::lean_ctor_get(v_x_612_, 0);
                    crate::leanh::lean_inc_ref(v_a_644_);
                    match crate::leanh::lean_obj_tag(v_a_644_) {
                        0 => {
                            v_k_645_ = crate::leanh::lean_ctor_get(v_x_612_, 1);
                            crate::leanh::lean_inc(v_k_645_);
                            crate::leanh::lean_dec_ref_known(v_x_612_, 2);
                            v_k_646_ = crate::leanh::lean_ctor_get(v_a_644_, 0);
                            v_isSharedCheck_656_ =
                                (!crate::leanh::lean_is_exclusive(v_a_644_)) as u8;
                            if v_isSharedCheck_656_ == 0 {
                                v___x_648_ = v_a_644_;
                                v_isShared_649_ = v_isSharedCheck_656_;
                                state = 5;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_k_646_);
                                crate::leanh::lean_dec(v_a_644_);
                                v___x_648_ = crate::leanh::lean_box(0);
                                v_isShared_649_ = v_isSharedCheck_656_;
                                state = 5;
                                continue;
                            }
                        }
                        3 => {
                            v_k_657_ = crate::leanh::lean_ctor_get(v_x_612_, 1);
                            v_isSharedCheck_668_ =
                                (!crate::leanh::lean_is_exclusive(v_x_612_)) as u8;
                            if v_isSharedCheck_668_ == 0 {
                                v_unused_669_ = crate::leanh::lean_ctor_get(v_x_612_, 0);
                                crate::leanh::lean_dec(v_unused_669_);
                                v___x_659_ = v_x_612_;
                                v_isShared_660_ = v_isSharedCheck_668_;
                                state = 7;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_k_657_);
                                crate::leanh::lean_dec(v_x_612_);
                                v___x_659_ = crate::leanh::lean_box(0);
                                v_isShared_660_ = v_isSharedCheck_668_;
                                state = 7;
                                continue;
                            }
                        }
                        _ => {
                            v_k_670_ = crate::leanh::lean_ctor_get(v_x_612_, 1);
                            crate::leanh::lean_inc(v_k_670_);
                            crate::leanh::lean_dec_ref_known(v_x_612_, 2);
                            v___x_671_ = l_Lean_Grind_CommRing_Expr_toPolyS(v_a_644_);
                            v___x_672_ = l_Lean_Grind_CommRing_Poly_pow(v___x_671_, v_k_670_);
                            crate::leanh::lean_dec(v_k_670_);
                            return v___x_672_;
                        }
                    }
                }
                _ => {
                    crate::leanh::lean_dec_ref(v_x_612_);
                    v___x_673_ = crate::leanh::lean_obj_once(
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
                crate::leanh::lean_dec(v_k_613_);
                v___x_618_ = lean_nat_to_int(v___x_617_);
                if v_isShared_616_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_615_, 0, v___x_618_);
                    v___x_620_ = v___x_615_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_621_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_621_, 0, v___x_618_);
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
                    crate::leanh::lean_ctor_set_tag(v___x_625_, 0);
                    crate::leanh::lean_ctor_set(v___x_625_, 0, v___x_627_);
                    v___x_629_ = v___x_625_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_630_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_630_, 0, v___x_627_);
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
                crate::leanh::lean_dec(v_k_646_);
                v___x_651_ = lean_nat_to_int(v___x_650_);
                v___x_652_ = l_Int_pow(v___x_651_, v_k_645_);
                crate::leanh::lean_dec(v_k_645_);
                crate::leanh::lean_dec(v___x_651_);
                if v_isShared_649_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_648_, 0, v___x_652_);
                    v___x_654_ = v___x_648_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_655_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_655_, 0, v___x_652_);
                    v___x_654_ = v_reuseFailAlloc_655_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_654_;
            }
            7 => {
                v_i_661_ = crate::leanh::lean_ctor_get(v_a_644_, 0);
                crate::leanh::lean_inc(v_i_661_);
                crate::leanh::lean_dec_ref_known(v_a_644_, 1);
                if v_isShared_660_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_659_, 0);
                    crate::leanh::lean_ctor_set(v___x_659_, 0, v_i_661_);
                    v___x_663_ = v___x_659_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_667_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_667_, 0, v_i_661_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_667_, 1, v_k_657_);
                    v___x_663_ = v_reuseFailAlloc_667_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                v___x_664_ = crate::leanh::lean_box(0);
                v___x_665_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_665_, 0, v___x_663_);
                crate::leanh::lean_ctor_set(v___x_665_, 1, v___x_664_);
                v___x_666_ = l_Lean_Grind_CommRing_Poly_ofMon(v___x_665_);
                return v___x_666_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Grind_CommRing_Expr_toPolyS__nc(
    mut v_x_674_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_k_675_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_677_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_678_: u8 = 0;
    let mut v___x_679_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_680_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_682_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_683_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_684_: u8 = 0;
    let mut v_k_685_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_687_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_688_: u8 = 0;
    let mut v___x_689_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_691_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_692_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_693_: u8 = 0;
    let mut v_i_694_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_695_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_696_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_b_697_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_698_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_699_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_700_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_701_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_b_702_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_703_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_704_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_705_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_706_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_707_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_708_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_710_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_711_: u8 = 0;
    let mut v___x_712_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_713_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_714_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_716_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_717_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_718_: u8 = 0;
    let mut v_k_719_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_721_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_722_: u8 = 0;
    let mut v_i_723_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_725_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_726_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_727_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_728_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_729_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_730_: u8 = 0;
    let mut v_unused_731_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_732_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_733_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_734_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_735_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => match crate::leanh::lean_obj_tag(v_x_674_) {
                0 => {
                    v_k_675_ = crate::leanh::lean_ctor_get(v_x_674_, 0);
                    v_isSharedCheck_684_ = (!crate::leanh::lean_is_exclusive(v_x_674_)) as u8;
                    if v_isSharedCheck_684_ == 0 {
                        v___x_677_ = v_x_674_;
                        v_isShared_678_ = v_isSharedCheck_684_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_k_675_);
                        crate::leanh::lean_dec(v_x_674_);
                        v___x_677_ = crate::leanh::lean_box(0);
                        v_isShared_678_ = v_isSharedCheck_684_;
                        state = 1;
                        continue;
                    }
                }
                1 => {
                    v_k_685_ = crate::leanh::lean_ctor_get(v_x_674_, 0);
                    v_isSharedCheck_693_ = (!crate::leanh::lean_is_exclusive(v_x_674_)) as u8;
                    if v_isSharedCheck_693_ == 0 {
                        v___x_687_ = v_x_674_;
                        v_isShared_688_ = v_isSharedCheck_693_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_k_685_);
                        crate::leanh::lean_dec(v_x_674_);
                        v___x_687_ = crate::leanh::lean_box(0);
                        v_isShared_688_ = v_isSharedCheck_693_;
                        state = 3;
                        continue;
                    }
                }
                3 => {
                    v_i_694_ = crate::leanh::lean_ctor_get(v_x_674_, 0);
                    crate::leanh::lean_inc(v_i_694_);
                    crate::leanh::lean_dec_ref_known(v_x_674_, 1);
                    v___x_695_ = l_Lean_Grind_CommRing_Poly_ofVar(v_i_694_);
                    return v___x_695_;
                }
                5 => {
                    v_a_696_ = crate::leanh::lean_ctor_get(v_x_674_, 0);
                    crate::leanh::lean_inc_ref(v_a_696_);
                    v_b_697_ = crate::leanh::lean_ctor_get(v_x_674_, 1);
                    crate::leanh::lean_inc_ref(v_b_697_);
                    crate::leanh::lean_dec_ref_known(v_x_674_, 2);
                    v___x_698_ = l_Lean_Grind_CommRing_Expr_toPolyS__nc(v_a_696_);
                    v___x_699_ = l_Lean_Grind_CommRing_Expr_toPolyS__nc(v_b_697_);
                    v___x_700_ = l_Lean_Grind_CommRing_Poly_combine(v___x_698_, v___x_699_);
                    return v___x_700_;
                }
                7 => {
                    v_a_701_ = crate::leanh::lean_ctor_get(v_x_674_, 0);
                    crate::leanh::lean_inc_ref(v_a_701_);
                    v_b_702_ = crate::leanh::lean_ctor_get(v_x_674_, 1);
                    crate::leanh::lean_inc_ref(v_b_702_);
                    crate::leanh::lean_dec_ref_known(v_x_674_, 2);
                    v___x_703_ = l_Lean_Grind_CommRing_Expr_toPolyS__nc(v_a_701_);
                    v___x_704_ = l_Lean_Grind_CommRing_Expr_toPolyS__nc(v_b_702_);
                    v___x_705_ = l_Lean_Grind_CommRing_Poly_mul__nc(v___x_703_, v___x_704_);
                    return v___x_705_;
                }
                8 => {
                    v_a_706_ = crate::leanh::lean_ctor_get(v_x_674_, 0);
                    crate::leanh::lean_inc_ref(v_a_706_);
                    match crate::leanh::lean_obj_tag(v_a_706_) {
                        0 => {
                            v_k_707_ = crate::leanh::lean_ctor_get(v_x_674_, 1);
                            crate::leanh::lean_inc(v_k_707_);
                            crate::leanh::lean_dec_ref_known(v_x_674_, 2);
                            v_k_708_ = crate::leanh::lean_ctor_get(v_a_706_, 0);
                            v_isSharedCheck_718_ =
                                (!crate::leanh::lean_is_exclusive(v_a_706_)) as u8;
                            if v_isSharedCheck_718_ == 0 {
                                v___x_710_ = v_a_706_;
                                v_isShared_711_ = v_isSharedCheck_718_;
                                state = 5;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_k_708_);
                                crate::leanh::lean_dec(v_a_706_);
                                v___x_710_ = crate::leanh::lean_box(0);
                                v_isShared_711_ = v_isSharedCheck_718_;
                                state = 5;
                                continue;
                            }
                        }
                        3 => {
                            v_k_719_ = crate::leanh::lean_ctor_get(v_x_674_, 1);
                            v_isSharedCheck_730_ =
                                (!crate::leanh::lean_is_exclusive(v_x_674_)) as u8;
                            if v_isSharedCheck_730_ == 0 {
                                v_unused_731_ = crate::leanh::lean_ctor_get(v_x_674_, 0);
                                crate::leanh::lean_dec(v_unused_731_);
                                v___x_721_ = v_x_674_;
                                v_isShared_722_ = v_isSharedCheck_730_;
                                state = 7;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_k_719_);
                                crate::leanh::lean_dec(v_x_674_);
                                v___x_721_ = crate::leanh::lean_box(0);
                                v_isShared_722_ = v_isSharedCheck_730_;
                                state = 7;
                                continue;
                            }
                        }
                        _ => {
                            v_k_732_ = crate::leanh::lean_ctor_get(v_x_674_, 1);
                            crate::leanh::lean_inc(v_k_732_);
                            crate::leanh::lean_dec_ref_known(v_x_674_, 2);
                            v___x_733_ = l_Lean_Grind_CommRing_Expr_toPolyS__nc(v_a_706_);
                            v___x_734_ = l_Lean_Grind_CommRing_Poly_pow__nc(v___x_733_, v_k_732_);
                            crate::leanh::lean_dec(v_k_732_);
                            return v___x_734_;
                        }
                    }
                }
                _ => {
                    crate::leanh::lean_dec_ref(v_x_674_);
                    v___x_735_ = crate::leanh::lean_obj_once(
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
                crate::leanh::lean_dec(v_k_675_);
                v___x_680_ = lean_nat_to_int(v___x_679_);
                if v_isShared_678_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_677_, 0, v___x_680_);
                    v___x_682_ = v___x_677_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_683_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_683_, 0, v___x_680_);
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
                    crate::leanh::lean_ctor_set_tag(v___x_687_, 0);
                    crate::leanh::lean_ctor_set(v___x_687_, 0, v___x_689_);
                    v___x_691_ = v___x_687_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_692_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_692_, 0, v___x_689_);
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
                crate::leanh::lean_dec(v_k_708_);
                v___x_713_ = lean_nat_to_int(v___x_712_);
                v___x_714_ = l_Int_pow(v___x_713_, v_k_707_);
                crate::leanh::lean_dec(v_k_707_);
                crate::leanh::lean_dec(v___x_713_);
                if v_isShared_711_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_710_, 0, v___x_714_);
                    v___x_716_ = v___x_710_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_717_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_717_, 0, v___x_714_);
                    v___x_716_ = v_reuseFailAlloc_717_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_716_;
            }
            7 => {
                v_i_723_ = crate::leanh::lean_ctor_get(v_a_706_, 0);
                crate::leanh::lean_inc(v_i_723_);
                crate::leanh::lean_dec_ref_known(v_a_706_, 1);
                if v_isShared_722_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_721_, 0);
                    crate::leanh::lean_ctor_set(v___x_721_, 0, v_i_723_);
                    v___x_725_ = v___x_721_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_729_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_729_, 0, v_i_723_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_729_, 1, v_k_719_);
                    v___x_725_ = v_reuseFailAlloc_729_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                v___x_726_ = crate::leanh::lean_box(0);
                v___x_727_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_727_, 0, v___x_725_);
                crate::leanh::lean_ctor_set(v___x_727_, 1, v___x_726_);
                v___x_728_ = l_Lean_Grind_CommRing_Poly_ofMon(v___x_727_);
                return v___x_728_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Grind_CommRing_denoteSInt___redArg(
    mut v_inst_736_: *mut crate::leanh::LeanObject,
    mut v_k_737_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_738_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_739_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_740_: u8 = 0;
    v___x_738_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_739_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Grind_CommRing_Expr_toPolyS___closed__0),
        core::ptr::addr_of_mut!(l_Lean_Grind_CommRing_Expr_toPolyS___closed__0_once),
        _init_l_Lean_Grind_CommRing_Expr_toPolyS___closed__0,
    );
    v___x_740_ = lean_int_dec_lt(v_k_737_, v___x_739_);
    if v___x_740_ == 0 {
        let mut v_ofNat_741_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_742_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_743_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_ofNat_741_ = crate::leanh::lean_ctor_get(v_inst_736_, 3);
        crate::leanh::lean_inc(v_ofNat_741_);
        crate::leanh::lean_dec_ref(v_inst_736_);
        v___x_742_ = lean_nat_abs(v_k_737_);
        v___x_743_ = crate::leanh::lean_apply_1(v_ofNat_741_, v___x_742_);
        return v___x_743_;
    } else {
        let mut v_ofNat_744_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_745_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_ofNat_744_ = crate::leanh::lean_ctor_get(v_inst_736_, 3);
        crate::leanh::lean_inc(v_ofNat_744_);
        crate::leanh::lean_dec_ref(v_inst_736_);
        v___x_745_ = crate::leanh::lean_apply_1(v_ofNat_744_, v___x_738_);
        return v___x_745_;
    }
}
pub unsafe fn l_Lean_Grind_CommRing_denoteSInt___redArg___boxed(
    mut v_inst_746_: *mut crate::leanh::LeanObject,
    mut v_k_747_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_748_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_748_ = l_Lean_Grind_CommRing_denoteSInt___redArg(v_inst_746_, v_k_747_);
    crate::leanh::lean_dec(v_k_747_);
    return v_res_748_;
}
pub unsafe fn l_Lean_Grind_CommRing_denoteSInt(
    mut v_00_u03b1_749_: *mut crate::leanh::LeanObject,
    mut v_inst_750_: *mut crate::leanh::LeanObject,
    mut v_k_751_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_752_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_752_ = l_Lean_Grind_CommRing_denoteSInt___redArg(v_inst_750_, v_k_751_);
    return v___x_752_;
}
pub unsafe fn l_Lean_Grind_CommRing_denoteSInt___boxed(
    mut v_00_u03b1_753_: *mut crate::leanh::LeanObject,
    mut v_inst_754_: *mut crate::leanh::LeanObject,
    mut v_k_755_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_756_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_756_ = l_Lean_Grind_CommRing_denoteSInt(v_00_u03b1_753_, v_inst_754_, v_k_755_);
    crate::leanh::lean_dec(v_k_755_);
    return v_res_756_;
}
pub unsafe fn l_Lean_Grind_CommRing_Poly_denoteS___redArg(
    mut v_inst_757_: *mut crate::leanh::LeanObject,
    mut v_ctx_758_: *mut crate::leanh::LeanObject,
    mut v_p_759_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_p_759_) == 0 {
        let mut v_k_760_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_761_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_k_760_ = crate::leanh::lean_ctor_get(v_p_759_, 0);
        crate::leanh::lean_inc(v_k_760_);
        crate::leanh::lean_dec_ref_known(v_p_759_, 1);
        v___x_761_ = l_Lean_Grind_CommRing_denoteSInt___redArg(v_inst_757_, v_k_760_);
        crate::leanh::lean_dec(v_k_760_);
        return v___x_761_;
    } else {
        let mut v_toAdd_762_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_toMul_763_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_k_764_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_v_765_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_p_766_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_767_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_768_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_769_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_770_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_771_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_toAdd_762_ = crate::leanh::lean_ctor_get(v_inst_757_, 0);
        crate::leanh::lean_inc(v_toAdd_762_);
        v_toMul_763_ = crate::leanh::lean_ctor_get(v_inst_757_, 1);
        v_k_764_ = crate::leanh::lean_ctor_get(v_p_759_, 0);
        crate::leanh::lean_inc(v_k_764_);
        v_v_765_ = crate::leanh::lean_ctor_get(v_p_759_, 1);
        crate::leanh::lean_inc(v_v_765_);
        v_p_766_ = crate::leanh::lean_ctor_get(v_p_759_, 2);
        crate::leanh::lean_inc_ref(v_p_766_);
        crate::leanh::lean_dec_ref_known(v_p_759_, 3);
        crate::leanh::lean_inc_ref_n(v_inst_757_, 2);
        v___x_767_ = l_Lean_Grind_CommRing_denoteSInt___redArg(v_inst_757_, v_k_764_);
        crate::leanh::lean_dec(v_k_764_);
        v___x_768_ = l_Lean_Grind_CommRing_Mon_denote___redArg(v_inst_757_, v_ctx_758_, v_v_765_);
        crate::leanh::lean_inc(v_toMul_763_);
        v___x_769_ = crate::leanh::lean_apply_2(v_toMul_763_, v___x_767_, v___x_768_);
        v___x_770_ = l_Lean_Grind_CommRing_Poly_denoteS___redArg(v_inst_757_, v_ctx_758_, v_p_766_);
        v___x_771_ = crate::leanh::lean_apply_2(v_toAdd_762_, v___x_769_, v___x_770_);
        return v___x_771_;
    }
}
pub unsafe fn l_Lean_Grind_CommRing_Poly_denoteS___redArg___boxed(
    mut v_inst_772_: *mut crate::leanh::LeanObject,
    mut v_ctx_773_: *mut crate::leanh::LeanObject,
    mut v_p_774_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_775_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_775_ = l_Lean_Grind_CommRing_Poly_denoteS___redArg(v_inst_772_, v_ctx_773_, v_p_774_);
    crate::leanh::lean_dec_ref(v_ctx_773_);
    return v_res_775_;
}
pub unsafe fn l_Lean_Grind_CommRing_Poly_denoteS(
    mut v_00_u03b1_776_: *mut crate::leanh::LeanObject,
    mut v_inst_777_: *mut crate::leanh::LeanObject,
    mut v_ctx_778_: *mut crate::leanh::LeanObject,
    mut v_p_779_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_780_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_780_ = l_Lean_Grind_CommRing_Poly_denoteS___redArg(v_inst_777_, v_ctx_778_, v_p_779_);
    return v___x_780_;
}
pub unsafe fn l_Lean_Grind_CommRing_Poly_denoteS___boxed(
    mut v_00_u03b1_781_: *mut crate::leanh::LeanObject,
    mut v_inst_782_: *mut crate::leanh::LeanObject,
    mut v_ctx_783_: *mut crate::leanh::LeanObject,
    mut v_p_784_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_785_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_785_ =
        l_Lean_Grind_CommRing_Poly_denoteS(v_00_u03b1_781_, v_inst_782_, v_ctx_783_, v_p_784_);
    crate::leanh::lean_dec_ref(v_ctx_783_);
    return v_res_785_;
}
pub unsafe fn l___private_Init_Grind_Ring_CommSemiringAdapter_0__Lean_Grind_CommRing_Poly_denoteS_match__1_splitter___redArg(
    mut v_p_786_: *mut crate::leanh::LeanObject,
    mut v_h__1_787_: *mut crate::leanh::LeanObject,
    mut v_h__2_788_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_p_786_) == 0 {
        let mut v_k_789_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_790_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_788_);
        v_k_789_ = crate::leanh::lean_ctor_get(v_p_786_, 0);
        crate::leanh::lean_inc(v_k_789_);
        crate::leanh::lean_dec_ref_known(v_p_786_, 1);
        v___x_790_ = crate::leanh::lean_apply_1(v_h__1_787_, v_k_789_);
        return v___x_790_;
    } else {
        let mut v_k_791_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_v_792_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_p_793_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_794_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_787_);
        v_k_791_ = crate::leanh::lean_ctor_get(v_p_786_, 0);
        crate::leanh::lean_inc(v_k_791_);
        v_v_792_ = crate::leanh::lean_ctor_get(v_p_786_, 1);
        crate::leanh::lean_inc(v_v_792_);
        v_p_793_ = crate::leanh::lean_ctor_get(v_p_786_, 2);
        crate::leanh::lean_inc_ref(v_p_793_);
        crate::leanh::lean_dec_ref_known(v_p_786_, 3);
        v___x_794_ = crate::leanh::lean_apply_3(v_h__2_788_, v_k_791_, v_v_792_, v_p_793_);
        return v___x_794_;
    }
}
pub unsafe fn l___private_Init_Grind_Ring_CommSemiringAdapter_0__Lean_Grind_CommRing_Poly_denoteS_match__1_splitter(
    mut v_motive_795_: *mut crate::leanh::LeanObject,
    mut v_p_796_: *mut crate::leanh::LeanObject,
    mut v_h__1_797_: *mut crate::leanh::LeanObject,
    mut v_h__2_798_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_p_796_) == 0 {
        let mut v_k_799_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_800_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_798_);
        v_k_799_ = crate::leanh::lean_ctor_get(v_p_796_, 0);
        crate::leanh::lean_inc(v_k_799_);
        crate::leanh::lean_dec_ref_known(v_p_796_, 1);
        v___x_800_ = crate::leanh::lean_apply_1(v_h__1_797_, v_k_799_);
        return v___x_800_;
    } else {
        let mut v_k_801_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_v_802_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_p_803_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_804_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_797_);
        v_k_801_ = crate::leanh::lean_ctor_get(v_p_796_, 0);
        crate::leanh::lean_inc(v_k_801_);
        v_v_802_ = crate::leanh::lean_ctor_get(v_p_796_, 1);
        crate::leanh::lean_inc(v_v_802_);
        v_p_803_ = crate::leanh::lean_ctor_get(v_p_796_, 2);
        crate::leanh::lean_inc_ref(v_p_803_);
        crate::leanh::lean_dec_ref_known(v_p_796_, 3);
        v___x_804_ = crate::leanh::lean_apply_3(v_h__2_798_, v_k_801_, v_v_802_, v_p_803_);
        return v___x_804_;
    }
}
pub unsafe fn l___private_Init_Grind_Ring_CommSemiringAdapter_0__Lean_Grind_CommRing_Expr_toPolyS_match__4_splitter___redArg(
    mut v_x_805_: *mut crate::leanh::LeanObject,
    mut v_h__1_806_: *mut crate::leanh::LeanObject,
    mut v_h__2_807_: *mut crate::leanh::LeanObject,
    mut v_h__3_808_: *mut crate::leanh::LeanObject,
    mut v_h__4_809_: *mut crate::leanh::LeanObject,
    mut v_h__5_810_: *mut crate::leanh::LeanObject,
    mut v_h__6_811_: *mut crate::leanh::LeanObject,
    mut v_h__7_812_: *mut crate::leanh::LeanObject,
    mut v_h__8_813_: *mut crate::leanh::LeanObject,
    mut v_h__9_814_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    match crate::leanh::lean_obj_tag(v_x_805_) {
        0 => {
            let mut v_k_815_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_816_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__9_814_);
            crate::leanh::lean_dec(v_h__8_813_);
            crate::leanh::lean_dec(v_h__7_812_);
            crate::leanh::lean_dec(v_h__6_811_);
            crate::leanh::lean_dec(v_h__5_810_);
            crate::leanh::lean_dec(v_h__4_809_);
            crate::leanh::lean_dec(v_h__3_808_);
            crate::leanh::lean_dec(v_h__2_807_);
            v_k_815_ = crate::leanh::lean_ctor_get(v_x_805_, 0);
            crate::leanh::lean_inc(v_k_815_);
            crate::leanh::lean_dec_ref_known(v_x_805_, 1);
            v___x_816_ = crate::leanh::lean_apply_1(v_h__1_806_, v_k_815_);
            return v___x_816_;
        }
        1 => {
            let mut v_k_817_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_818_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__9_814_);
            crate::leanh::lean_dec(v_h__8_813_);
            crate::leanh::lean_dec(v_h__7_812_);
            crate::leanh::lean_dec(v_h__5_810_);
            crate::leanh::lean_dec(v_h__4_809_);
            crate::leanh::lean_dec(v_h__3_808_);
            crate::leanh::lean_dec(v_h__2_807_);
            crate::leanh::lean_dec(v_h__1_806_);
            v_k_817_ = crate::leanh::lean_ctor_get(v_x_805_, 0);
            crate::leanh::lean_inc(v_k_817_);
            crate::leanh::lean_dec_ref_known(v_x_805_, 1);
            v___x_818_ = crate::leanh::lean_apply_1(v_h__6_811_, v_k_817_);
            return v___x_818_;
        }
        2 => {
            let mut v_k_819_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_820_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__8_813_);
            crate::leanh::lean_dec(v_h__7_812_);
            crate::leanh::lean_dec(v_h__6_811_);
            crate::leanh::lean_dec(v_h__5_810_);
            crate::leanh::lean_dec(v_h__4_809_);
            crate::leanh::lean_dec(v_h__3_808_);
            crate::leanh::lean_dec(v_h__2_807_);
            crate::leanh::lean_dec(v_h__1_806_);
            v_k_819_ = crate::leanh::lean_ctor_get(v_x_805_, 0);
            crate::leanh::lean_inc(v_k_819_);
            crate::leanh::lean_dec_ref_known(v_x_805_, 1);
            v___x_820_ = crate::leanh::lean_apply_1(v_h__9_814_, v_k_819_);
            return v___x_820_;
        }
        3 => {
            let mut v_i_821_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_822_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__9_814_);
            crate::leanh::lean_dec(v_h__8_813_);
            crate::leanh::lean_dec(v_h__7_812_);
            crate::leanh::lean_dec(v_h__6_811_);
            crate::leanh::lean_dec(v_h__5_810_);
            crate::leanh::lean_dec(v_h__4_809_);
            crate::leanh::lean_dec(v_h__3_808_);
            crate::leanh::lean_dec(v_h__1_806_);
            v_i_821_ = crate::leanh::lean_ctor_get(v_x_805_, 0);
            crate::leanh::lean_inc(v_i_821_);
            crate::leanh::lean_dec_ref_known(v_x_805_, 1);
            v___x_822_ = crate::leanh::lean_apply_1(v_h__2_807_, v_i_821_);
            return v___x_822_;
        }
        4 => {
            let mut v_a_823_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_824_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__9_814_);
            crate::leanh::lean_dec(v_h__7_812_);
            crate::leanh::lean_dec(v_h__6_811_);
            crate::leanh::lean_dec(v_h__5_810_);
            crate::leanh::lean_dec(v_h__4_809_);
            crate::leanh::lean_dec(v_h__3_808_);
            crate::leanh::lean_dec(v_h__2_807_);
            crate::leanh::lean_dec(v_h__1_806_);
            v_a_823_ = crate::leanh::lean_ctor_get(v_x_805_, 0);
            crate::leanh::lean_inc_ref(v_a_823_);
            crate::leanh::lean_dec_ref_known(v_x_805_, 1);
            v___x_824_ = crate::leanh::lean_apply_1(v_h__8_813_, v_a_823_);
            return v___x_824_;
        }
        5 => {
            let mut v_a_825_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_b_826_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_827_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__9_814_);
            crate::leanh::lean_dec(v_h__8_813_);
            crate::leanh::lean_dec(v_h__7_812_);
            crate::leanh::lean_dec(v_h__6_811_);
            crate::leanh::lean_dec(v_h__5_810_);
            crate::leanh::lean_dec(v_h__4_809_);
            crate::leanh::lean_dec(v_h__2_807_);
            crate::leanh::lean_dec(v_h__1_806_);
            v_a_825_ = crate::leanh::lean_ctor_get(v_x_805_, 0);
            crate::leanh::lean_inc_ref(v_a_825_);
            v_b_826_ = crate::leanh::lean_ctor_get(v_x_805_, 1);
            crate::leanh::lean_inc_ref(v_b_826_);
            crate::leanh::lean_dec_ref_known(v_x_805_, 2);
            v___x_827_ = crate::leanh::lean_apply_2(v_h__3_808_, v_a_825_, v_b_826_);
            return v___x_827_;
        }
        6 => {
            let mut v_a_828_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_b_829_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_830_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__9_814_);
            crate::leanh::lean_dec(v_h__8_813_);
            crate::leanh::lean_dec(v_h__6_811_);
            crate::leanh::lean_dec(v_h__5_810_);
            crate::leanh::lean_dec(v_h__4_809_);
            crate::leanh::lean_dec(v_h__3_808_);
            crate::leanh::lean_dec(v_h__2_807_);
            crate::leanh::lean_dec(v_h__1_806_);
            v_a_828_ = crate::leanh::lean_ctor_get(v_x_805_, 0);
            crate::leanh::lean_inc_ref(v_a_828_);
            v_b_829_ = crate::leanh::lean_ctor_get(v_x_805_, 1);
            crate::leanh::lean_inc_ref(v_b_829_);
            crate::leanh::lean_dec_ref_known(v_x_805_, 2);
            v___x_830_ = crate::leanh::lean_apply_2(v_h__7_812_, v_a_828_, v_b_829_);
            return v___x_830_;
        }
        7 => {
            let mut v_a_831_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_b_832_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_833_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__9_814_);
            crate::leanh::lean_dec(v_h__8_813_);
            crate::leanh::lean_dec(v_h__7_812_);
            crate::leanh::lean_dec(v_h__6_811_);
            crate::leanh::lean_dec(v_h__5_810_);
            crate::leanh::lean_dec(v_h__3_808_);
            crate::leanh::lean_dec(v_h__2_807_);
            crate::leanh::lean_dec(v_h__1_806_);
            v_a_831_ = crate::leanh::lean_ctor_get(v_x_805_, 0);
            crate::leanh::lean_inc_ref(v_a_831_);
            v_b_832_ = crate::leanh::lean_ctor_get(v_x_805_, 1);
            crate::leanh::lean_inc_ref(v_b_832_);
            crate::leanh::lean_dec_ref_known(v_x_805_, 2);
            v___x_833_ = crate::leanh::lean_apply_2(v_h__4_809_, v_a_831_, v_b_832_);
            return v___x_833_;
        }
        _ => {
            let mut v_a_834_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_k_835_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_836_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__9_814_);
            crate::leanh::lean_dec(v_h__8_813_);
            crate::leanh::lean_dec(v_h__7_812_);
            crate::leanh::lean_dec(v_h__6_811_);
            crate::leanh::lean_dec(v_h__4_809_);
            crate::leanh::lean_dec(v_h__3_808_);
            crate::leanh::lean_dec(v_h__2_807_);
            crate::leanh::lean_dec(v_h__1_806_);
            v_a_834_ = crate::leanh::lean_ctor_get(v_x_805_, 0);
            crate::leanh::lean_inc_ref(v_a_834_);
            v_k_835_ = crate::leanh::lean_ctor_get(v_x_805_, 1);
            crate::leanh::lean_inc(v_k_835_);
            crate::leanh::lean_dec_ref_known(v_x_805_, 2);
            v___x_836_ = crate::leanh::lean_apply_2(v_h__5_810_, v_a_834_, v_k_835_);
            return v___x_836_;
        }
    }
}
pub unsafe fn l___private_Init_Grind_Ring_CommSemiringAdapter_0__Lean_Grind_CommRing_Expr_toPolyS_match__4_splitter(
    mut v_motive_837_: *mut crate::leanh::LeanObject,
    mut v_x_838_: *mut crate::leanh::LeanObject,
    mut v_h__1_839_: *mut crate::leanh::LeanObject,
    mut v_h__2_840_: *mut crate::leanh::LeanObject,
    mut v_h__3_841_: *mut crate::leanh::LeanObject,
    mut v_h__4_842_: *mut crate::leanh::LeanObject,
    mut v_h__5_843_: *mut crate::leanh::LeanObject,
    mut v_h__6_844_: *mut crate::leanh::LeanObject,
    mut v_h__7_845_: *mut crate::leanh::LeanObject,
    mut v_h__8_846_: *mut crate::leanh::LeanObject,
    mut v_h__9_847_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    match crate::leanh::lean_obj_tag(v_x_838_) {
        0 => {
            let mut v_k_848_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_849_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__9_847_);
            crate::leanh::lean_dec(v_h__8_846_);
            crate::leanh::lean_dec(v_h__7_845_);
            crate::leanh::lean_dec(v_h__6_844_);
            crate::leanh::lean_dec(v_h__5_843_);
            crate::leanh::lean_dec(v_h__4_842_);
            crate::leanh::lean_dec(v_h__3_841_);
            crate::leanh::lean_dec(v_h__2_840_);
            v_k_848_ = crate::leanh::lean_ctor_get(v_x_838_, 0);
            crate::leanh::lean_inc(v_k_848_);
            crate::leanh::lean_dec_ref_known(v_x_838_, 1);
            v___x_849_ = crate::leanh::lean_apply_1(v_h__1_839_, v_k_848_);
            return v___x_849_;
        }
        1 => {
            let mut v_k_850_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_851_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__9_847_);
            crate::leanh::lean_dec(v_h__8_846_);
            crate::leanh::lean_dec(v_h__7_845_);
            crate::leanh::lean_dec(v_h__5_843_);
            crate::leanh::lean_dec(v_h__4_842_);
            crate::leanh::lean_dec(v_h__3_841_);
            crate::leanh::lean_dec(v_h__2_840_);
            crate::leanh::lean_dec(v_h__1_839_);
            v_k_850_ = crate::leanh::lean_ctor_get(v_x_838_, 0);
            crate::leanh::lean_inc(v_k_850_);
            crate::leanh::lean_dec_ref_known(v_x_838_, 1);
            v___x_851_ = crate::leanh::lean_apply_1(v_h__6_844_, v_k_850_);
            return v___x_851_;
        }
        2 => {
            let mut v_k_852_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_853_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__8_846_);
            crate::leanh::lean_dec(v_h__7_845_);
            crate::leanh::lean_dec(v_h__6_844_);
            crate::leanh::lean_dec(v_h__5_843_);
            crate::leanh::lean_dec(v_h__4_842_);
            crate::leanh::lean_dec(v_h__3_841_);
            crate::leanh::lean_dec(v_h__2_840_);
            crate::leanh::lean_dec(v_h__1_839_);
            v_k_852_ = crate::leanh::lean_ctor_get(v_x_838_, 0);
            crate::leanh::lean_inc(v_k_852_);
            crate::leanh::lean_dec_ref_known(v_x_838_, 1);
            v___x_853_ = crate::leanh::lean_apply_1(v_h__9_847_, v_k_852_);
            return v___x_853_;
        }
        3 => {
            let mut v_i_854_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_855_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__9_847_);
            crate::leanh::lean_dec(v_h__8_846_);
            crate::leanh::lean_dec(v_h__7_845_);
            crate::leanh::lean_dec(v_h__6_844_);
            crate::leanh::lean_dec(v_h__5_843_);
            crate::leanh::lean_dec(v_h__4_842_);
            crate::leanh::lean_dec(v_h__3_841_);
            crate::leanh::lean_dec(v_h__1_839_);
            v_i_854_ = crate::leanh::lean_ctor_get(v_x_838_, 0);
            crate::leanh::lean_inc(v_i_854_);
            crate::leanh::lean_dec_ref_known(v_x_838_, 1);
            v___x_855_ = crate::leanh::lean_apply_1(v_h__2_840_, v_i_854_);
            return v___x_855_;
        }
        4 => {
            let mut v_a_856_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_857_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__9_847_);
            crate::leanh::lean_dec(v_h__7_845_);
            crate::leanh::lean_dec(v_h__6_844_);
            crate::leanh::lean_dec(v_h__5_843_);
            crate::leanh::lean_dec(v_h__4_842_);
            crate::leanh::lean_dec(v_h__3_841_);
            crate::leanh::lean_dec(v_h__2_840_);
            crate::leanh::lean_dec(v_h__1_839_);
            v_a_856_ = crate::leanh::lean_ctor_get(v_x_838_, 0);
            crate::leanh::lean_inc_ref(v_a_856_);
            crate::leanh::lean_dec_ref_known(v_x_838_, 1);
            v___x_857_ = crate::leanh::lean_apply_1(v_h__8_846_, v_a_856_);
            return v___x_857_;
        }
        5 => {
            let mut v_a_858_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_b_859_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_860_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__9_847_);
            crate::leanh::lean_dec(v_h__8_846_);
            crate::leanh::lean_dec(v_h__7_845_);
            crate::leanh::lean_dec(v_h__6_844_);
            crate::leanh::lean_dec(v_h__5_843_);
            crate::leanh::lean_dec(v_h__4_842_);
            crate::leanh::lean_dec(v_h__2_840_);
            crate::leanh::lean_dec(v_h__1_839_);
            v_a_858_ = crate::leanh::lean_ctor_get(v_x_838_, 0);
            crate::leanh::lean_inc_ref(v_a_858_);
            v_b_859_ = crate::leanh::lean_ctor_get(v_x_838_, 1);
            crate::leanh::lean_inc_ref(v_b_859_);
            crate::leanh::lean_dec_ref_known(v_x_838_, 2);
            v___x_860_ = crate::leanh::lean_apply_2(v_h__3_841_, v_a_858_, v_b_859_);
            return v___x_860_;
        }
        6 => {
            let mut v_a_861_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_b_862_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_863_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__9_847_);
            crate::leanh::lean_dec(v_h__8_846_);
            crate::leanh::lean_dec(v_h__6_844_);
            crate::leanh::lean_dec(v_h__5_843_);
            crate::leanh::lean_dec(v_h__4_842_);
            crate::leanh::lean_dec(v_h__3_841_);
            crate::leanh::lean_dec(v_h__2_840_);
            crate::leanh::lean_dec(v_h__1_839_);
            v_a_861_ = crate::leanh::lean_ctor_get(v_x_838_, 0);
            crate::leanh::lean_inc_ref(v_a_861_);
            v_b_862_ = crate::leanh::lean_ctor_get(v_x_838_, 1);
            crate::leanh::lean_inc_ref(v_b_862_);
            crate::leanh::lean_dec_ref_known(v_x_838_, 2);
            v___x_863_ = crate::leanh::lean_apply_2(v_h__7_845_, v_a_861_, v_b_862_);
            return v___x_863_;
        }
        7 => {
            let mut v_a_864_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_b_865_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_866_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__9_847_);
            crate::leanh::lean_dec(v_h__8_846_);
            crate::leanh::lean_dec(v_h__7_845_);
            crate::leanh::lean_dec(v_h__6_844_);
            crate::leanh::lean_dec(v_h__5_843_);
            crate::leanh::lean_dec(v_h__3_841_);
            crate::leanh::lean_dec(v_h__2_840_);
            crate::leanh::lean_dec(v_h__1_839_);
            v_a_864_ = crate::leanh::lean_ctor_get(v_x_838_, 0);
            crate::leanh::lean_inc_ref(v_a_864_);
            v_b_865_ = crate::leanh::lean_ctor_get(v_x_838_, 1);
            crate::leanh::lean_inc_ref(v_b_865_);
            crate::leanh::lean_dec_ref_known(v_x_838_, 2);
            v___x_866_ = crate::leanh::lean_apply_2(v_h__4_842_, v_a_864_, v_b_865_);
            return v___x_866_;
        }
        _ => {
            let mut v_a_867_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_k_868_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_869_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__9_847_);
            crate::leanh::lean_dec(v_h__8_846_);
            crate::leanh::lean_dec(v_h__7_845_);
            crate::leanh::lean_dec(v_h__6_844_);
            crate::leanh::lean_dec(v_h__4_842_);
            crate::leanh::lean_dec(v_h__3_841_);
            crate::leanh::lean_dec(v_h__2_840_);
            crate::leanh::lean_dec(v_h__1_839_);
            v_a_867_ = crate::leanh::lean_ctor_get(v_x_838_, 0);
            crate::leanh::lean_inc_ref(v_a_867_);
            v_k_868_ = crate::leanh::lean_ctor_get(v_x_838_, 1);
            crate::leanh::lean_inc(v_k_868_);
            crate::leanh::lean_dec_ref_known(v_x_838_, 2);
            v___x_869_ = crate::leanh::lean_apply_2(v_h__5_843_, v_a_867_, v_k_868_);
            return v___x_869_;
        }
    }
}
pub unsafe fn l___private_Init_Grind_Ring_CommSemiringAdapter_0__Lean_Grind_CommRing_Expr_toPolyS_match__1_splitter___redArg(
    mut v_a_870_: *mut crate::leanh::LeanObject,
    mut v_h__1_871_: *mut crate::leanh::LeanObject,
    mut v_h__2_872_: *mut crate::leanh::LeanObject,
    mut v_h__3_873_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    match crate::leanh::lean_obj_tag(v_a_870_) {
        0 => {
            let mut v_k_874_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_875_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__3_873_);
            crate::leanh::lean_dec(v_h__2_872_);
            v_k_874_ = crate::leanh::lean_ctor_get(v_a_870_, 0);
            crate::leanh::lean_inc(v_k_874_);
            crate::leanh::lean_dec_ref_known(v_a_870_, 1);
            v___x_875_ = crate::leanh::lean_apply_1(v_h__1_871_, v_k_874_);
            return v___x_875_;
        }
        3 => {
            let mut v_i_876_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_877_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__3_873_);
            crate::leanh::lean_dec(v_h__1_871_);
            v_i_876_ = crate::leanh::lean_ctor_get(v_a_870_, 0);
            crate::leanh::lean_inc(v_i_876_);
            crate::leanh::lean_dec_ref_known(v_a_870_, 1);
            v___x_877_ = crate::leanh::lean_apply_1(v_h__2_872_, v_i_876_);
            return v___x_877_;
        }
        _ => {
            let mut v___x_878_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__2_872_);
            crate::leanh::lean_dec(v_h__1_871_);
            v___x_878_ = crate::leanh::lean_apply_3(
                v_h__3_873_,
                v_a_870_,
                crate::leanh::lean_box(0),
                crate::leanh::lean_box(0),
            );
            return v___x_878_;
        }
    }
}
pub unsafe fn l___private_Init_Grind_Ring_CommSemiringAdapter_0__Lean_Grind_CommRing_Expr_toPolyS_match__1_splitter(
    mut v_motive_879_: *mut crate::leanh::LeanObject,
    mut v_a_880_: *mut crate::leanh::LeanObject,
    mut v_h__1_881_: *mut crate::leanh::LeanObject,
    mut v_h__2_882_: *mut crate::leanh::LeanObject,
    mut v_h__3_883_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    match crate::leanh::lean_obj_tag(v_a_880_) {
        0 => {
            let mut v_k_884_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_885_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__3_883_);
            crate::leanh::lean_dec(v_h__2_882_);
            v_k_884_ = crate::leanh::lean_ctor_get(v_a_880_, 0);
            crate::leanh::lean_inc(v_k_884_);
            crate::leanh::lean_dec_ref_known(v_a_880_, 1);
            v___x_885_ = crate::leanh::lean_apply_1(v_h__1_881_, v_k_884_);
            return v___x_885_;
        }
        3 => {
            let mut v_i_886_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_887_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__3_883_);
            crate::leanh::lean_dec(v_h__1_881_);
            v_i_886_ = crate::leanh::lean_ctor_get(v_a_880_, 0);
            crate::leanh::lean_inc(v_i_886_);
            crate::leanh::lean_dec_ref_known(v_a_880_, 1);
            v___x_887_ = crate::leanh::lean_apply_1(v_h__2_882_, v_i_886_);
            return v___x_887_;
        }
        _ => {
            let mut v___x_888_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__2_882_);
            crate::leanh::lean_dec(v_h__1_881_);
            v___x_888_ = crate::leanh::lean_apply_3(
                v_h__3_883_,
                v_a_880_,
                crate::leanh::lean_box(0),
                crate::leanh::lean_box(0),
            );
            return v___x_888_;
        }
    }
}
pub unsafe fn l_Lean_Grind_CommRing_eq__normS__cert(
    mut v_lhs_889_: *mut crate::leanh::LeanObject,
    mut v_rhs_890_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_891_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_892_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_893_: u8 = 0;
    v___x_891_ = l_Lean_Grind_CommRing_Expr_toPolyS(v_lhs_889_);
    v___x_892_ = l_Lean_Grind_CommRing_Expr_toPolyS(v_rhs_890_);
    v___x_893_ = l_Lean_Grind_CommRing_instBEqPoly_beq(v___x_891_, v___x_892_);
    crate::leanh::lean_dec_ref(v___x_892_);
    crate::leanh::lean_dec_ref(v___x_891_);
    return v___x_893_;
}
pub unsafe fn l_Lean_Grind_CommRing_eq__normS__cert___boxed(
    mut v_lhs_894_: *mut crate::leanh::LeanObject,
    mut v_rhs_895_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_896_: u8 = 0;
    let mut v_r_897_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_896_ = l_Lean_Grind_CommRing_eq__normS__cert(v_lhs_894_, v_rhs_895_);
    v_r_897_ = crate::leanh::lean_box((v_res_896_) as usize);
    return v_r_897_;
}
pub unsafe fn l_Lean_Grind_CommRing_eq__normS__nc__cert(
    mut v_lhs_898_: *mut crate::leanh::LeanObject,
    mut v_rhs_899_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_900_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_901_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_902_: u8 = 0;
    v___x_900_ = l_Lean_Grind_CommRing_Expr_toPolyS__nc(v_lhs_898_);
    v___x_901_ = l_Lean_Grind_CommRing_Expr_toPolyS__nc(v_rhs_899_);
    v___x_902_ = l_Lean_Grind_CommRing_instBEqPoly_beq(v___x_900_, v___x_901_);
    crate::leanh::lean_dec_ref(v___x_901_);
    crate::leanh::lean_dec_ref(v___x_900_);
    return v___x_902_;
}
pub unsafe fn l_Lean_Grind_CommRing_eq__normS__nc__cert___boxed(
    mut v_lhs_903_: *mut crate::leanh::LeanObject,
    mut v_rhs_904_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_905_: u8 = 0;
    let mut v_r_906_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_905_ = l_Lean_Grind_CommRing_eq__normS__nc__cert(v_lhs_903_, v_rhs_904_);
    v_r_906_ = crate::leanh::lean_box((v_res_905_) as usize);
    return v_r_906_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Init_Grind_Ring_CommSemiringAdapter(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Init_Grind_Ring_Envelope(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Grind_Ring_CommSolver(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Int_LemmasAux(builtin);
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
pub unsafe fn meta_initialize_Init_Grind_Ring_CommSemiringAdapter(
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
pub unsafe fn initialize_Init_Grind_Ring_CommSemiringAdapter(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Init_Grind_Ring_Envelope(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Grind_Ring_CommSolver(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Int_LemmasAux(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Omega(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Grind_Ring_CommSemiringAdapter(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Init_Grind_Ring_CommSemiringAdapter(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Init_Grind_Ring_CommSemiringAdapter(builtin);
}
