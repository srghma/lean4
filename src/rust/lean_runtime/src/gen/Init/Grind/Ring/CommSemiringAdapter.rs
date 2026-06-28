// Lean compiler output
// Module: Init.Grind.Ring.CommSemiringAdapter
// Imports: Init.Grind.Ring.Envelope Init.Grind.Ring.CommSolver Init.Data.Int.LemmasAux Init.Omega
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
use crate::lean_imports_rs::Init::Data::Int::Basic::{
    lean_int_dec_lt, lean_nat_abs, lean_nat_to_int,
};
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_alloc_ctor, lean_apply_1, lean_apply_2, lean_apply_3,
    lean_box, lean_ctor_get, lean_ctor_set, lean_ctor_set_tag, lean_dec, lean_dec_ref,
    lean_dec_ref_known, lean_inc, lean_inc_ref, lean_inc_ref_n, lean_io_result_is_error,
    lean_io_result_mk_ok, lean_is_exclusive, lean_obj_once, lean_obj_tag, lean_unsigned_to_nat,
};
static mut l_Lean_Grind_CommRing_Expr_toPolyS___closed__0_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Grind_CommRing_Expr_toPolyS___closed__0: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_Grind_CommRing_Expr_toPolyS___closed__1_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Grind_CommRing_Expr_toPolyS___closed__1: *mut LeanObject = core::ptr::null_mut();
pub unsafe fn l_Lean_Grind_CommRing_Expr_denoteS___redArg(
    mut v_inst_454_: *mut LeanObject,
    mut v_ctx_455_: *mut LeanObject,
    mut v_x_456_: *mut LeanObject,
) -> *mut LeanObject {
    match lean_obj_tag(v_x_456_) {
        0 => {
            let mut v_ofNat_457_: *mut LeanObject = core::ptr::null_mut();
            let mut v_k_458_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_459_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_460_: *mut LeanObject = core::ptr::null_mut();
            v_ofNat_457_ = lean_ctor_get(v_inst_454_, 3);
            lean_inc(v_ofNat_457_);
            lean_dec_ref(v_inst_454_);
            v_k_458_ = lean_ctor_get(v_x_456_, 0);
            lean_inc(v_k_458_);
            lean_dec_ref_known(v_x_456_, 1);
            v___x_459_ = lean_nat_abs(v_k_458_);
            lean_dec(v_k_458_);
            v___x_460_ = lean_apply_1(v_ofNat_457_, v___x_459_);
            return v___x_460_;
        }
        1 => {
            let mut v_ofNat_461_: *mut LeanObject = core::ptr::null_mut();
            let mut v_k_462_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_463_: *mut LeanObject = core::ptr::null_mut();
            v_ofNat_461_ = lean_ctor_get(v_inst_454_, 3);
            lean_inc(v_ofNat_461_);
            lean_dec_ref(v_inst_454_);
            v_k_462_ = lean_ctor_get(v_x_456_, 0);
            lean_inc(v_k_462_);
            lean_dec_ref_known(v_x_456_, 1);
            v___x_463_ = lean_apply_1(v_ofNat_461_, v_k_462_);
            return v___x_463_;
        }
        3 => {
            let mut v_i_464_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_465_: *mut LeanObject = core::ptr::null_mut();
            lean_dec_ref(v_inst_454_);
            v_i_464_ = lean_ctor_get(v_x_456_, 0);
            lean_inc(v_i_464_);
            lean_dec_ref_known(v_x_456_, 1);
            v___x_465_ = l_Lean_RArray_getImpl___redArg(v_ctx_455_, v_i_464_);
            lean_dec(v_i_464_);
            return v___x_465_;
        }
        5 => {
            let mut v_toAdd_466_: *mut LeanObject = core::ptr::null_mut();
            let mut v_a_467_: *mut LeanObject = core::ptr::null_mut();
            let mut v_b_468_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_469_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_470_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_471_: *mut LeanObject = core::ptr::null_mut();
            v_toAdd_466_ = lean_ctor_get(v_inst_454_, 0);
            lean_inc(v_toAdd_466_);
            v_a_467_ = lean_ctor_get(v_x_456_, 0);
            lean_inc_ref(v_a_467_);
            v_b_468_ = lean_ctor_get(v_x_456_, 1);
            lean_inc_ref(v_b_468_);
            lean_dec_ref_known(v_x_456_, 2);
            lean_inc_ref(v_inst_454_);
            v___x_469_ =
                l_Lean_Grind_CommRing_Expr_denoteS___redArg(v_inst_454_, v_ctx_455_, v_a_467_);
            v___x_470_ =
                l_Lean_Grind_CommRing_Expr_denoteS___redArg(v_inst_454_, v_ctx_455_, v_b_468_);
            v___x_471_ = lean_apply_2(v_toAdd_466_, v___x_469_, v___x_470_);
            return v___x_471_;
        }
        7 => {
            let mut v_toMul_472_: *mut LeanObject = core::ptr::null_mut();
            let mut v_a_473_: *mut LeanObject = core::ptr::null_mut();
            let mut v_b_474_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_475_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_476_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_477_: *mut LeanObject = core::ptr::null_mut();
            v_toMul_472_ = lean_ctor_get(v_inst_454_, 1);
            lean_inc(v_toMul_472_);
            v_a_473_ = lean_ctor_get(v_x_456_, 0);
            lean_inc_ref(v_a_473_);
            v_b_474_ = lean_ctor_get(v_x_456_, 1);
            lean_inc_ref(v_b_474_);
            lean_dec_ref_known(v_x_456_, 2);
            lean_inc_ref(v_inst_454_);
            v___x_475_ =
                l_Lean_Grind_CommRing_Expr_denoteS___redArg(v_inst_454_, v_ctx_455_, v_a_473_);
            v___x_476_ =
                l_Lean_Grind_CommRing_Expr_denoteS___redArg(v_inst_454_, v_ctx_455_, v_b_474_);
            v___x_477_ = lean_apply_2(v_toMul_472_, v___x_475_, v___x_476_);
            return v___x_477_;
        }
        8 => {
            let mut v_npow_478_: *mut LeanObject = core::ptr::null_mut();
            let mut v_a_479_: *mut LeanObject = core::ptr::null_mut();
            let mut v_k_480_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_481_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_482_: *mut LeanObject = core::ptr::null_mut();
            v_npow_478_ = lean_ctor_get(v_inst_454_, 5);
            lean_inc(v_npow_478_);
            v_a_479_ = lean_ctor_get(v_x_456_, 0);
            lean_inc_ref(v_a_479_);
            v_k_480_ = lean_ctor_get(v_x_456_, 1);
            lean_inc(v_k_480_);
            lean_dec_ref_known(v_x_456_, 2);
            v___x_481_ =
                l_Lean_Grind_CommRing_Expr_denoteS___redArg(v_inst_454_, v_ctx_455_, v_a_479_);
            v___x_482_ = lean_apply_2(v_npow_478_, v___x_481_, v_k_480_);
            return v___x_482_;
        }
        _ => {
            let mut v_ofNat_483_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_484_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_485_: *mut LeanObject = core::ptr::null_mut();
            lean_dec_ref(v_x_456_);
            v_ofNat_483_ = lean_ctor_get(v_inst_454_, 3);
            lean_inc(v_ofNat_483_);
            lean_dec_ref(v_inst_454_);
            v___x_484_ = lean_unsigned_to_nat(0);
            v___x_485_ = lean_apply_1(v_ofNat_483_, v___x_484_);
            return v___x_485_;
        }
    }
}
pub unsafe fn l_Lean_Grind_CommRing_Expr_denoteS___redArg___boxed(
    mut v_inst_486_: *mut LeanObject,
    mut v_ctx_487_: *mut LeanObject,
    mut v_x_488_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_489_: *mut LeanObject = core::ptr::null_mut();
    v_res_489_ = l_Lean_Grind_CommRing_Expr_denoteS___redArg(v_inst_486_, v_ctx_487_, v_x_488_);
    lean_dec_ref(v_ctx_487_);
    return v_res_489_;
}
pub unsafe fn l_Lean_Grind_CommRing_Expr_denoteS(
    mut v_00_u03b1_490_: *mut LeanObject,
    mut v_inst_491_: *mut LeanObject,
    mut v_ctx_492_: *mut LeanObject,
    mut v_x_493_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_494_: *mut LeanObject = core::ptr::null_mut();
    v___x_494_ = l_Lean_Grind_CommRing_Expr_denoteS___redArg(v_inst_491_, v_ctx_492_, v_x_493_);
    return v___x_494_;
}
pub unsafe fn l_Lean_Grind_CommRing_Expr_denoteS___boxed(
    mut v_00_u03b1_495_: *mut LeanObject,
    mut v_inst_496_: *mut LeanObject,
    mut v_ctx_497_: *mut LeanObject,
    mut v_x_498_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_499_: *mut LeanObject = core::ptr::null_mut();
    v_res_499_ =
        l_Lean_Grind_CommRing_Expr_denoteS(v_00_u03b1_495_, v_inst_496_, v_ctx_497_, v_x_498_);
    lean_dec_ref(v_ctx_497_);
    return v_res_499_;
}
pub unsafe fn l_Lean_Grind_CommRing_Expr_denoteSAsRing___redArg(
    mut v_inst_500_: *mut LeanObject,
    mut v_ctx_501_: *mut LeanObject,
    mut v_x_502_: *mut LeanObject,
) -> *mut LeanObject {
    match lean_obj_tag(v_x_502_) {
        0 => {
            let mut v_k_503_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_504_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_505_: *mut LeanObject = core::ptr::null_mut();
            v_k_503_ = lean_ctor_get(v_x_502_, 0);
            lean_inc(v_k_503_);
            lean_dec_ref_known(v_x_502_, 1);
            v___x_504_ = lean_nat_abs(v_k_503_);
            lean_dec(v_k_503_);
            v___x_505_ = l_Lean_Grind_Ring_OfSemiring_natCast___redArg(v_inst_500_, v___x_504_);
            return v___x_505_;
        }
        1 => {
            let mut v_k_506_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_507_: *mut LeanObject = core::ptr::null_mut();
            v_k_506_ = lean_ctor_get(v_x_502_, 0);
            lean_inc(v_k_506_);
            lean_dec_ref_known(v_x_502_, 1);
            v___x_507_ = l_Lean_Grind_Ring_OfSemiring_natCast___redArg(v_inst_500_, v_k_506_);
            return v___x_507_;
        }
        3 => {
            let mut v_i_508_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_509_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_510_: *mut LeanObject = core::ptr::null_mut();
            v_i_508_ = lean_ctor_get(v_x_502_, 0);
            lean_inc(v_i_508_);
            lean_dec_ref_known(v_x_502_, 1);
            v___x_509_ = l_Lean_RArray_getImpl___redArg(v_ctx_501_, v_i_508_);
            lean_dec(v_i_508_);
            v___x_510_ = l_Lean_Grind_Ring_OfSemiring_toQ___redArg(v_inst_500_, v___x_509_);
            return v___x_510_;
        }
        5 => {
            let mut v_a_511_: *mut LeanObject = core::ptr::null_mut();
            let mut v_b_512_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_513_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_514_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_515_: *mut LeanObject = core::ptr::null_mut();
            v_a_511_ = lean_ctor_get(v_x_502_, 0);
            lean_inc_ref(v_a_511_);
            v_b_512_ = lean_ctor_get(v_x_502_, 1);
            lean_inc_ref(v_b_512_);
            lean_dec_ref_known(v_x_502_, 2);
            lean_inc_ref_n(v_inst_500_, 2);
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
            let mut v_a_516_: *mut LeanObject = core::ptr::null_mut();
            let mut v_b_517_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_518_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_519_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_520_: *mut LeanObject = core::ptr::null_mut();
            v_a_516_ = lean_ctor_get(v_x_502_, 0);
            lean_inc_ref(v_a_516_);
            v_b_517_ = lean_ctor_get(v_x_502_, 1);
            lean_inc_ref(v_b_517_);
            lean_dec_ref_known(v_x_502_, 2);
            lean_inc_ref_n(v_inst_500_, 2);
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
            let mut v_a_521_: *mut LeanObject = core::ptr::null_mut();
            let mut v_k_522_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_523_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_524_: *mut LeanObject = core::ptr::null_mut();
            v_a_521_ = lean_ctor_get(v_x_502_, 0);
            lean_inc_ref(v_a_521_);
            v_k_522_ = lean_ctor_get(v_x_502_, 1);
            lean_inc(v_k_522_);
            lean_dec_ref_known(v_x_502_, 2);
            lean_inc_ref(v_inst_500_);
            v___x_523_ = l_Lean_Grind_CommRing_Expr_denoteSAsRing___redArg(
                v_inst_500_,
                v_ctx_501_,
                v_a_521_,
            );
            v___x_524_ =
                l_Lean_Grind_Ring_OfSemiring_npow___redArg(v_inst_500_, v___x_523_, v_k_522_);
            lean_dec(v_k_522_);
            return v___x_524_;
        }
        _ => {
            let mut v___x_525_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_526_: *mut LeanObject = core::ptr::null_mut();
            lean_dec_ref(v_x_502_);
            v___x_525_ = lean_unsigned_to_nat(0);
            v___x_526_ = l_Lean_Grind_Ring_OfSemiring_natCast___redArg(v_inst_500_, v___x_525_);
            return v___x_526_;
        }
    }
}
pub unsafe fn l_Lean_Grind_CommRing_Expr_denoteSAsRing___redArg___boxed(
    mut v_inst_527_: *mut LeanObject,
    mut v_ctx_528_: *mut LeanObject,
    mut v_x_529_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_530_: *mut LeanObject = core::ptr::null_mut();
    v_res_530_ =
        l_Lean_Grind_CommRing_Expr_denoteSAsRing___redArg(v_inst_527_, v_ctx_528_, v_x_529_);
    lean_dec_ref(v_ctx_528_);
    return v_res_530_;
}
pub unsafe fn l_Lean_Grind_CommRing_Expr_denoteSAsRing(
    mut v_00_u03b1_531_: *mut LeanObject,
    mut v_inst_532_: *mut LeanObject,
    mut v_ctx_533_: *mut LeanObject,
    mut v_x_534_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_535_: *mut LeanObject = core::ptr::null_mut();
    v___x_535_ =
        l_Lean_Grind_CommRing_Expr_denoteSAsRing___redArg(v_inst_532_, v_ctx_533_, v_x_534_);
    return v___x_535_;
}
pub unsafe fn l_Lean_Grind_CommRing_Expr_denoteSAsRing___boxed(
    mut v_00_u03b1_536_: *mut LeanObject,
    mut v_inst_537_: *mut LeanObject,
    mut v_ctx_538_: *mut LeanObject,
    mut v_x_539_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_540_: *mut LeanObject = core::ptr::null_mut();
    v_res_540_ = l_Lean_Grind_CommRing_Expr_denoteSAsRing(
        v_00_u03b1_536_,
        v_inst_537_,
        v_ctx_538_,
        v_x_539_,
    );
    lean_dec_ref(v_ctx_538_);
    return v_res_540_;
}
pub unsafe fn l___private_Init_Grind_Ring_CommSemiringAdapter_0__Lean_Grind_CommRing_Expr_denoteS_match__1_splitter___redArg(
    mut v_x_541_: *mut LeanObject,
    mut v_h__1_542_: *mut LeanObject,
    mut v_h__2_543_: *mut LeanObject,
    mut v_h__3_544_: *mut LeanObject,
    mut v_h__4_545_: *mut LeanObject,
    mut v_h__5_546_: *mut LeanObject,
    mut v_h__6_547_: *mut LeanObject,
    mut v_h__7_548_: *mut LeanObject,
    mut v_h__8_549_: *mut LeanObject,
    mut v_h__9_550_: *mut LeanObject,
) -> *mut LeanObject {
    match lean_obj_tag(v_x_541_) {
        0 => {
            let mut v_k_551_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_552_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__9_550_);
            lean_dec(v_h__8_549_);
            lean_dec(v_h__7_548_);
            lean_dec(v_h__6_547_);
            lean_dec(v_h__5_546_);
            lean_dec(v_h__4_545_);
            lean_dec(v_h__3_544_);
            lean_dec(v_h__2_543_);
            v_k_551_ = lean_ctor_get(v_x_541_, 0);
            lean_inc(v_k_551_);
            lean_dec_ref_known(v_x_541_, 1);
            v___x_552_ = lean_apply_1(v_h__1_542_, v_k_551_);
            return v___x_552_;
        }
        1 => {
            let mut v_k_553_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_554_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__9_550_);
            lean_dec(v_h__8_549_);
            lean_dec(v_h__7_548_);
            lean_dec(v_h__6_547_);
            lean_dec(v_h__5_546_);
            lean_dec(v_h__4_545_);
            lean_dec(v_h__3_544_);
            lean_dec(v_h__1_542_);
            v_k_553_ = lean_ctor_get(v_x_541_, 0);
            lean_inc(v_k_553_);
            lean_dec_ref_known(v_x_541_, 1);
            v___x_554_ = lean_apply_1(v_h__2_543_, v_k_553_);
            return v___x_554_;
        }
        2 => {
            let mut v_k_555_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_556_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__8_549_);
            lean_dec(v_h__7_548_);
            lean_dec(v_h__6_547_);
            lean_dec(v_h__5_546_);
            lean_dec(v_h__4_545_);
            lean_dec(v_h__3_544_);
            lean_dec(v_h__2_543_);
            lean_dec(v_h__1_542_);
            v_k_555_ = lean_ctor_get(v_x_541_, 0);
            lean_inc(v_k_555_);
            lean_dec_ref_known(v_x_541_, 1);
            v___x_556_ = lean_apply_1(v_h__9_550_, v_k_555_);
            return v___x_556_;
        }
        3 => {
            let mut v_i_557_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_558_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__9_550_);
            lean_dec(v_h__8_549_);
            lean_dec(v_h__7_548_);
            lean_dec(v_h__6_547_);
            lean_dec(v_h__5_546_);
            lean_dec(v_h__4_545_);
            lean_dec(v_h__2_543_);
            lean_dec(v_h__1_542_);
            v_i_557_ = lean_ctor_get(v_x_541_, 0);
            lean_inc(v_i_557_);
            lean_dec_ref_known(v_x_541_, 1);
            v___x_558_ = lean_apply_1(v_h__3_544_, v_i_557_);
            return v___x_558_;
        }
        4 => {
            let mut v_a_559_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_560_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__9_550_);
            lean_dec(v_h__7_548_);
            lean_dec(v_h__6_547_);
            lean_dec(v_h__5_546_);
            lean_dec(v_h__4_545_);
            lean_dec(v_h__3_544_);
            lean_dec(v_h__2_543_);
            lean_dec(v_h__1_542_);
            v_a_559_ = lean_ctor_get(v_x_541_, 0);
            lean_inc_ref(v_a_559_);
            lean_dec_ref_known(v_x_541_, 1);
            v___x_560_ = lean_apply_1(v_h__8_549_, v_a_559_);
            return v___x_560_;
        }
        5 => {
            let mut v_a_561_: *mut LeanObject = core::ptr::null_mut();
            let mut v_b_562_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_563_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__9_550_);
            lean_dec(v_h__8_549_);
            lean_dec(v_h__7_548_);
            lean_dec(v_h__6_547_);
            lean_dec(v_h__5_546_);
            lean_dec(v_h__3_544_);
            lean_dec(v_h__2_543_);
            lean_dec(v_h__1_542_);
            v_a_561_ = lean_ctor_get(v_x_541_, 0);
            lean_inc_ref(v_a_561_);
            v_b_562_ = lean_ctor_get(v_x_541_, 1);
            lean_inc_ref(v_b_562_);
            lean_dec_ref_known(v_x_541_, 2);
            v___x_563_ = lean_apply_2(v_h__4_545_, v_a_561_, v_b_562_);
            return v___x_563_;
        }
        6 => {
            let mut v_a_564_: *mut LeanObject = core::ptr::null_mut();
            let mut v_b_565_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_566_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__9_550_);
            lean_dec(v_h__8_549_);
            lean_dec(v_h__6_547_);
            lean_dec(v_h__5_546_);
            lean_dec(v_h__4_545_);
            lean_dec(v_h__3_544_);
            lean_dec(v_h__2_543_);
            lean_dec(v_h__1_542_);
            v_a_564_ = lean_ctor_get(v_x_541_, 0);
            lean_inc_ref(v_a_564_);
            v_b_565_ = lean_ctor_get(v_x_541_, 1);
            lean_inc_ref(v_b_565_);
            lean_dec_ref_known(v_x_541_, 2);
            v___x_566_ = lean_apply_2(v_h__7_548_, v_a_564_, v_b_565_);
            return v___x_566_;
        }
        7 => {
            let mut v_a_567_: *mut LeanObject = core::ptr::null_mut();
            let mut v_b_568_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_569_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__9_550_);
            lean_dec(v_h__8_549_);
            lean_dec(v_h__7_548_);
            lean_dec(v_h__6_547_);
            lean_dec(v_h__4_545_);
            lean_dec(v_h__3_544_);
            lean_dec(v_h__2_543_);
            lean_dec(v_h__1_542_);
            v_a_567_ = lean_ctor_get(v_x_541_, 0);
            lean_inc_ref(v_a_567_);
            v_b_568_ = lean_ctor_get(v_x_541_, 1);
            lean_inc_ref(v_b_568_);
            lean_dec_ref_known(v_x_541_, 2);
            v___x_569_ = lean_apply_2(v_h__5_546_, v_a_567_, v_b_568_);
            return v___x_569_;
        }
        _ => {
            let mut v_a_570_: *mut LeanObject = core::ptr::null_mut();
            let mut v_k_571_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_572_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__9_550_);
            lean_dec(v_h__8_549_);
            lean_dec(v_h__7_548_);
            lean_dec(v_h__5_546_);
            lean_dec(v_h__4_545_);
            lean_dec(v_h__3_544_);
            lean_dec(v_h__2_543_);
            lean_dec(v_h__1_542_);
            v_a_570_ = lean_ctor_get(v_x_541_, 0);
            lean_inc_ref(v_a_570_);
            v_k_571_ = lean_ctor_get(v_x_541_, 1);
            lean_inc(v_k_571_);
            lean_dec_ref_known(v_x_541_, 2);
            v___x_572_ = lean_apply_2(v_h__6_547_, v_a_570_, v_k_571_);
            return v___x_572_;
        }
    }
}
pub unsafe fn l___private_Init_Grind_Ring_CommSemiringAdapter_0__Lean_Grind_CommRing_Expr_denoteS_match__1_splitter(
    mut v_motive_573_: *mut LeanObject,
    mut v_x_574_: *mut LeanObject,
    mut v_h__1_575_: *mut LeanObject,
    mut v_h__2_576_: *mut LeanObject,
    mut v_h__3_577_: *mut LeanObject,
    mut v_h__4_578_: *mut LeanObject,
    mut v_h__5_579_: *mut LeanObject,
    mut v_h__6_580_: *mut LeanObject,
    mut v_h__7_581_: *mut LeanObject,
    mut v_h__8_582_: *mut LeanObject,
    mut v_h__9_583_: *mut LeanObject,
) -> *mut LeanObject {
    match lean_obj_tag(v_x_574_) {
        0 => {
            let mut v_k_584_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_585_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__9_583_);
            lean_dec(v_h__8_582_);
            lean_dec(v_h__7_581_);
            lean_dec(v_h__6_580_);
            lean_dec(v_h__5_579_);
            lean_dec(v_h__4_578_);
            lean_dec(v_h__3_577_);
            lean_dec(v_h__2_576_);
            v_k_584_ = lean_ctor_get(v_x_574_, 0);
            lean_inc(v_k_584_);
            lean_dec_ref_known(v_x_574_, 1);
            v___x_585_ = lean_apply_1(v_h__1_575_, v_k_584_);
            return v___x_585_;
        }
        1 => {
            let mut v_k_586_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_587_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__9_583_);
            lean_dec(v_h__8_582_);
            lean_dec(v_h__7_581_);
            lean_dec(v_h__6_580_);
            lean_dec(v_h__5_579_);
            lean_dec(v_h__4_578_);
            lean_dec(v_h__3_577_);
            lean_dec(v_h__1_575_);
            v_k_586_ = lean_ctor_get(v_x_574_, 0);
            lean_inc(v_k_586_);
            lean_dec_ref_known(v_x_574_, 1);
            v___x_587_ = lean_apply_1(v_h__2_576_, v_k_586_);
            return v___x_587_;
        }
        2 => {
            let mut v_k_588_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_589_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__8_582_);
            lean_dec(v_h__7_581_);
            lean_dec(v_h__6_580_);
            lean_dec(v_h__5_579_);
            lean_dec(v_h__4_578_);
            lean_dec(v_h__3_577_);
            lean_dec(v_h__2_576_);
            lean_dec(v_h__1_575_);
            v_k_588_ = lean_ctor_get(v_x_574_, 0);
            lean_inc(v_k_588_);
            lean_dec_ref_known(v_x_574_, 1);
            v___x_589_ = lean_apply_1(v_h__9_583_, v_k_588_);
            return v___x_589_;
        }
        3 => {
            let mut v_i_590_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_591_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__9_583_);
            lean_dec(v_h__8_582_);
            lean_dec(v_h__7_581_);
            lean_dec(v_h__6_580_);
            lean_dec(v_h__5_579_);
            lean_dec(v_h__4_578_);
            lean_dec(v_h__2_576_);
            lean_dec(v_h__1_575_);
            v_i_590_ = lean_ctor_get(v_x_574_, 0);
            lean_inc(v_i_590_);
            lean_dec_ref_known(v_x_574_, 1);
            v___x_591_ = lean_apply_1(v_h__3_577_, v_i_590_);
            return v___x_591_;
        }
        4 => {
            let mut v_a_592_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_593_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__9_583_);
            lean_dec(v_h__7_581_);
            lean_dec(v_h__6_580_);
            lean_dec(v_h__5_579_);
            lean_dec(v_h__4_578_);
            lean_dec(v_h__3_577_);
            lean_dec(v_h__2_576_);
            lean_dec(v_h__1_575_);
            v_a_592_ = lean_ctor_get(v_x_574_, 0);
            lean_inc_ref(v_a_592_);
            lean_dec_ref_known(v_x_574_, 1);
            v___x_593_ = lean_apply_1(v_h__8_582_, v_a_592_);
            return v___x_593_;
        }
        5 => {
            let mut v_a_594_: *mut LeanObject = core::ptr::null_mut();
            let mut v_b_595_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_596_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__9_583_);
            lean_dec(v_h__8_582_);
            lean_dec(v_h__7_581_);
            lean_dec(v_h__6_580_);
            lean_dec(v_h__5_579_);
            lean_dec(v_h__3_577_);
            lean_dec(v_h__2_576_);
            lean_dec(v_h__1_575_);
            v_a_594_ = lean_ctor_get(v_x_574_, 0);
            lean_inc_ref(v_a_594_);
            v_b_595_ = lean_ctor_get(v_x_574_, 1);
            lean_inc_ref(v_b_595_);
            lean_dec_ref_known(v_x_574_, 2);
            v___x_596_ = lean_apply_2(v_h__4_578_, v_a_594_, v_b_595_);
            return v___x_596_;
        }
        6 => {
            let mut v_a_597_: *mut LeanObject = core::ptr::null_mut();
            let mut v_b_598_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_599_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__9_583_);
            lean_dec(v_h__8_582_);
            lean_dec(v_h__6_580_);
            lean_dec(v_h__5_579_);
            lean_dec(v_h__4_578_);
            lean_dec(v_h__3_577_);
            lean_dec(v_h__2_576_);
            lean_dec(v_h__1_575_);
            v_a_597_ = lean_ctor_get(v_x_574_, 0);
            lean_inc_ref(v_a_597_);
            v_b_598_ = lean_ctor_get(v_x_574_, 1);
            lean_inc_ref(v_b_598_);
            lean_dec_ref_known(v_x_574_, 2);
            v___x_599_ = lean_apply_2(v_h__7_581_, v_a_597_, v_b_598_);
            return v___x_599_;
        }
        7 => {
            let mut v_a_600_: *mut LeanObject = core::ptr::null_mut();
            let mut v_b_601_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_602_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__9_583_);
            lean_dec(v_h__8_582_);
            lean_dec(v_h__7_581_);
            lean_dec(v_h__6_580_);
            lean_dec(v_h__4_578_);
            lean_dec(v_h__3_577_);
            lean_dec(v_h__2_576_);
            lean_dec(v_h__1_575_);
            v_a_600_ = lean_ctor_get(v_x_574_, 0);
            lean_inc_ref(v_a_600_);
            v_b_601_ = lean_ctor_get(v_x_574_, 1);
            lean_inc_ref(v_b_601_);
            lean_dec_ref_known(v_x_574_, 2);
            v___x_602_ = lean_apply_2(v_h__5_579_, v_a_600_, v_b_601_);
            return v___x_602_;
        }
        _ => {
            let mut v_a_603_: *mut LeanObject = core::ptr::null_mut();
            let mut v_k_604_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_605_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__9_583_);
            lean_dec(v_h__8_582_);
            lean_dec(v_h__7_581_);
            lean_dec(v_h__5_579_);
            lean_dec(v_h__4_578_);
            lean_dec(v_h__3_577_);
            lean_dec(v_h__2_576_);
            lean_dec(v_h__1_575_);
            v_a_603_ = lean_ctor_get(v_x_574_, 0);
            lean_inc_ref(v_a_603_);
            v_k_604_ = lean_ctor_get(v_x_574_, 1);
            lean_inc(v_k_604_);
            lean_dec_ref_known(v_x_574_, 2);
            v___x_605_ = lean_apply_2(v_h__6_580_, v_a_603_, v_k_604_);
            return v___x_605_;
        }
    }
}
pub unsafe fn l_Nat_cast___at___00Lean_Grind_CommRing_Expr_toPolyS_spec__0(
    mut v_a_606_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_607_: *mut LeanObject = core::ptr::null_mut();
    v___x_607_ = lean_nat_to_int(v_a_606_);
    return v___x_607_;
}
pub unsafe fn _init_l_Lean_Grind_CommRing_Expr_toPolyS___closed__0() -> *mut LeanObject {
    let mut v___x_608_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_609_: *mut LeanObject = core::ptr::null_mut();
    v___x_608_ = lean_unsigned_to_nat(0);
    v___x_609_ = lean_nat_to_int(v___x_608_);
    return v___x_609_;
}
pub unsafe fn _init_l_Lean_Grind_CommRing_Expr_toPolyS___closed__1() -> *mut LeanObject {
    let mut v___x_610_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_611_: *mut LeanObject = core::ptr::null_mut();
    v___x_610_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Grind_CommRing_Expr_toPolyS___closed__0),
        core::ptr::addr_of_mut!(l_Lean_Grind_CommRing_Expr_toPolyS___closed__0_once),
        _init_l_Lean_Grind_CommRing_Expr_toPolyS___closed__0,
    );
    v___x_611_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_611_, 0, v___x_610_);
    return v___x_611_;
}
pub unsafe fn l_Lean_Grind_CommRing_Expr_toPolyS(mut v_x_612_: *mut LeanObject) -> *mut LeanObject {
    let mut v_k_613_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_615_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_616_: u8 = 0;
    let mut v___x_617_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_618_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_620_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_621_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_622_: u8 = 0;
    let mut v_k_623_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_625_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_626_: u8 = 0;
    let mut v___x_627_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_629_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_630_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_631_: u8 = 0;
    let mut v_i_632_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_633_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_634_: *mut LeanObject = core::ptr::null_mut();
    let mut v_b_635_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_636_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_637_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_638_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_639_: *mut LeanObject = core::ptr::null_mut();
    let mut v_b_640_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_641_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_642_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_643_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_644_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_645_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_646_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_648_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_649_: u8 = 0;
    let mut v___x_650_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_651_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_652_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_654_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_655_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_656_: u8 = 0;
    let mut v_k_657_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_659_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_660_: u8 = 0;
    let mut v_i_661_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_663_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_664_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_665_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_666_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_667_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_668_: u8 = 0;
    let mut v_unused_669_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_670_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_671_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_672_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_673_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => match lean_obj_tag(v_x_612_) {
                0 => {
                    v_k_613_ = lean_ctor_get(v_x_612_, 0);
                    v_isSharedCheck_622_ = (!lean_is_exclusive(v_x_612_)) as u8;
                    if v_isSharedCheck_622_ == 0 {
                        v___x_615_ = v_x_612_;
                        v_isShared_616_ = v_isSharedCheck_622_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_k_613_);
                        lean_dec(v_x_612_);
                        v___x_615_ = lean_box(0);
                        v_isShared_616_ = v_isSharedCheck_622_;
                        state = 1;
                        continue;
                    }
                }
                1 => {
                    v_k_623_ = lean_ctor_get(v_x_612_, 0);
                    v_isSharedCheck_631_ = (!lean_is_exclusive(v_x_612_)) as u8;
                    if v_isSharedCheck_631_ == 0 {
                        v___x_625_ = v_x_612_;
                        v_isShared_626_ = v_isSharedCheck_631_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_k_623_);
                        lean_dec(v_x_612_);
                        v___x_625_ = lean_box(0);
                        v_isShared_626_ = v_isSharedCheck_631_;
                        state = 3;
                        continue;
                    }
                }
                3 => {
                    v_i_632_ = lean_ctor_get(v_x_612_, 0);
                    lean_inc(v_i_632_);
                    lean_dec_ref_known(v_x_612_, 1);
                    v___x_633_ = l_Lean_Grind_CommRing_Poly_ofVar(v_i_632_);
                    return v___x_633_;
                }
                5 => {
                    v_a_634_ = lean_ctor_get(v_x_612_, 0);
                    lean_inc_ref(v_a_634_);
                    v_b_635_ = lean_ctor_get(v_x_612_, 1);
                    lean_inc_ref(v_b_635_);
                    lean_dec_ref_known(v_x_612_, 2);
                    v___x_636_ = l_Lean_Grind_CommRing_Expr_toPolyS(v_a_634_);
                    v___x_637_ = l_Lean_Grind_CommRing_Expr_toPolyS(v_b_635_);
                    v___x_638_ = l_Lean_Grind_CommRing_Poly_combine(v___x_636_, v___x_637_);
                    return v___x_638_;
                }
                7 => {
                    v_a_639_ = lean_ctor_get(v_x_612_, 0);
                    lean_inc_ref(v_a_639_);
                    v_b_640_ = lean_ctor_get(v_x_612_, 1);
                    lean_inc_ref(v_b_640_);
                    lean_dec_ref_known(v_x_612_, 2);
                    v___x_641_ = l_Lean_Grind_CommRing_Expr_toPolyS(v_a_639_);
                    v___x_642_ = l_Lean_Grind_CommRing_Expr_toPolyS(v_b_640_);
                    v___x_643_ = l_Lean_Grind_CommRing_Poly_mul(v___x_641_, v___x_642_);
                    return v___x_643_;
                }
                8 => {
                    v_a_644_ = lean_ctor_get(v_x_612_, 0);
                    lean_inc_ref(v_a_644_);
                    match lean_obj_tag(v_a_644_) {
                        0 => {
                            v_k_645_ = lean_ctor_get(v_x_612_, 1);
                            lean_inc(v_k_645_);
                            lean_dec_ref_known(v_x_612_, 2);
                            v_k_646_ = lean_ctor_get(v_a_644_, 0);
                            v_isSharedCheck_656_ = (!lean_is_exclusive(v_a_644_)) as u8;
                            if v_isSharedCheck_656_ == 0 {
                                v___x_648_ = v_a_644_;
                                v_isShared_649_ = v_isSharedCheck_656_;
                                state = 5;
                                continue;
                            } else {
                                lean_inc(v_k_646_);
                                lean_dec(v_a_644_);
                                v___x_648_ = lean_box(0);
                                v_isShared_649_ = v_isSharedCheck_656_;
                                state = 5;
                                continue;
                            }
                        }
                        3 => {
                            v_k_657_ = lean_ctor_get(v_x_612_, 1);
                            v_isSharedCheck_668_ = (!lean_is_exclusive(v_x_612_)) as u8;
                            if v_isSharedCheck_668_ == 0 {
                                v_unused_669_ = lean_ctor_get(v_x_612_, 0);
                                lean_dec(v_unused_669_);
                                v___x_659_ = v_x_612_;
                                v_isShared_660_ = v_isSharedCheck_668_;
                                state = 7;
                                continue;
                            } else {
                                lean_inc(v_k_657_);
                                lean_dec(v_x_612_);
                                v___x_659_ = lean_box(0);
                                v_isShared_660_ = v_isSharedCheck_668_;
                                state = 7;
                                continue;
                            }
                        }
                        _ => {
                            v_k_670_ = lean_ctor_get(v_x_612_, 1);
                            lean_inc(v_k_670_);
                            lean_dec_ref_known(v_x_612_, 2);
                            v___x_671_ = l_Lean_Grind_CommRing_Expr_toPolyS(v_a_644_);
                            v___x_672_ = l_Lean_Grind_CommRing_Poly_pow(v___x_671_, v_k_670_);
                            lean_dec(v_k_670_);
                            return v___x_672_;
                        }
                    }
                }
                _ => {
                    lean_dec_ref(v_x_612_);
                    v___x_673_ = lean_obj_once(
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
                lean_dec(v_k_613_);
                v___x_618_ = lean_nat_to_int(v___x_617_);
                if v_isShared_616_ == 0 {
                    lean_ctor_set(v___x_615_, 0, v___x_618_);
                    v___x_620_ = v___x_615_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_621_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_621_, 0, v___x_618_);
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
                    lean_ctor_set_tag(v___x_625_, 0);
                    lean_ctor_set(v___x_625_, 0, v___x_627_);
                    v___x_629_ = v___x_625_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_630_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_630_, 0, v___x_627_);
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
                lean_dec(v_k_646_);
                v___x_651_ = lean_nat_to_int(v___x_650_);
                v___x_652_ = l_Int_pow(v___x_651_, v_k_645_);
                lean_dec(v_k_645_);
                lean_dec(v___x_651_);
                if v_isShared_649_ == 0 {
                    lean_ctor_set(v___x_648_, 0, v___x_652_);
                    v___x_654_ = v___x_648_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_655_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_655_, 0, v___x_652_);
                    v___x_654_ = v_reuseFailAlloc_655_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_654_;
            }
            7 => {
                v_i_661_ = lean_ctor_get(v_a_644_, 0);
                lean_inc(v_i_661_);
                lean_dec_ref_known(v_a_644_, 1);
                if v_isShared_660_ == 0 {
                    lean_ctor_set_tag(v___x_659_, 0);
                    lean_ctor_set(v___x_659_, 0, v_i_661_);
                    v___x_663_ = v___x_659_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_667_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_667_, 0, v_i_661_);
                    lean_ctor_set(v_reuseFailAlloc_667_, 1, v_k_657_);
                    v___x_663_ = v_reuseFailAlloc_667_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                v___x_664_ = lean_box(0);
                v___x_665_ = lean_alloc_ctor(1, 2, (0) as u32);
                lean_ctor_set(v___x_665_, 0, v___x_663_);
                lean_ctor_set(v___x_665_, 1, v___x_664_);
                v___x_666_ = l_Lean_Grind_CommRing_Poly_ofMon(v___x_665_);
                return v___x_666_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Grind_CommRing_Expr_toPolyS__nc(
    mut v_x_674_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_k_675_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_677_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_678_: u8 = 0;
    let mut v___x_679_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_680_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_682_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_683_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_684_: u8 = 0;
    let mut v_k_685_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_687_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_688_: u8 = 0;
    let mut v___x_689_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_691_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_692_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_693_: u8 = 0;
    let mut v_i_694_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_695_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_696_: *mut LeanObject = core::ptr::null_mut();
    let mut v_b_697_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_698_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_699_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_700_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_701_: *mut LeanObject = core::ptr::null_mut();
    let mut v_b_702_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_703_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_704_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_705_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_706_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_707_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_708_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_710_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_711_: u8 = 0;
    let mut v___x_712_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_713_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_714_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_716_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_717_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_718_: u8 = 0;
    let mut v_k_719_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_721_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_722_: u8 = 0;
    let mut v_i_723_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_725_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_726_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_727_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_728_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_729_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_730_: u8 = 0;
    let mut v_unused_731_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_732_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_733_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_734_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_735_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => match lean_obj_tag(v_x_674_) {
                0 => {
                    v_k_675_ = lean_ctor_get(v_x_674_, 0);
                    v_isSharedCheck_684_ = (!lean_is_exclusive(v_x_674_)) as u8;
                    if v_isSharedCheck_684_ == 0 {
                        v___x_677_ = v_x_674_;
                        v_isShared_678_ = v_isSharedCheck_684_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_k_675_);
                        lean_dec(v_x_674_);
                        v___x_677_ = lean_box(0);
                        v_isShared_678_ = v_isSharedCheck_684_;
                        state = 1;
                        continue;
                    }
                }
                1 => {
                    v_k_685_ = lean_ctor_get(v_x_674_, 0);
                    v_isSharedCheck_693_ = (!lean_is_exclusive(v_x_674_)) as u8;
                    if v_isSharedCheck_693_ == 0 {
                        v___x_687_ = v_x_674_;
                        v_isShared_688_ = v_isSharedCheck_693_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_k_685_);
                        lean_dec(v_x_674_);
                        v___x_687_ = lean_box(0);
                        v_isShared_688_ = v_isSharedCheck_693_;
                        state = 3;
                        continue;
                    }
                }
                3 => {
                    v_i_694_ = lean_ctor_get(v_x_674_, 0);
                    lean_inc(v_i_694_);
                    lean_dec_ref_known(v_x_674_, 1);
                    v___x_695_ = l_Lean_Grind_CommRing_Poly_ofVar(v_i_694_);
                    return v___x_695_;
                }
                5 => {
                    v_a_696_ = lean_ctor_get(v_x_674_, 0);
                    lean_inc_ref(v_a_696_);
                    v_b_697_ = lean_ctor_get(v_x_674_, 1);
                    lean_inc_ref(v_b_697_);
                    lean_dec_ref_known(v_x_674_, 2);
                    v___x_698_ = l_Lean_Grind_CommRing_Expr_toPolyS__nc(v_a_696_);
                    v___x_699_ = l_Lean_Grind_CommRing_Expr_toPolyS__nc(v_b_697_);
                    v___x_700_ = l_Lean_Grind_CommRing_Poly_combine(v___x_698_, v___x_699_);
                    return v___x_700_;
                }
                7 => {
                    v_a_701_ = lean_ctor_get(v_x_674_, 0);
                    lean_inc_ref(v_a_701_);
                    v_b_702_ = lean_ctor_get(v_x_674_, 1);
                    lean_inc_ref(v_b_702_);
                    lean_dec_ref_known(v_x_674_, 2);
                    v___x_703_ = l_Lean_Grind_CommRing_Expr_toPolyS__nc(v_a_701_);
                    v___x_704_ = l_Lean_Grind_CommRing_Expr_toPolyS__nc(v_b_702_);
                    v___x_705_ = l_Lean_Grind_CommRing_Poly_mul__nc(v___x_703_, v___x_704_);
                    return v___x_705_;
                }
                8 => {
                    v_a_706_ = lean_ctor_get(v_x_674_, 0);
                    lean_inc_ref(v_a_706_);
                    match lean_obj_tag(v_a_706_) {
                        0 => {
                            v_k_707_ = lean_ctor_get(v_x_674_, 1);
                            lean_inc(v_k_707_);
                            lean_dec_ref_known(v_x_674_, 2);
                            v_k_708_ = lean_ctor_get(v_a_706_, 0);
                            v_isSharedCheck_718_ = (!lean_is_exclusive(v_a_706_)) as u8;
                            if v_isSharedCheck_718_ == 0 {
                                v___x_710_ = v_a_706_;
                                v_isShared_711_ = v_isSharedCheck_718_;
                                state = 5;
                                continue;
                            } else {
                                lean_inc(v_k_708_);
                                lean_dec(v_a_706_);
                                v___x_710_ = lean_box(0);
                                v_isShared_711_ = v_isSharedCheck_718_;
                                state = 5;
                                continue;
                            }
                        }
                        3 => {
                            v_k_719_ = lean_ctor_get(v_x_674_, 1);
                            v_isSharedCheck_730_ = (!lean_is_exclusive(v_x_674_)) as u8;
                            if v_isSharedCheck_730_ == 0 {
                                v_unused_731_ = lean_ctor_get(v_x_674_, 0);
                                lean_dec(v_unused_731_);
                                v___x_721_ = v_x_674_;
                                v_isShared_722_ = v_isSharedCheck_730_;
                                state = 7;
                                continue;
                            } else {
                                lean_inc(v_k_719_);
                                lean_dec(v_x_674_);
                                v___x_721_ = lean_box(0);
                                v_isShared_722_ = v_isSharedCheck_730_;
                                state = 7;
                                continue;
                            }
                        }
                        _ => {
                            v_k_732_ = lean_ctor_get(v_x_674_, 1);
                            lean_inc(v_k_732_);
                            lean_dec_ref_known(v_x_674_, 2);
                            v___x_733_ = l_Lean_Grind_CommRing_Expr_toPolyS__nc(v_a_706_);
                            v___x_734_ = l_Lean_Grind_CommRing_Poly_pow__nc(v___x_733_, v_k_732_);
                            lean_dec(v_k_732_);
                            return v___x_734_;
                        }
                    }
                }
                _ => {
                    lean_dec_ref(v_x_674_);
                    v___x_735_ = lean_obj_once(
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
                lean_dec(v_k_675_);
                v___x_680_ = lean_nat_to_int(v___x_679_);
                if v_isShared_678_ == 0 {
                    lean_ctor_set(v___x_677_, 0, v___x_680_);
                    v___x_682_ = v___x_677_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_683_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_683_, 0, v___x_680_);
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
                    lean_ctor_set_tag(v___x_687_, 0);
                    lean_ctor_set(v___x_687_, 0, v___x_689_);
                    v___x_691_ = v___x_687_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_692_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_692_, 0, v___x_689_);
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
                lean_dec(v_k_708_);
                v___x_713_ = lean_nat_to_int(v___x_712_);
                v___x_714_ = l_Int_pow(v___x_713_, v_k_707_);
                lean_dec(v_k_707_);
                lean_dec(v___x_713_);
                if v_isShared_711_ == 0 {
                    lean_ctor_set(v___x_710_, 0, v___x_714_);
                    v___x_716_ = v___x_710_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_717_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_717_, 0, v___x_714_);
                    v___x_716_ = v_reuseFailAlloc_717_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_716_;
            }
            7 => {
                v_i_723_ = lean_ctor_get(v_a_706_, 0);
                lean_inc(v_i_723_);
                lean_dec_ref_known(v_a_706_, 1);
                if v_isShared_722_ == 0 {
                    lean_ctor_set_tag(v___x_721_, 0);
                    lean_ctor_set(v___x_721_, 0, v_i_723_);
                    v___x_725_ = v___x_721_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_729_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_729_, 0, v_i_723_);
                    lean_ctor_set(v_reuseFailAlloc_729_, 1, v_k_719_);
                    v___x_725_ = v_reuseFailAlloc_729_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                v___x_726_ = lean_box(0);
                v___x_727_ = lean_alloc_ctor(1, 2, (0) as u32);
                lean_ctor_set(v___x_727_, 0, v___x_725_);
                lean_ctor_set(v___x_727_, 1, v___x_726_);
                v___x_728_ = l_Lean_Grind_CommRing_Poly_ofMon(v___x_727_);
                return v___x_728_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Grind_CommRing_denoteSInt___redArg(
    mut v_inst_736_: *mut LeanObject,
    mut v_k_737_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_738_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_739_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_740_: u8 = 0;
    v___x_738_ = lean_unsigned_to_nat(0);
    v___x_739_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Grind_CommRing_Expr_toPolyS___closed__0),
        core::ptr::addr_of_mut!(l_Lean_Grind_CommRing_Expr_toPolyS___closed__0_once),
        _init_l_Lean_Grind_CommRing_Expr_toPolyS___closed__0,
    );
    v___x_740_ = lean_int_dec_lt(v_k_737_, v___x_739_);
    if v___x_740_ == 0 {
        let mut v_ofNat_741_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_742_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_743_: *mut LeanObject = core::ptr::null_mut();
        v_ofNat_741_ = lean_ctor_get(v_inst_736_, 3);
        lean_inc(v_ofNat_741_);
        lean_dec_ref(v_inst_736_);
        v___x_742_ = lean_nat_abs(v_k_737_);
        v___x_743_ = lean_apply_1(v_ofNat_741_, v___x_742_);
        return v___x_743_;
    } else {
        let mut v_ofNat_744_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_745_: *mut LeanObject = core::ptr::null_mut();
        v_ofNat_744_ = lean_ctor_get(v_inst_736_, 3);
        lean_inc(v_ofNat_744_);
        lean_dec_ref(v_inst_736_);
        v___x_745_ = lean_apply_1(v_ofNat_744_, v___x_738_);
        return v___x_745_;
    }
}
pub unsafe fn l_Lean_Grind_CommRing_denoteSInt___redArg___boxed(
    mut v_inst_746_: *mut LeanObject,
    mut v_k_747_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_748_: *mut LeanObject = core::ptr::null_mut();
    v_res_748_ = l_Lean_Grind_CommRing_denoteSInt___redArg(v_inst_746_, v_k_747_);
    lean_dec(v_k_747_);
    return v_res_748_;
}
pub unsafe fn l_Lean_Grind_CommRing_denoteSInt(
    mut v_00_u03b1_749_: *mut LeanObject,
    mut v_inst_750_: *mut LeanObject,
    mut v_k_751_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_752_: *mut LeanObject = core::ptr::null_mut();
    v___x_752_ = l_Lean_Grind_CommRing_denoteSInt___redArg(v_inst_750_, v_k_751_);
    return v___x_752_;
}
pub unsafe fn l_Lean_Grind_CommRing_denoteSInt___boxed(
    mut v_00_u03b1_753_: *mut LeanObject,
    mut v_inst_754_: *mut LeanObject,
    mut v_k_755_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_756_: *mut LeanObject = core::ptr::null_mut();
    v_res_756_ = l_Lean_Grind_CommRing_denoteSInt(v_00_u03b1_753_, v_inst_754_, v_k_755_);
    lean_dec(v_k_755_);
    return v_res_756_;
}
pub unsafe fn l_Lean_Grind_CommRing_Poly_denoteS___redArg(
    mut v_inst_757_: *mut LeanObject,
    mut v_ctx_758_: *mut LeanObject,
    mut v_p_759_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_p_759_) == 0 {
        let mut v_k_760_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_761_: *mut LeanObject = core::ptr::null_mut();
        v_k_760_ = lean_ctor_get(v_p_759_, 0);
        lean_inc(v_k_760_);
        lean_dec_ref_known(v_p_759_, 1);
        v___x_761_ = l_Lean_Grind_CommRing_denoteSInt___redArg(v_inst_757_, v_k_760_);
        lean_dec(v_k_760_);
        return v___x_761_;
    } else {
        let mut v_toAdd_762_: *mut LeanObject = core::ptr::null_mut();
        let mut v_toMul_763_: *mut LeanObject = core::ptr::null_mut();
        let mut v_k_764_: *mut LeanObject = core::ptr::null_mut();
        let mut v_v_765_: *mut LeanObject = core::ptr::null_mut();
        let mut v_p_766_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_767_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_768_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_769_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_770_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_771_: *mut LeanObject = core::ptr::null_mut();
        v_toAdd_762_ = lean_ctor_get(v_inst_757_, 0);
        lean_inc(v_toAdd_762_);
        v_toMul_763_ = lean_ctor_get(v_inst_757_, 1);
        v_k_764_ = lean_ctor_get(v_p_759_, 0);
        lean_inc(v_k_764_);
        v_v_765_ = lean_ctor_get(v_p_759_, 1);
        lean_inc(v_v_765_);
        v_p_766_ = lean_ctor_get(v_p_759_, 2);
        lean_inc_ref(v_p_766_);
        lean_dec_ref_known(v_p_759_, 3);
        lean_inc_ref_n(v_inst_757_, 2);
        v___x_767_ = l_Lean_Grind_CommRing_denoteSInt___redArg(v_inst_757_, v_k_764_);
        lean_dec(v_k_764_);
        v___x_768_ = l_Lean_Grind_CommRing_Mon_denote___redArg(v_inst_757_, v_ctx_758_, v_v_765_);
        lean_inc(v_toMul_763_);
        v___x_769_ = lean_apply_2(v_toMul_763_, v___x_767_, v___x_768_);
        v___x_770_ = l_Lean_Grind_CommRing_Poly_denoteS___redArg(v_inst_757_, v_ctx_758_, v_p_766_);
        v___x_771_ = lean_apply_2(v_toAdd_762_, v___x_769_, v___x_770_);
        return v___x_771_;
    }
}
pub unsafe fn l_Lean_Grind_CommRing_Poly_denoteS___redArg___boxed(
    mut v_inst_772_: *mut LeanObject,
    mut v_ctx_773_: *mut LeanObject,
    mut v_p_774_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_775_: *mut LeanObject = core::ptr::null_mut();
    v_res_775_ = l_Lean_Grind_CommRing_Poly_denoteS___redArg(v_inst_772_, v_ctx_773_, v_p_774_);
    lean_dec_ref(v_ctx_773_);
    return v_res_775_;
}
pub unsafe fn l_Lean_Grind_CommRing_Poly_denoteS(
    mut v_00_u03b1_776_: *mut LeanObject,
    mut v_inst_777_: *mut LeanObject,
    mut v_ctx_778_: *mut LeanObject,
    mut v_p_779_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_780_: *mut LeanObject = core::ptr::null_mut();
    v___x_780_ = l_Lean_Grind_CommRing_Poly_denoteS___redArg(v_inst_777_, v_ctx_778_, v_p_779_);
    return v___x_780_;
}
pub unsafe fn l_Lean_Grind_CommRing_Poly_denoteS___boxed(
    mut v_00_u03b1_781_: *mut LeanObject,
    mut v_inst_782_: *mut LeanObject,
    mut v_ctx_783_: *mut LeanObject,
    mut v_p_784_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_785_: *mut LeanObject = core::ptr::null_mut();
    v_res_785_ =
        l_Lean_Grind_CommRing_Poly_denoteS(v_00_u03b1_781_, v_inst_782_, v_ctx_783_, v_p_784_);
    lean_dec_ref(v_ctx_783_);
    return v_res_785_;
}
pub unsafe fn l___private_Init_Grind_Ring_CommSemiringAdapter_0__Lean_Grind_CommRing_Poly_denoteS_match__1_splitter___redArg(
    mut v_p_786_: *mut LeanObject,
    mut v_h__1_787_: *mut LeanObject,
    mut v_h__2_788_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_p_786_) == 0 {
        let mut v_k_789_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_790_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_788_);
        v_k_789_ = lean_ctor_get(v_p_786_, 0);
        lean_inc(v_k_789_);
        lean_dec_ref_known(v_p_786_, 1);
        v___x_790_ = lean_apply_1(v_h__1_787_, v_k_789_);
        return v___x_790_;
    } else {
        let mut v_k_791_: *mut LeanObject = core::ptr::null_mut();
        let mut v_v_792_: *mut LeanObject = core::ptr::null_mut();
        let mut v_p_793_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_794_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_787_);
        v_k_791_ = lean_ctor_get(v_p_786_, 0);
        lean_inc(v_k_791_);
        v_v_792_ = lean_ctor_get(v_p_786_, 1);
        lean_inc(v_v_792_);
        v_p_793_ = lean_ctor_get(v_p_786_, 2);
        lean_inc_ref(v_p_793_);
        lean_dec_ref_known(v_p_786_, 3);
        v___x_794_ = lean_apply_3(v_h__2_788_, v_k_791_, v_v_792_, v_p_793_);
        return v___x_794_;
    }
}
pub unsafe fn l___private_Init_Grind_Ring_CommSemiringAdapter_0__Lean_Grind_CommRing_Poly_denoteS_match__1_splitter(
    mut v_motive_795_: *mut LeanObject,
    mut v_p_796_: *mut LeanObject,
    mut v_h__1_797_: *mut LeanObject,
    mut v_h__2_798_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_p_796_) == 0 {
        let mut v_k_799_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_800_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_798_);
        v_k_799_ = lean_ctor_get(v_p_796_, 0);
        lean_inc(v_k_799_);
        lean_dec_ref_known(v_p_796_, 1);
        v___x_800_ = lean_apply_1(v_h__1_797_, v_k_799_);
        return v___x_800_;
    } else {
        let mut v_k_801_: *mut LeanObject = core::ptr::null_mut();
        let mut v_v_802_: *mut LeanObject = core::ptr::null_mut();
        let mut v_p_803_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_804_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_797_);
        v_k_801_ = lean_ctor_get(v_p_796_, 0);
        lean_inc(v_k_801_);
        v_v_802_ = lean_ctor_get(v_p_796_, 1);
        lean_inc(v_v_802_);
        v_p_803_ = lean_ctor_get(v_p_796_, 2);
        lean_inc_ref(v_p_803_);
        lean_dec_ref_known(v_p_796_, 3);
        v___x_804_ = lean_apply_3(v_h__2_798_, v_k_801_, v_v_802_, v_p_803_);
        return v___x_804_;
    }
}
pub unsafe fn l___private_Init_Grind_Ring_CommSemiringAdapter_0__Lean_Grind_CommRing_Expr_toPolyS_match__4_splitter___redArg(
    mut v_x_805_: *mut LeanObject,
    mut v_h__1_806_: *mut LeanObject,
    mut v_h__2_807_: *mut LeanObject,
    mut v_h__3_808_: *mut LeanObject,
    mut v_h__4_809_: *mut LeanObject,
    mut v_h__5_810_: *mut LeanObject,
    mut v_h__6_811_: *mut LeanObject,
    mut v_h__7_812_: *mut LeanObject,
    mut v_h__8_813_: *mut LeanObject,
    mut v_h__9_814_: *mut LeanObject,
) -> *mut LeanObject {
    match lean_obj_tag(v_x_805_) {
        0 => {
            let mut v_k_815_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_816_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__9_814_);
            lean_dec(v_h__8_813_);
            lean_dec(v_h__7_812_);
            lean_dec(v_h__6_811_);
            lean_dec(v_h__5_810_);
            lean_dec(v_h__4_809_);
            lean_dec(v_h__3_808_);
            lean_dec(v_h__2_807_);
            v_k_815_ = lean_ctor_get(v_x_805_, 0);
            lean_inc(v_k_815_);
            lean_dec_ref_known(v_x_805_, 1);
            v___x_816_ = lean_apply_1(v_h__1_806_, v_k_815_);
            return v___x_816_;
        }
        1 => {
            let mut v_k_817_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_818_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__9_814_);
            lean_dec(v_h__8_813_);
            lean_dec(v_h__7_812_);
            lean_dec(v_h__5_810_);
            lean_dec(v_h__4_809_);
            lean_dec(v_h__3_808_);
            lean_dec(v_h__2_807_);
            lean_dec(v_h__1_806_);
            v_k_817_ = lean_ctor_get(v_x_805_, 0);
            lean_inc(v_k_817_);
            lean_dec_ref_known(v_x_805_, 1);
            v___x_818_ = lean_apply_1(v_h__6_811_, v_k_817_);
            return v___x_818_;
        }
        2 => {
            let mut v_k_819_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_820_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__8_813_);
            lean_dec(v_h__7_812_);
            lean_dec(v_h__6_811_);
            lean_dec(v_h__5_810_);
            lean_dec(v_h__4_809_);
            lean_dec(v_h__3_808_);
            lean_dec(v_h__2_807_);
            lean_dec(v_h__1_806_);
            v_k_819_ = lean_ctor_get(v_x_805_, 0);
            lean_inc(v_k_819_);
            lean_dec_ref_known(v_x_805_, 1);
            v___x_820_ = lean_apply_1(v_h__9_814_, v_k_819_);
            return v___x_820_;
        }
        3 => {
            let mut v_i_821_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_822_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__9_814_);
            lean_dec(v_h__8_813_);
            lean_dec(v_h__7_812_);
            lean_dec(v_h__6_811_);
            lean_dec(v_h__5_810_);
            lean_dec(v_h__4_809_);
            lean_dec(v_h__3_808_);
            lean_dec(v_h__1_806_);
            v_i_821_ = lean_ctor_get(v_x_805_, 0);
            lean_inc(v_i_821_);
            lean_dec_ref_known(v_x_805_, 1);
            v___x_822_ = lean_apply_1(v_h__2_807_, v_i_821_);
            return v___x_822_;
        }
        4 => {
            let mut v_a_823_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_824_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__9_814_);
            lean_dec(v_h__7_812_);
            lean_dec(v_h__6_811_);
            lean_dec(v_h__5_810_);
            lean_dec(v_h__4_809_);
            lean_dec(v_h__3_808_);
            lean_dec(v_h__2_807_);
            lean_dec(v_h__1_806_);
            v_a_823_ = lean_ctor_get(v_x_805_, 0);
            lean_inc_ref(v_a_823_);
            lean_dec_ref_known(v_x_805_, 1);
            v___x_824_ = lean_apply_1(v_h__8_813_, v_a_823_);
            return v___x_824_;
        }
        5 => {
            let mut v_a_825_: *mut LeanObject = core::ptr::null_mut();
            let mut v_b_826_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_827_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__9_814_);
            lean_dec(v_h__8_813_);
            lean_dec(v_h__7_812_);
            lean_dec(v_h__6_811_);
            lean_dec(v_h__5_810_);
            lean_dec(v_h__4_809_);
            lean_dec(v_h__2_807_);
            lean_dec(v_h__1_806_);
            v_a_825_ = lean_ctor_get(v_x_805_, 0);
            lean_inc_ref(v_a_825_);
            v_b_826_ = lean_ctor_get(v_x_805_, 1);
            lean_inc_ref(v_b_826_);
            lean_dec_ref_known(v_x_805_, 2);
            v___x_827_ = lean_apply_2(v_h__3_808_, v_a_825_, v_b_826_);
            return v___x_827_;
        }
        6 => {
            let mut v_a_828_: *mut LeanObject = core::ptr::null_mut();
            let mut v_b_829_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_830_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__9_814_);
            lean_dec(v_h__8_813_);
            lean_dec(v_h__6_811_);
            lean_dec(v_h__5_810_);
            lean_dec(v_h__4_809_);
            lean_dec(v_h__3_808_);
            lean_dec(v_h__2_807_);
            lean_dec(v_h__1_806_);
            v_a_828_ = lean_ctor_get(v_x_805_, 0);
            lean_inc_ref(v_a_828_);
            v_b_829_ = lean_ctor_get(v_x_805_, 1);
            lean_inc_ref(v_b_829_);
            lean_dec_ref_known(v_x_805_, 2);
            v___x_830_ = lean_apply_2(v_h__7_812_, v_a_828_, v_b_829_);
            return v___x_830_;
        }
        7 => {
            let mut v_a_831_: *mut LeanObject = core::ptr::null_mut();
            let mut v_b_832_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_833_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__9_814_);
            lean_dec(v_h__8_813_);
            lean_dec(v_h__7_812_);
            lean_dec(v_h__6_811_);
            lean_dec(v_h__5_810_);
            lean_dec(v_h__3_808_);
            lean_dec(v_h__2_807_);
            lean_dec(v_h__1_806_);
            v_a_831_ = lean_ctor_get(v_x_805_, 0);
            lean_inc_ref(v_a_831_);
            v_b_832_ = lean_ctor_get(v_x_805_, 1);
            lean_inc_ref(v_b_832_);
            lean_dec_ref_known(v_x_805_, 2);
            v___x_833_ = lean_apply_2(v_h__4_809_, v_a_831_, v_b_832_);
            return v___x_833_;
        }
        _ => {
            let mut v_a_834_: *mut LeanObject = core::ptr::null_mut();
            let mut v_k_835_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_836_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__9_814_);
            lean_dec(v_h__8_813_);
            lean_dec(v_h__7_812_);
            lean_dec(v_h__6_811_);
            lean_dec(v_h__4_809_);
            lean_dec(v_h__3_808_);
            lean_dec(v_h__2_807_);
            lean_dec(v_h__1_806_);
            v_a_834_ = lean_ctor_get(v_x_805_, 0);
            lean_inc_ref(v_a_834_);
            v_k_835_ = lean_ctor_get(v_x_805_, 1);
            lean_inc(v_k_835_);
            lean_dec_ref_known(v_x_805_, 2);
            v___x_836_ = lean_apply_2(v_h__5_810_, v_a_834_, v_k_835_);
            return v___x_836_;
        }
    }
}
pub unsafe fn l___private_Init_Grind_Ring_CommSemiringAdapter_0__Lean_Grind_CommRing_Expr_toPolyS_match__4_splitter(
    mut v_motive_837_: *mut LeanObject,
    mut v_x_838_: *mut LeanObject,
    mut v_h__1_839_: *mut LeanObject,
    mut v_h__2_840_: *mut LeanObject,
    mut v_h__3_841_: *mut LeanObject,
    mut v_h__4_842_: *mut LeanObject,
    mut v_h__5_843_: *mut LeanObject,
    mut v_h__6_844_: *mut LeanObject,
    mut v_h__7_845_: *mut LeanObject,
    mut v_h__8_846_: *mut LeanObject,
    mut v_h__9_847_: *mut LeanObject,
) -> *mut LeanObject {
    match lean_obj_tag(v_x_838_) {
        0 => {
            let mut v_k_848_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_849_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__9_847_);
            lean_dec(v_h__8_846_);
            lean_dec(v_h__7_845_);
            lean_dec(v_h__6_844_);
            lean_dec(v_h__5_843_);
            lean_dec(v_h__4_842_);
            lean_dec(v_h__3_841_);
            lean_dec(v_h__2_840_);
            v_k_848_ = lean_ctor_get(v_x_838_, 0);
            lean_inc(v_k_848_);
            lean_dec_ref_known(v_x_838_, 1);
            v___x_849_ = lean_apply_1(v_h__1_839_, v_k_848_);
            return v___x_849_;
        }
        1 => {
            let mut v_k_850_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_851_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__9_847_);
            lean_dec(v_h__8_846_);
            lean_dec(v_h__7_845_);
            lean_dec(v_h__5_843_);
            lean_dec(v_h__4_842_);
            lean_dec(v_h__3_841_);
            lean_dec(v_h__2_840_);
            lean_dec(v_h__1_839_);
            v_k_850_ = lean_ctor_get(v_x_838_, 0);
            lean_inc(v_k_850_);
            lean_dec_ref_known(v_x_838_, 1);
            v___x_851_ = lean_apply_1(v_h__6_844_, v_k_850_);
            return v___x_851_;
        }
        2 => {
            let mut v_k_852_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_853_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__8_846_);
            lean_dec(v_h__7_845_);
            lean_dec(v_h__6_844_);
            lean_dec(v_h__5_843_);
            lean_dec(v_h__4_842_);
            lean_dec(v_h__3_841_);
            lean_dec(v_h__2_840_);
            lean_dec(v_h__1_839_);
            v_k_852_ = lean_ctor_get(v_x_838_, 0);
            lean_inc(v_k_852_);
            lean_dec_ref_known(v_x_838_, 1);
            v___x_853_ = lean_apply_1(v_h__9_847_, v_k_852_);
            return v___x_853_;
        }
        3 => {
            let mut v_i_854_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_855_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__9_847_);
            lean_dec(v_h__8_846_);
            lean_dec(v_h__7_845_);
            lean_dec(v_h__6_844_);
            lean_dec(v_h__5_843_);
            lean_dec(v_h__4_842_);
            lean_dec(v_h__3_841_);
            lean_dec(v_h__1_839_);
            v_i_854_ = lean_ctor_get(v_x_838_, 0);
            lean_inc(v_i_854_);
            lean_dec_ref_known(v_x_838_, 1);
            v___x_855_ = lean_apply_1(v_h__2_840_, v_i_854_);
            return v___x_855_;
        }
        4 => {
            let mut v_a_856_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_857_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__9_847_);
            lean_dec(v_h__7_845_);
            lean_dec(v_h__6_844_);
            lean_dec(v_h__5_843_);
            lean_dec(v_h__4_842_);
            lean_dec(v_h__3_841_);
            lean_dec(v_h__2_840_);
            lean_dec(v_h__1_839_);
            v_a_856_ = lean_ctor_get(v_x_838_, 0);
            lean_inc_ref(v_a_856_);
            lean_dec_ref_known(v_x_838_, 1);
            v___x_857_ = lean_apply_1(v_h__8_846_, v_a_856_);
            return v___x_857_;
        }
        5 => {
            let mut v_a_858_: *mut LeanObject = core::ptr::null_mut();
            let mut v_b_859_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_860_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__9_847_);
            lean_dec(v_h__8_846_);
            lean_dec(v_h__7_845_);
            lean_dec(v_h__6_844_);
            lean_dec(v_h__5_843_);
            lean_dec(v_h__4_842_);
            lean_dec(v_h__2_840_);
            lean_dec(v_h__1_839_);
            v_a_858_ = lean_ctor_get(v_x_838_, 0);
            lean_inc_ref(v_a_858_);
            v_b_859_ = lean_ctor_get(v_x_838_, 1);
            lean_inc_ref(v_b_859_);
            lean_dec_ref_known(v_x_838_, 2);
            v___x_860_ = lean_apply_2(v_h__3_841_, v_a_858_, v_b_859_);
            return v___x_860_;
        }
        6 => {
            let mut v_a_861_: *mut LeanObject = core::ptr::null_mut();
            let mut v_b_862_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_863_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__9_847_);
            lean_dec(v_h__8_846_);
            lean_dec(v_h__6_844_);
            lean_dec(v_h__5_843_);
            lean_dec(v_h__4_842_);
            lean_dec(v_h__3_841_);
            lean_dec(v_h__2_840_);
            lean_dec(v_h__1_839_);
            v_a_861_ = lean_ctor_get(v_x_838_, 0);
            lean_inc_ref(v_a_861_);
            v_b_862_ = lean_ctor_get(v_x_838_, 1);
            lean_inc_ref(v_b_862_);
            lean_dec_ref_known(v_x_838_, 2);
            v___x_863_ = lean_apply_2(v_h__7_845_, v_a_861_, v_b_862_);
            return v___x_863_;
        }
        7 => {
            let mut v_a_864_: *mut LeanObject = core::ptr::null_mut();
            let mut v_b_865_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_866_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__9_847_);
            lean_dec(v_h__8_846_);
            lean_dec(v_h__7_845_);
            lean_dec(v_h__6_844_);
            lean_dec(v_h__5_843_);
            lean_dec(v_h__3_841_);
            lean_dec(v_h__2_840_);
            lean_dec(v_h__1_839_);
            v_a_864_ = lean_ctor_get(v_x_838_, 0);
            lean_inc_ref(v_a_864_);
            v_b_865_ = lean_ctor_get(v_x_838_, 1);
            lean_inc_ref(v_b_865_);
            lean_dec_ref_known(v_x_838_, 2);
            v___x_866_ = lean_apply_2(v_h__4_842_, v_a_864_, v_b_865_);
            return v___x_866_;
        }
        _ => {
            let mut v_a_867_: *mut LeanObject = core::ptr::null_mut();
            let mut v_k_868_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_869_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__9_847_);
            lean_dec(v_h__8_846_);
            lean_dec(v_h__7_845_);
            lean_dec(v_h__6_844_);
            lean_dec(v_h__4_842_);
            lean_dec(v_h__3_841_);
            lean_dec(v_h__2_840_);
            lean_dec(v_h__1_839_);
            v_a_867_ = lean_ctor_get(v_x_838_, 0);
            lean_inc_ref(v_a_867_);
            v_k_868_ = lean_ctor_get(v_x_838_, 1);
            lean_inc(v_k_868_);
            lean_dec_ref_known(v_x_838_, 2);
            v___x_869_ = lean_apply_2(v_h__5_843_, v_a_867_, v_k_868_);
            return v___x_869_;
        }
    }
}
pub unsafe fn l___private_Init_Grind_Ring_CommSemiringAdapter_0__Lean_Grind_CommRing_Expr_toPolyS_match__1_splitter___redArg(
    mut v_a_870_: *mut LeanObject,
    mut v_h__1_871_: *mut LeanObject,
    mut v_h__2_872_: *mut LeanObject,
    mut v_h__3_873_: *mut LeanObject,
) -> *mut LeanObject {
    match lean_obj_tag(v_a_870_) {
        0 => {
            let mut v_k_874_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_875_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__3_873_);
            lean_dec(v_h__2_872_);
            v_k_874_ = lean_ctor_get(v_a_870_, 0);
            lean_inc(v_k_874_);
            lean_dec_ref_known(v_a_870_, 1);
            v___x_875_ = lean_apply_1(v_h__1_871_, v_k_874_);
            return v___x_875_;
        }
        3 => {
            let mut v_i_876_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_877_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__3_873_);
            lean_dec(v_h__1_871_);
            v_i_876_ = lean_ctor_get(v_a_870_, 0);
            lean_inc(v_i_876_);
            lean_dec_ref_known(v_a_870_, 1);
            v___x_877_ = lean_apply_1(v_h__2_872_, v_i_876_);
            return v___x_877_;
        }
        _ => {
            let mut v___x_878_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__2_872_);
            lean_dec(v_h__1_871_);
            v___x_878_ = lean_apply_3(v_h__3_873_, v_a_870_, lean_box(0), lean_box(0));
            return v___x_878_;
        }
    }
}
pub unsafe fn l___private_Init_Grind_Ring_CommSemiringAdapter_0__Lean_Grind_CommRing_Expr_toPolyS_match__1_splitter(
    mut v_motive_879_: *mut LeanObject,
    mut v_a_880_: *mut LeanObject,
    mut v_h__1_881_: *mut LeanObject,
    mut v_h__2_882_: *mut LeanObject,
    mut v_h__3_883_: *mut LeanObject,
) -> *mut LeanObject {
    match lean_obj_tag(v_a_880_) {
        0 => {
            let mut v_k_884_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_885_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__3_883_);
            lean_dec(v_h__2_882_);
            v_k_884_ = lean_ctor_get(v_a_880_, 0);
            lean_inc(v_k_884_);
            lean_dec_ref_known(v_a_880_, 1);
            v___x_885_ = lean_apply_1(v_h__1_881_, v_k_884_);
            return v___x_885_;
        }
        3 => {
            let mut v_i_886_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_887_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__3_883_);
            lean_dec(v_h__1_881_);
            v_i_886_ = lean_ctor_get(v_a_880_, 0);
            lean_inc(v_i_886_);
            lean_dec_ref_known(v_a_880_, 1);
            v___x_887_ = lean_apply_1(v_h__2_882_, v_i_886_);
            return v___x_887_;
        }
        _ => {
            let mut v___x_888_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__2_882_);
            lean_dec(v_h__1_881_);
            v___x_888_ = lean_apply_3(v_h__3_883_, v_a_880_, lean_box(0), lean_box(0));
            return v___x_888_;
        }
    }
}
pub unsafe fn l_Lean_Grind_CommRing_eq__normS__cert(
    mut v_lhs_889_: *mut LeanObject,
    mut v_rhs_890_: *mut LeanObject,
) -> u8 {
    let mut v___x_891_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_892_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_893_: u8 = 0;
    v___x_891_ = l_Lean_Grind_CommRing_Expr_toPolyS(v_lhs_889_);
    v___x_892_ = l_Lean_Grind_CommRing_Expr_toPolyS(v_rhs_890_);
    v___x_893_ = l_Lean_Grind_CommRing_instBEqPoly_beq(v___x_891_, v___x_892_);
    lean_dec_ref(v___x_892_);
    lean_dec_ref(v___x_891_);
    return v___x_893_;
}
pub unsafe fn l_Lean_Grind_CommRing_eq__normS__cert___boxed(
    mut v_lhs_894_: *mut LeanObject,
    mut v_rhs_895_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_896_: u8 = 0;
    let mut v_r_897_: *mut LeanObject = core::ptr::null_mut();
    v_res_896_ = l_Lean_Grind_CommRing_eq__normS__cert(v_lhs_894_, v_rhs_895_);
    v_r_897_ = lean_box((v_res_896_) as usize);
    return v_r_897_;
}
pub unsafe fn l_Lean_Grind_CommRing_eq__normS__nc__cert(
    mut v_lhs_898_: *mut LeanObject,
    mut v_rhs_899_: *mut LeanObject,
) -> u8 {
    let mut v___x_900_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_901_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_902_: u8 = 0;
    v___x_900_ = l_Lean_Grind_CommRing_Expr_toPolyS__nc(v_lhs_898_);
    v___x_901_ = l_Lean_Grind_CommRing_Expr_toPolyS__nc(v_rhs_899_);
    v___x_902_ = l_Lean_Grind_CommRing_instBEqPoly_beq(v___x_900_, v___x_901_);
    lean_dec_ref(v___x_901_);
    lean_dec_ref(v___x_900_);
    return v___x_902_;
}
pub unsafe fn l_Lean_Grind_CommRing_eq__normS__nc__cert___boxed(
    mut v_lhs_903_: *mut LeanObject,
    mut v_rhs_904_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_905_: u8 = 0;
    let mut v_r_906_: *mut LeanObject = core::ptr::null_mut();
    v_res_905_ = l_Lean_Grind_CommRing_eq__normS__nc__cert(v_lhs_903_, v_rhs_904_);
    v_r_906_ = lean_box((v_res_905_) as usize);
    return v_r_906_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Init_Grind_Ring_CommSemiringAdapter(
    builtin: u8,
) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Init_Grind_Ring_Envelope(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Grind_Ring_CommSolver(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Int_LemmasAux(builtin);
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
pub unsafe fn meta_initialize_Init_Grind_Ring_CommSemiringAdapter(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_meta_initialized = true;
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Init_Grind_Ring_CommSemiringAdapter(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Init_Grind_Ring_Envelope(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Grind_Ring_CommSolver(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Data_Int_LemmasAux(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Omega(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Grind_Ring_CommSemiringAdapter(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Init_Grind_Ring_CommSemiringAdapter(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Init_Grind_Ring_CommSemiringAdapter(builtin);
}
