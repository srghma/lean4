// Lean compiler output
// Module: Std.Tactic.BVDecide.Reflect
// Imports: Std.Tactic.BVDecide.LRAT.Checker Std.Tactic.BVDecide.LRAT.Parser Std.Tactic.BVDecide.Bitblast Std.Sat.AIG.CNF Std.Sat.AIG.RelabelNat
use crate::ffi::{
    lean_array_fget, lean_array_fget_borrowed, lean_array_fset, lean_array_get_size,
    lean_array_size, lean_array_uget, lean_array_uget_borrowed, lean_array_uset, lean_mk_array,
    lean_nat_add, lean_nat_dec_le, lean_nat_dec_lt, lean_nat_div, lean_nat_mul,
    lean_string_to_utf8, lean_uint64_shift_right, lean_uint64_to_usize, lean_uint64_xor,
    lean_usize_add, lean_usize_dec_lt, lean_usize_land, lean_usize_of_nat, lean_usize_sub,
};
use crate::r#gen::Std::Sat::AIG::CNF::{
    initialize_Std_Sat_AIG_CNF, l_Std_Sat_AIG_toCNF, runtime_initialize_Std_Sat_AIG_CNF,
};
use crate::r#gen::Std::Sat::AIG::Relabel::l_Std_Sat_AIG_Decl_relabel___redArg;
use crate::r#gen::Std::Sat::AIG::RelabelNat::{
    initialize_Std_Sat_AIG_RelabelNat, runtime_initialize_Std_Sat_AIG_RelabelNat,
};
use crate::r#gen::Std::Tactic::BVDecide::Bitblast::BVExpr::Basic::{
    l_Std_Tactic_BVDecide_instDecidableEqBVBit_decEq, l_Std_Tactic_BVDecide_instHashableBVBit_hash,
};
use crate::r#gen::Std::Tactic::BVDecide::Bitblast::BVExpr::Circuit::Impl::Substructure::l_Std_Tactic_BVDecide_BVLogicalExpr_bitblast;
use crate::r#gen::Std::Tactic::BVDecide::Bitblast::{
    initialize_Std_Tactic_BVDecide_Bitblast, runtime_initialize_Std_Tactic_BVDecide_Bitblast,
};
use crate::r#gen::Std::Tactic::BVDecide::LRAT::Checker::{
    initialize_Std_Tactic_BVDecide_LRAT_Checker, l_Std_Tactic_BVDecide_LRAT_check,
    runtime_initialize_Std_Tactic_BVDecide_LRAT_Checker,
};
use crate::r#gen::Std::Tactic::BVDecide::LRAT::Parser::{
    initialize_Std_Tactic_BVDecide_LRAT_Parser, l_Std_Tactic_BVDecide_LRAT_parseLRATProof,
    runtime_initialize_Std_Tactic_BVDecide_LRAT_Parser,
};
static mut l_Std_Sat_AIG_relabel___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_relabelNat___at___00Std_Sat_AIG_Entrypoint_relabelNat___at___00Std_Tactic_BVDecide_Reflect_verifyBVExpr_spec__0_spec__0_spec__1_spec__4___closed__0_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Std_Sat_AIG_relabel___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_relabelNat___at___00Std_Sat_AIG_Entrypoint_relabelNat___at___00Std_Tactic_BVDecide_Reflect_verifyBVExpr_spec__0_spec__0_spec__1_spec__4___closed__0: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Std_Sat_AIG_relabel___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_relabelNat___at___00Std_Sat_AIG_Entrypoint_relabelNat___at___00Std_Tactic_BVDecide_Reflect_verifyBVExpr_spec__0_spec__0_spec__1_spec__4___closed__1_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Std_Sat_AIG_relabel___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_relabelNat___at___00Std_Sat_AIG_Entrypoint_relabelNat___at___00Std_Tactic_BVDecide_Reflect_verifyBVExpr_spec__0_spec__0_spec__1_spec__4___closed__1: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Std_Sat_AIG_RelabelNat_State_empty___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux___at___00Std_Sat_AIG_RelabelNat_State_ofAIG___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_relabelNat___at___00Std_Sat_AIG_Entrypoint_relabelNat___at___00Std_Tactic_BVDecide_Reflect_verifyBVExpr_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___closed__0_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Std_Sat_AIG_RelabelNat_State_empty___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux___at___00Std_Sat_AIG_RelabelNat_State_ofAIG___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_relabelNat___at___00Std_Sat_AIG_Entrypoint_relabelNat___at___00Std_Tactic_BVDecide_Reflect_verifyBVExpr_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___closed__0: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Std_Sat_AIG_RelabelNat_State_empty___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux___at___00Std_Sat_AIG_RelabelNat_State_ofAIG___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_relabelNat___at___00Std_Sat_AIG_Entrypoint_relabelNat___at___00Std_Tactic_BVDecide_Reflect_verifyBVExpr_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___closed__1_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Std_Sat_AIG_RelabelNat_State_empty___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux___at___00Std_Sat_AIG_RelabelNat_State_ofAIG___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_relabelNat___at___00Std_Sat_AIG_Entrypoint_relabelNat___at___00Std_Tactic_BVDecide_Reflect_verifyBVExpr_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___closed__1: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Std_Sat_AIG_RelabelNat_State_empty___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux___at___00Std_Sat_AIG_RelabelNat_State_ofAIG___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_relabelNat___at___00Std_Sat_AIG_Entrypoint_relabelNat___at___00Std_Tactic_BVDecide_Reflect_verifyBVExpr_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___closed__2_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Std_Sat_AIG_RelabelNat_State_empty___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux___at___00Std_Sat_AIG_RelabelNat_State_ofAIG___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_relabelNat___at___00Std_Sat_AIG_Entrypoint_relabelNat___at___00Std_Tactic_BVDecide_Reflect_verifyBVExpr_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___closed__2: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub unsafe fn l_Std_Tactic_BVDecide_Reflect_verifyCert(
    mut v_cnf_447_: *mut crate::leanh::LeanObject,
    mut v_cert_448_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_449_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_450_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_449_ = lean_string_to_utf8(v_cert_448_);
    v___x_450_ = l_Std_Tactic_BVDecide_LRAT_parseLRATProof(v___x_449_);
    if crate::leanh::lean_obj_tag(v___x_450_) == 0 {
        let mut v___x_451_: u8 = 0;
        crate::leanh::lean_dec_ref_known(v___x_450_, 1);
        crate::leanh::lean_dec_ref(v_cnf_447_);
        v___x_451_ = 0;
        return v___x_451_;
    } else {
        let mut v_a_452_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_453_: u8 = 0;
        v_a_452_ = crate::leanh::lean_ctor_get(v___x_450_, 0);
        crate::leanh::lean_inc(v_a_452_);
        crate::leanh::lean_dec_ref_known(v___x_450_, 1);
        v___x_453_ = l_Std_Tactic_BVDecide_LRAT_check(v_a_452_, v_cnf_447_);
        crate::leanh::lean_dec(v_a_452_);
        return v___x_453_;
    }
}
pub unsafe fn l_Std_Tactic_BVDecide_Reflect_verifyCert___boxed(
    mut v_cnf_454_: *mut crate::leanh::LeanObject,
    mut v_cert_455_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_456_: u8 = 0;
    let mut v_r_457_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_456_ = l_Std_Tactic_BVDecide_Reflect_verifyCert(v_cnf_454_, v_cert_455_);
    crate::leanh::lean_dec_ref(v_cert_455_);
    v_r_457_ = crate::leanh::lean_box((v_res_456_) as usize);
    return v_r_457_;
}
pub unsafe fn l___private_Std_Tactic_BVDecide_Reflect_0__Std_Tactic_BVDecide_Reflect_verifyCert_match__1_splitter___redArg(
    mut v_x_458_: *mut crate::leanh::LeanObject,
    mut v_h__1_459_: *mut crate::leanh::LeanObject,
    mut v_h__2_460_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_458_) == 0 {
        let mut v_a_461_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_462_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_459_);
        v_a_461_ = crate::leanh::lean_ctor_get(v_x_458_, 0);
        crate::leanh::lean_inc(v_a_461_);
        crate::leanh::lean_dec_ref_known(v_x_458_, 1);
        v___x_462_ = crate::leanh::lean_apply_1(v_h__2_460_, v_a_461_);
        return v___x_462_;
    } else {
        let mut v_a_463_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_464_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_460_);
        v_a_463_ = crate::leanh::lean_ctor_get(v_x_458_, 0);
        crate::leanh::lean_inc(v_a_463_);
        crate::leanh::lean_dec_ref_known(v_x_458_, 1);
        v___x_464_ = crate::leanh::lean_apply_1(v_h__1_459_, v_a_463_);
        return v___x_464_;
    }
}
pub unsafe fn l___private_Std_Tactic_BVDecide_Reflect_0__Std_Tactic_BVDecide_Reflect_verifyCert_match__1_splitter(
    mut v_motive_465_: *mut crate::leanh::LeanObject,
    mut v_x_466_: *mut crate::leanh::LeanObject,
    mut v_h__1_467_: *mut crate::leanh::LeanObject,
    mut v_h__2_468_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_466_) == 0 {
        let mut v_a_469_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_470_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_467_);
        v_a_469_ = crate::leanh::lean_ctor_get(v_x_466_, 0);
        crate::leanh::lean_inc(v_a_469_);
        crate::leanh::lean_dec_ref_known(v_x_466_, 1);
        v___x_470_ = crate::leanh::lean_apply_1(v_h__2_468_, v_a_469_);
        return v___x_470_;
    } else {
        let mut v_a_471_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_472_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_468_);
        v_a_471_ = crate::leanh::lean_ctor_get(v_x_466_, 0);
        crate::leanh::lean_inc(v_a_471_);
        crate::leanh::lean_dec_ref_known(v_x_466_, 1);
        v___x_472_ = crate::leanh::lean_apply_1(v_h__1_467_, v_a_471_);
        return v___x_472_;
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_Sat_AIG_relabel___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_relabelNat___at___00Std_Sat_AIG_Entrypoint_relabelNat___at___00Std_Tactic_BVDecide_Reflect_verifyBVExpr_spec__0_spec__0_spec__1_spec__4_spec__7(
    mut v_r_473_: *mut crate::leanh::LeanObject,
    mut v_sz_474_: usize,
    mut v_i_475_: usize,
    mut v_bs_476_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_477_: u8 = 0;
    let mut v_v_478_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_479_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_bs_x27_480_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_481_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_482_: usize = 0;
    let mut v___x_483_: usize = 0;
    let mut v___x_484_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_477_ = lean_usize_dec_lt(v_i_475_, v_sz_474_);
                if v___x_477_ == 0 {
                    crate::leanh::lean_dec_ref(v_r_473_);
                    return v_bs_476_;
                } else {
                    v_v_478_ = lean_array_uget(v_bs_476_, v_i_475_);
                    v___x_479_ = crate::leanh::lean_unsigned_to_nat(0);
                    v_bs_x27_480_ = lean_array_uset(v_bs_476_, v_i_475_, v___x_479_);
                    crate::leanh::lean_inc_ref(v_r_473_);
                    v___x_481_ = l_Std_Sat_AIG_Decl_relabel___redArg(v_r_473_, v_v_478_);
                    v___x_482_ = 1usize;
                    v___x_483_ = lean_usize_add(v_i_475_, v___x_482_);
                    v___x_484_ = lean_array_uset(v_bs_x27_480_, v_i_475_, v___x_481_);
                    v_i_475_ = v___x_483_;
                    v_bs_476_ = v___x_484_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_Sat_AIG_relabel___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_relabelNat___at___00Std_Sat_AIG_Entrypoint_relabelNat___at___00Std_Tactic_BVDecide_Reflect_verifyBVExpr_spec__0_spec__0_spec__1_spec__4_spec__7___boxed(
    mut v_r_486_: *mut crate::leanh::LeanObject,
    mut v_sz_487_: *mut crate::leanh::LeanObject,
    mut v_i_488_: *mut crate::leanh::LeanObject,
    mut v_bs_489_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_sz_boxed_490_: usize = 0;
    let mut v_i_boxed_491_: usize = 0;
    let mut v_res_492_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_490_ = crate::leanh::lean_unbox_usize(v_sz_487_);
    crate::leanh::lean_dec(v_sz_487_);
    v_i_boxed_491_ = crate::leanh::lean_unbox_usize(v_i_488_);
    crate::leanh::lean_dec(v_i_488_);
    v_res_492_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_Sat_AIG_relabel___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_relabelNat___at___00Std_Sat_AIG_Entrypoint_relabelNat___at___00Std_Tactic_BVDecide_Reflect_verifyBVExpr_spec__0_spec__0_spec__1_spec__4_spec__7(v_r_486_, v_sz_boxed_490_, v_i_boxed_491_, v_bs_489_);
    return v_res_492_;
}
pub unsafe fn _init_l_Std_Sat_AIG_relabel___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_relabelNat___at___00Std_Sat_AIG_Entrypoint_relabelNat___at___00Std_Tactic_BVDecide_Reflect_verifyBVExpr_spec__0_spec__0_spec__1_spec__4___closed__0()
-> *mut crate::leanh::LeanObject {
    let mut v___x_493_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_494_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_495_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_493_ = crate::leanh::lean_box(0);
    v___x_494_ = crate::leanh::lean_unsigned_to_nat(16);
    v___x_495_ = lean_mk_array(v___x_494_, v___x_493_);
    return v___x_495_;
}
pub unsafe fn _init_l_Std_Sat_AIG_relabel___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_relabelNat___at___00Std_Sat_AIG_Entrypoint_relabelNat___at___00Std_Tactic_BVDecide_Reflect_verifyBVExpr_spec__0_spec__0_spec__1_spec__4___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_496_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_497_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_cache_498_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_496_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Std_Sat_AIG_relabel___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_relabelNat___at___00Std_Sat_AIG_Entrypoint_relabelNat___at___00Std_Tactic_BVDecide_Reflect_verifyBVExpr_spec__0_spec__0_spec__1_spec__4___closed__0), core::ptr::addr_of_mut!(l_Std_Sat_AIG_relabel___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_relabelNat___at___00Std_Sat_AIG_Entrypoint_relabelNat___at___00Std_Tactic_BVDecide_Reflect_verifyBVExpr_spec__0_spec__0_spec__1_spec__4___closed__0_once), _init_l_Std_Sat_AIG_relabel___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_relabelNat___at___00Std_Sat_AIG_Entrypoint_relabelNat___at___00Std_Tactic_BVDecide_Reflect_verifyBVExpr_spec__0_spec__0_spec__1_spec__4___closed__0);
    v___x_497_ = crate::leanh::lean_unsigned_to_nat(0);
    v_cache_498_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v_cache_498_, 0, v___x_497_);
    crate::leanh::lean_ctor_set(v_cache_498_, 1, v___x_496_);
    return v_cache_498_;
}
pub unsafe fn l_Std_Sat_AIG_relabel___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_relabelNat___at___00Std_Sat_AIG_Entrypoint_relabelNat___at___00Std_Tactic_BVDecide_Reflect_verifyBVExpr_spec__0_spec__0_spec__1_spec__4(
    mut v_r_499_: *mut crate::leanh::LeanObject,
    mut v_aig_500_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_decls_501_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_503_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_504_: u8 = 0;
    let mut v_sz_505_: usize = 0;
    let mut v___x_506_: usize = 0;
    let mut v_decls_507_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_cache_508_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_510_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_511_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_512_: u8 = 0;
    let mut v_unused_513_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_decls_501_ = crate::leanh::lean_ctor_get(v_aig_500_, 0);
                v_isSharedCheck_512_ = (!crate::leanh::lean_is_exclusive(v_aig_500_)) as u8;
                if v_isSharedCheck_512_ == 0 {
                    v_unused_513_ = crate::leanh::lean_ctor_get(v_aig_500_, 1);
                    crate::leanh::lean_dec(v_unused_513_);
                    v___x_503_ = v_aig_500_;
                    v_isShared_504_ = v_isSharedCheck_512_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_decls_501_);
                    crate::leanh::lean_dec(v_aig_500_);
                    v___x_503_ = crate::leanh::lean_box(0);
                    v_isShared_504_ = v_isSharedCheck_512_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_sz_505_ = lean_array_size(v_decls_501_);
                v___x_506_ = 0usize;
                v_decls_507_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_Sat_AIG_relabel___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_relabelNat___at___00Std_Sat_AIG_Entrypoint_relabelNat___at___00Std_Tactic_BVDecide_Reflect_verifyBVExpr_spec__0_spec__0_spec__1_spec__4_spec__7(v_r_499_, v_sz_505_, v___x_506_, v_decls_501_);
                v_cache_508_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Std_Sat_AIG_relabel___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_relabelNat___at___00Std_Sat_AIG_Entrypoint_relabelNat___at___00Std_Tactic_BVDecide_Reflect_verifyBVExpr_spec__0_spec__0_spec__1_spec__4___closed__1), core::ptr::addr_of_mut!(l_Std_Sat_AIG_relabel___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_relabelNat___at___00Std_Sat_AIG_Entrypoint_relabelNat___at___00Std_Tactic_BVDecide_Reflect_verifyBVExpr_spec__0_spec__0_spec__1_spec__4___closed__1_once), _init_l_Std_Sat_AIG_relabel___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_relabelNat___at___00Std_Sat_AIG_Entrypoint_relabelNat___at___00Std_Tactic_BVDecide_Reflect_verifyBVExpr_spec__0_spec__0_spec__1_spec__4___closed__1);
                if v_isShared_504_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_503_, 1, v_cache_508_);
                    crate::leanh::lean_ctor_set(v___x_503_, 0, v_decls_507_);
                    v___x_510_ = v___x_503_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_511_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_511_, 0, v_decls_507_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_511_, 1, v_cache_508_);
                    v___x_510_ = v_reuseFailAlloc_511_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_510_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Sat_AIG_RelabelNat_State_addFalse___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux_go___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux___at___00Std_Sat_AIG_RelabelNat_State_ofAIG___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_relabelNat___at___00Std_Sat_AIG_Entrypoint_relabelNat___at___00Std_Tactic_BVDecide_Reflect_verifyBVExpr_spec__0_spec__0_spec__1_spec__2_spec__3_spec__5_spec__8___redArg(
    mut v_state_514_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_max_515_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_map_516_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_518_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_519_: u8 = 0;
    let mut v___x_521_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_522_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_523_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_max_515_ = crate::leanh::lean_ctor_get(v_state_514_, 0);
                v_map_516_ = crate::leanh::lean_ctor_get(v_state_514_, 1);
                v_isSharedCheck_523_ = (!crate::leanh::lean_is_exclusive(v_state_514_)) as u8;
                if v_isSharedCheck_523_ == 0 {
                    v___x_518_ = v_state_514_;
                    v_isShared_519_ = v_isSharedCheck_523_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_map_516_);
                    crate::leanh::lean_inc(v_max_515_);
                    crate::leanh::lean_dec(v_state_514_);
                    v___x_518_ = crate::leanh::lean_box(0);
                    v_isShared_519_ = v_isSharedCheck_523_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                if v_isShared_519_ == 0 {
                    v___x_521_ = v___x_518_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_522_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_522_, 0, v_max_515_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_522_, 1, v_map_516_);
                    v___x_521_ = v_reuseFailAlloc_522_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_521_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_relabelNat___at___00Std_Sat_AIG_Entrypoint_relabelNat___at___00Std_Tactic_BVDecide_Reflect_verifyBVExpr_spec__0_spec__0_spec__1_spec__3_spec__5___redArg(
    mut v_a_524_: *mut crate::leanh::LeanObject,
    mut v_x_525_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_526_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_key_527_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_528_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_529_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_530_: u8 = 0;
    let mut v___x_532_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_525_) == 0 {
                    v___x_526_ = crate::leanh::lean_box(0);
                    return v___x_526_;
                } else {
                    v_key_527_ = crate::leanh::lean_ctor_get(v_x_525_, 0);
                    v_value_528_ = crate::leanh::lean_ctor_get(v_x_525_, 1);
                    v_tail_529_ = crate::leanh::lean_ctor_get(v_x_525_, 2);
                    v___x_530_ =
                        l_Std_Tactic_BVDecide_instDecidableEqBVBit_decEq(v_key_527_, v_a_524_);
                    if v___x_530_ == 0 {
                        v_x_525_ = v_tail_529_;
                        state = 0;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_value_528_);
                        v___x_532_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_532_, 0, v_value_528_);
                        return v___x_532_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_relabelNat___at___00Std_Sat_AIG_Entrypoint_relabelNat___at___00Std_Tactic_BVDecide_Reflect_verifyBVExpr_spec__0_spec__0_spec__1_spec__3_spec__5___redArg___boxed(
    mut v_a_533_: *mut crate::leanh::LeanObject,
    mut v_x_534_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_535_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_535_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_relabelNat___at___00Std_Sat_AIG_Entrypoint_relabelNat___at___00Std_Tactic_BVDecide_Reflect_verifyBVExpr_spec__0_spec__0_spec__1_spec__3_spec__5___redArg(v_a_533_, v_x_534_);
    crate::leanh::lean_dec(v_x_534_);
    crate::leanh::lean_dec_ref(v_a_533_);
    return v_res_535_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_relabelNat___at___00Std_Sat_AIG_Entrypoint_relabelNat___at___00Std_Tactic_BVDecide_Reflect_verifyBVExpr_spec__0_spec__0_spec__1_spec__3___redArg(
    mut v_m_536_: *mut crate::leanh::LeanObject,
    mut v_a_537_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_buckets_538_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_539_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_540_: u64 = 0;
    let mut v___x_541_: u64 = 0;
    let mut v___x_542_: u64 = 0;
    let mut v_fold_543_: u64 = 0;
    let mut v___x_544_: u64 = 0;
    let mut v___x_545_: u64 = 0;
    let mut v___x_546_: u64 = 0;
    let mut v___x_547_: usize = 0;
    let mut v___x_548_: usize = 0;
    let mut v___x_549_: usize = 0;
    let mut v___x_550_: usize = 0;
    let mut v___x_551_: usize = 0;
    let mut v___x_552_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_553_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_buckets_538_ = crate::leanh::lean_ctor_get(v_m_536_, 1);
    v___x_539_ = lean_array_get_size(v_buckets_538_);
    v___x_540_ = l_Std_Tactic_BVDecide_instHashableBVBit_hash(v_a_537_);
    v___x_541_ = 32u64;
    v___x_542_ = lean_uint64_shift_right(v___x_540_, v___x_541_);
    v_fold_543_ = lean_uint64_xor(v___x_540_, v___x_542_);
    v___x_544_ = 16u64;
    v___x_545_ = lean_uint64_shift_right(v_fold_543_, v___x_544_);
    v___x_546_ = lean_uint64_xor(v_fold_543_, v___x_545_);
    v___x_547_ = lean_uint64_to_usize(v___x_546_);
    v___x_548_ = lean_usize_of_nat(v___x_539_);
    v___x_549_ = 1usize;
    v___x_550_ = lean_usize_sub(v___x_548_, v___x_549_);
    v___x_551_ = lean_usize_land(v___x_547_, v___x_550_);
    v___x_552_ = lean_array_uget_borrowed(v_buckets_538_, v___x_551_);
    v___x_553_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_relabelNat___at___00Std_Sat_AIG_Entrypoint_relabelNat___at___00Std_Tactic_BVDecide_Reflect_verifyBVExpr_spec__0_spec__0_spec__1_spec__3_spec__5___redArg(v_a_537_, v___x_552_);
    return v___x_553_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_relabelNat___at___00Std_Sat_AIG_Entrypoint_relabelNat___at___00Std_Tactic_BVDecide_Reflect_verifyBVExpr_spec__0_spec__0_spec__1_spec__3___redArg___boxed(
    mut v_m_554_: *mut crate::leanh::LeanObject,
    mut v_a_555_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_556_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_556_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_relabelNat___at___00Std_Sat_AIG_Entrypoint_relabelNat___at___00Std_Tactic_BVDecide_Reflect_verifyBVExpr_spec__0_spec__0_spec__1_spec__3___redArg(v_m_554_, v_a_555_);
    crate::leanh::lean_dec_ref(v_a_555_);
    crate::leanh::lean_dec_ref(v_m_554_);
    return v_res_556_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Sat_AIG_RelabelNat_State_addAtom___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux_go___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux___at___00Std_Sat_AIG_RelabelNat_State_ofAIG___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_relabelNat___at___00Std_Sat_AIG_Entrypoint_relabelNat___at___00Std_Tactic_BVDecide_Reflect_verifyBVExpr_spec__0_spec__0_spec__1_spec__2_spec__3_spec__5_spec__9_spec__12_spec__16___redArg(
    mut v_a_557_: *mut crate::leanh::LeanObject,
    mut v_b_558_: *mut crate::leanh::LeanObject,
    mut v_x_559_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_key_560_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_561_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_562_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_564_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_565_: u8 = 0;
    let mut v___x_566_: u8 = 0;
    let mut v___x_567_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_569_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_570_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_572_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_573_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_574_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_559_) == 0 {
                    crate::leanh::lean_dec(v_b_558_);
                    crate::leanh::lean_dec_ref(v_a_557_);
                    return v_x_559_;
                } else {
                    v_key_560_ = crate::leanh::lean_ctor_get(v_x_559_, 0);
                    v_value_561_ = crate::leanh::lean_ctor_get(v_x_559_, 1);
                    v_tail_562_ = crate::leanh::lean_ctor_get(v_x_559_, 2);
                    v_isSharedCheck_574_ = (!crate::leanh::lean_is_exclusive(v_x_559_)) as u8;
                    if v_isSharedCheck_574_ == 0 {
                        v___x_564_ = v_x_559_;
                        v_isShared_565_ = v_isSharedCheck_574_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_tail_562_);
                        crate::leanh::lean_inc(v_value_561_);
                        crate::leanh::lean_inc(v_key_560_);
                        crate::leanh::lean_dec(v_x_559_);
                        v___x_564_ = crate::leanh::lean_box(0);
                        v_isShared_565_ = v_isSharedCheck_574_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_566_ = l_Std_Tactic_BVDecide_instDecidableEqBVBit_decEq(v_key_560_, v_a_557_);
                if v___x_566_ == 0 {
                    v___x_567_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Sat_AIG_RelabelNat_State_addAtom___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux_go___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux___at___00Std_Sat_AIG_RelabelNat_State_ofAIG___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_relabelNat___at___00Std_Sat_AIG_Entrypoint_relabelNat___at___00Std_Tactic_BVDecide_Reflect_verifyBVExpr_spec__0_spec__0_spec__1_spec__2_spec__3_spec__5_spec__9_spec__12_spec__16___redArg(v_a_557_, v_b_558_, v_tail_562_);
                    if v_isShared_565_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_564_, 2, v___x_567_);
                        v___x_569_ = v___x_564_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_570_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_570_, 0, v_key_560_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_570_, 1, v_value_561_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_570_, 2, v___x_567_);
                        v___x_569_ = v_reuseFailAlloc_570_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_value_561_);
                    crate::leanh::lean_dec(v_key_560_);
                    if v_isShared_565_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_564_, 1, v_b_558_);
                        crate::leanh::lean_ctor_set(v___x_564_, 0, v_a_557_);
                        v___x_572_ = v___x_564_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_573_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_573_, 0, v_a_557_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_573_, 1, v_b_558_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_573_, 2, v_tail_562_);
                        v___x_572_ = v_reuseFailAlloc_573_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_569_;
            }
            3 => {
                return v___x_572_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Sat_AIG_RelabelNat_State_addAtom___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux_go___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux___at___00Std_Sat_AIG_RelabelNat_State_ofAIG___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_relabelNat___at___00Std_Sat_AIG_Entrypoint_relabelNat___at___00Std_Tactic_BVDecide_Reflect_verifyBVExpr_spec__0_spec__0_spec__1_spec__2_spec__3_spec__5_spec__9_spec__12_spec__15_spec__16_spec__17___redArg(
    mut v_x_575_: *mut crate::leanh::LeanObject,
    mut v_x_576_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_key_577_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_578_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_579_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_581_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_582_: u8 = 0;
    let mut v___x_583_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_584_: u64 = 0;
    let mut v___x_585_: u64 = 0;
    let mut v___x_586_: u64 = 0;
    let mut v_fold_587_: u64 = 0;
    let mut v___x_588_: u64 = 0;
    let mut v___x_589_: u64 = 0;
    let mut v___x_590_: u64 = 0;
    let mut v___x_591_: usize = 0;
    let mut v___x_592_: usize = 0;
    let mut v___x_593_: usize = 0;
    let mut v___x_594_: usize = 0;
    let mut v___x_595_: usize = 0;
    let mut v___x_596_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_598_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_599_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_601_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_602_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_576_) == 0 {
                    return v_x_575_;
                } else {
                    v_key_577_ = crate::leanh::lean_ctor_get(v_x_576_, 0);
                    v_value_578_ = crate::leanh::lean_ctor_get(v_x_576_, 1);
                    v_tail_579_ = crate::leanh::lean_ctor_get(v_x_576_, 2);
                    v_isSharedCheck_602_ = (!crate::leanh::lean_is_exclusive(v_x_576_)) as u8;
                    if v_isSharedCheck_602_ == 0 {
                        v___x_581_ = v_x_576_;
                        v_isShared_582_ = v_isSharedCheck_602_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_tail_579_);
                        crate::leanh::lean_inc(v_value_578_);
                        crate::leanh::lean_inc(v_key_577_);
                        crate::leanh::lean_dec(v_x_576_);
                        v___x_581_ = crate::leanh::lean_box(0);
                        v_isShared_582_ = v_isSharedCheck_602_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_583_ = lean_array_get_size(v_x_575_);
                v___x_584_ = l_Std_Tactic_BVDecide_instHashableBVBit_hash(v_key_577_);
                v___x_585_ = 32u64;
                v___x_586_ = lean_uint64_shift_right(v___x_584_, v___x_585_);
                v_fold_587_ = lean_uint64_xor(v___x_584_, v___x_586_);
                v___x_588_ = 16u64;
                v___x_589_ = lean_uint64_shift_right(v_fold_587_, v___x_588_);
                v___x_590_ = lean_uint64_xor(v_fold_587_, v___x_589_);
                v___x_591_ = lean_uint64_to_usize(v___x_590_);
                v___x_592_ = lean_usize_of_nat(v___x_583_);
                v___x_593_ = 1usize;
                v___x_594_ = lean_usize_sub(v___x_592_, v___x_593_);
                v___x_595_ = lean_usize_land(v___x_591_, v___x_594_);
                v___x_596_ = lean_array_uget_borrowed(v_x_575_, v___x_595_);
                crate::leanh::lean_inc(v___x_596_);
                if v_isShared_582_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_581_, 2, v___x_596_);
                    v___x_598_ = v___x_581_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_601_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_601_, 0, v_key_577_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_601_, 1, v_value_578_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_601_, 2, v___x_596_);
                    v___x_598_ = v_reuseFailAlloc_601_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_599_ = lean_array_uset(v_x_575_, v___x_595_, v___x_598_);
                v_x_575_ = v___x_599_;
                v_x_576_ = v_tail_579_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Sat_AIG_RelabelNat_State_addAtom___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux_go___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux___at___00Std_Sat_AIG_RelabelNat_State_ofAIG___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_relabelNat___at___00Std_Sat_AIG_Entrypoint_relabelNat___at___00Std_Tactic_BVDecide_Reflect_verifyBVExpr_spec__0_spec__0_spec__1_spec__2_spec__3_spec__5_spec__9_spec__12_spec__15_spec__16___redArg(
    mut v_i_603_: *mut crate::leanh::LeanObject,
    mut v_source_604_: *mut crate::leanh::LeanObject,
    mut v_target_605_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_606_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_607_: u8 = 0;
    let mut v_es_608_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_609_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_source_610_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_target_611_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_612_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_613_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_606_ = lean_array_get_size(v_source_604_);
                v___x_607_ = lean_nat_dec_lt(v_i_603_, v___x_606_);
                if v___x_607_ == 0 {
                    crate::leanh::lean_dec_ref(v_source_604_);
                    crate::leanh::lean_dec(v_i_603_);
                    return v_target_605_;
                } else {
                    v_es_608_ = lean_array_fget(v_source_604_, v_i_603_);
                    v___x_609_ = crate::leanh::lean_box(0);
                    v_source_610_ = lean_array_fset(v_source_604_, v_i_603_, v___x_609_);
                    v_target_611_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Sat_AIG_RelabelNat_State_addAtom___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux_go___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux___at___00Std_Sat_AIG_RelabelNat_State_ofAIG___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_relabelNat___at___00Std_Sat_AIG_Entrypoint_relabelNat___at___00Std_Tactic_BVDecide_Reflect_verifyBVExpr_spec__0_spec__0_spec__1_spec__2_spec__3_spec__5_spec__9_spec__12_spec__15_spec__16_spec__17___redArg(v_target_605_, v_es_608_);
                    v___x_612_ = crate::leanh::lean_unsigned_to_nat(1);
                    v___x_613_ = lean_nat_add(v_i_603_, v___x_612_);
                    crate::leanh::lean_dec(v_i_603_);
                    v_i_603_ = v___x_613_;
                    v_source_604_ = v_source_610_;
                    v_target_605_ = v_target_611_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Sat_AIG_RelabelNat_State_addAtom___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux_go___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux___at___00Std_Sat_AIG_RelabelNat_State_ofAIG___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_relabelNat___at___00Std_Sat_AIG_Entrypoint_relabelNat___at___00Std_Tactic_BVDecide_Reflect_verifyBVExpr_spec__0_spec__0_spec__1_spec__2_spec__3_spec__5_spec__9_spec__12_spec__15___redArg(
    mut v_data_615_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_616_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_617_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nbuckets_618_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_619_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_620_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_621_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_622_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_616_ = lean_array_get_size(v_data_615_);
    v___x_617_ = crate::leanh::lean_unsigned_to_nat(2);
    v_nbuckets_618_ = lean_nat_mul(v___x_616_, v___x_617_);
    v___x_619_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_620_ = crate::leanh::lean_box(0);
    v___x_621_ = lean_mk_array(v_nbuckets_618_, v___x_620_);
    v___x_622_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Sat_AIG_RelabelNat_State_addAtom___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux_go___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux___at___00Std_Sat_AIG_RelabelNat_State_ofAIG___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_relabelNat___at___00Std_Sat_AIG_Entrypoint_relabelNat___at___00Std_Tactic_BVDecide_Reflect_verifyBVExpr_spec__0_spec__0_spec__1_spec__2_spec__3_spec__5_spec__9_spec__12_spec__15_spec__16___redArg(v___x_619_, v_data_615_, v___x_621_);
    return v___x_622_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Sat_AIG_RelabelNat_State_addAtom___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux_go___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux___at___00Std_Sat_AIG_RelabelNat_State_ofAIG___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_relabelNat___at___00Std_Sat_AIG_Entrypoint_relabelNat___at___00Std_Tactic_BVDecide_Reflect_verifyBVExpr_spec__0_spec__0_spec__1_spec__2_spec__3_spec__5_spec__9_spec__12_spec__14___redArg(
    mut v_a_623_: *mut crate::leanh::LeanObject,
    mut v_x_624_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_625_: u8 = 0;
    let mut v_key_626_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_627_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_628_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_624_) == 0 {
                    v___x_625_ = 0;
                    return v___x_625_;
                } else {
                    v_key_626_ = crate::leanh::lean_ctor_get(v_x_624_, 0);
                    v_tail_627_ = crate::leanh::lean_ctor_get(v_x_624_, 2);
                    v___x_628_ =
                        l_Std_Tactic_BVDecide_instDecidableEqBVBit_decEq(v_key_626_, v_a_623_);
                    if v___x_628_ == 0 {
                        v_x_624_ = v_tail_627_;
                        state = 0;
                        continue;
                    } else {
                        return v___x_628_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Sat_AIG_RelabelNat_State_addAtom___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux_go___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux___at___00Std_Sat_AIG_RelabelNat_State_ofAIG___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_relabelNat___at___00Std_Sat_AIG_Entrypoint_relabelNat___at___00Std_Tactic_BVDecide_Reflect_verifyBVExpr_spec__0_spec__0_spec__1_spec__2_spec__3_spec__5_spec__9_spec__12_spec__14___redArg___boxed(
    mut v_a_630_: *mut crate::leanh::LeanObject,
    mut v_x_631_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_632_: u8 = 0;
    let mut v_r_633_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_632_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Sat_AIG_RelabelNat_State_addAtom___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux_go___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux___at___00Std_Sat_AIG_RelabelNat_State_ofAIG___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_relabelNat___at___00Std_Sat_AIG_Entrypoint_relabelNat___at___00Std_Tactic_BVDecide_Reflect_verifyBVExpr_spec__0_spec__0_spec__1_spec__2_spec__3_spec__5_spec__9_spec__12_spec__14___redArg(v_a_630_, v_x_631_);
    crate::leanh::lean_dec(v_x_631_);
    crate::leanh::lean_dec_ref(v_a_630_);
    v_r_633_ = crate::leanh::lean_box((v_res_632_) as usize);
    return v_r_633_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Sat_AIG_RelabelNat_State_addAtom___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux_go___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux___at___00Std_Sat_AIG_RelabelNat_State_ofAIG___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_relabelNat___at___00Std_Sat_AIG_Entrypoint_relabelNat___at___00Std_Tactic_BVDecide_Reflect_verifyBVExpr_spec__0_spec__0_spec__1_spec__2_spec__3_spec__5_spec__9_spec__12___redArg(
    mut v_m_634_: *mut crate::leanh::LeanObject,
    mut v_a_635_: *mut crate::leanh::LeanObject,
    mut v_b_636_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_size_637_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_638_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_640_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_641_: u8 = 0;
    let mut v___x_642_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_643_: u64 = 0;
    let mut v___x_644_: u64 = 0;
    let mut v___x_645_: u64 = 0;
    let mut v_fold_646_: u64 = 0;
    let mut v___x_647_: u64 = 0;
    let mut v___x_648_: u64 = 0;
    let mut v___x_649_: u64 = 0;
    let mut v___x_650_: usize = 0;
    let mut v___x_651_: usize = 0;
    let mut v___x_652_: usize = 0;
    let mut v___x_653_: usize = 0;
    let mut v___x_654_: usize = 0;
    let mut v_bkt_655_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_656_: u8 = 0;
    let mut v___x_657_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_x27_658_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_659_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_x27_660_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_661_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_662_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_663_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_664_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_665_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_666_: u8 = 0;
    let mut v_val_667_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_669_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_670_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_672_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_673_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_674_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_x27_675_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_676_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_677_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_679_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_680_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_681_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_size_637_ = crate::leanh::lean_ctor_get(v_m_634_, 0);
                v_buckets_638_ = crate::leanh::lean_ctor_get(v_m_634_, 1);
                v_isSharedCheck_681_ = (!crate::leanh::lean_is_exclusive(v_m_634_)) as u8;
                if v_isSharedCheck_681_ == 0 {
                    v___x_640_ = v_m_634_;
                    v_isShared_641_ = v_isSharedCheck_681_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_buckets_638_);
                    crate::leanh::lean_inc(v_size_637_);
                    crate::leanh::lean_dec(v_m_634_);
                    v___x_640_ = crate::leanh::lean_box(0);
                    v_isShared_641_ = v_isSharedCheck_681_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_642_ = lean_array_get_size(v_buckets_638_);
                v___x_643_ = l_Std_Tactic_BVDecide_instHashableBVBit_hash(v_a_635_);
                v___x_644_ = 32u64;
                v___x_645_ = lean_uint64_shift_right(v___x_643_, v___x_644_);
                v_fold_646_ = lean_uint64_xor(v___x_643_, v___x_645_);
                v___x_647_ = 16u64;
                v___x_648_ = lean_uint64_shift_right(v_fold_646_, v___x_647_);
                v___x_649_ = lean_uint64_xor(v_fold_646_, v___x_648_);
                v___x_650_ = lean_uint64_to_usize(v___x_649_);
                v___x_651_ = lean_usize_of_nat(v___x_642_);
                v___x_652_ = 1usize;
                v___x_653_ = lean_usize_sub(v___x_651_, v___x_652_);
                v___x_654_ = lean_usize_land(v___x_650_, v___x_653_);
                v_bkt_655_ = lean_array_uget_borrowed(v_buckets_638_, v___x_654_);
                v___x_656_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Sat_AIG_RelabelNat_State_addAtom___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux_go___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux___at___00Std_Sat_AIG_RelabelNat_State_ofAIG___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_relabelNat___at___00Std_Sat_AIG_Entrypoint_relabelNat___at___00Std_Tactic_BVDecide_Reflect_verifyBVExpr_spec__0_spec__0_spec__1_spec__2_spec__3_spec__5_spec__9_spec__12_spec__14___redArg(v_a_635_, v_bkt_655_);
                if v___x_656_ == 0 {
                    v___x_657_ = crate::leanh::lean_unsigned_to_nat(1);
                    v_size_x27_658_ = lean_nat_add(v_size_637_, v___x_657_);
                    crate::leanh::lean_dec(v_size_637_);
                    crate::leanh::lean_inc(v_bkt_655_);
                    v___x_659_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_659_, 0, v_a_635_);
                    crate::leanh::lean_ctor_set(v___x_659_, 1, v_b_636_);
                    crate::leanh::lean_ctor_set(v___x_659_, 2, v_bkt_655_);
                    v_buckets_x27_660_ = lean_array_uset(v_buckets_638_, v___x_654_, v___x_659_);
                    v___x_661_ = crate::leanh::lean_unsigned_to_nat(4);
                    v___x_662_ = lean_nat_mul(v_size_x27_658_, v___x_661_);
                    v___x_663_ = crate::leanh::lean_unsigned_to_nat(3);
                    v___x_664_ = lean_nat_div(v___x_662_, v___x_663_);
                    crate::leanh::lean_dec(v___x_662_);
                    v___x_665_ = lean_array_get_size(v_buckets_x27_660_);
                    v___x_666_ = lean_nat_dec_le(v___x_664_, v___x_665_);
                    crate::leanh::lean_dec(v___x_664_);
                    if v___x_666_ == 0 {
                        v_val_667_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Sat_AIG_RelabelNat_State_addAtom___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux_go___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux___at___00Std_Sat_AIG_RelabelNat_State_ofAIG___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_relabelNat___at___00Std_Sat_AIG_Entrypoint_relabelNat___at___00Std_Tactic_BVDecide_Reflect_verifyBVExpr_spec__0_spec__0_spec__1_spec__2_spec__3_spec__5_spec__9_spec__12_spec__15___redArg(v_buckets_x27_660_);
                        if v_isShared_641_ == 0 {
                            crate::leanh::lean_ctor_set(v___x_640_, 1, v_val_667_);
                            crate::leanh::lean_ctor_set(v___x_640_, 0, v_size_x27_658_);
                            v___x_669_ = v___x_640_;
                            state = 2;
                            continue;
                        } else {
                            v_reuseFailAlloc_670_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_670_, 0, v_size_x27_658_);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_670_, 1, v_val_667_);
                            v___x_669_ = v_reuseFailAlloc_670_;
                            state = 2;
                            continue;
                        }
                    } else {
                        if v_isShared_641_ == 0 {
                            crate::leanh::lean_ctor_set(v___x_640_, 1, v_buckets_x27_660_);
                            crate::leanh::lean_ctor_set(v___x_640_, 0, v_size_x27_658_);
                            v___x_672_ = v___x_640_;
                            state = 3;
                            continue;
                        } else {
                            v_reuseFailAlloc_673_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_673_, 0, v_size_x27_658_);
                            crate::leanh::lean_ctor_set(
                                v_reuseFailAlloc_673_,
                                1,
                                v_buckets_x27_660_,
                            );
                            v___x_672_ = v_reuseFailAlloc_673_;
                            state = 3;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_inc(v_bkt_655_);
                    v___x_674_ = crate::leanh::lean_box(0);
                    v_buckets_x27_675_ = lean_array_uset(v_buckets_638_, v___x_654_, v___x_674_);
                    v___x_676_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Sat_AIG_RelabelNat_State_addAtom___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux_go___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux___at___00Std_Sat_AIG_RelabelNat_State_ofAIG___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_relabelNat___at___00Std_Sat_AIG_Entrypoint_relabelNat___at___00Std_Tactic_BVDecide_Reflect_verifyBVExpr_spec__0_spec__0_spec__1_spec__2_spec__3_spec__5_spec__9_spec__12_spec__16___redArg(v_a_635_, v_b_636_, v_bkt_655_);
                    v___x_677_ = lean_array_uset(v_buckets_x27_675_, v___x_654_, v___x_676_);
                    if v_isShared_641_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_640_, 1, v___x_677_);
                        v___x_679_ = v___x_640_;
                        state = 4;
                        continue;
                    } else {
                        v_reuseFailAlloc_680_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_680_, 0, v_size_637_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_680_, 1, v___x_677_);
                        v___x_679_ = v_reuseFailAlloc_680_;
                        state = 4;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_669_;
            }
            3 => {
                return v___x_672_;
            }
            4 => {
                return v___x_679_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Sat_AIG_RelabelNat_State_addAtom___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux_go___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux___at___00Std_Sat_AIG_RelabelNat_State_ofAIG___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_relabelNat___at___00Std_Sat_AIG_Entrypoint_relabelNat___at___00Std_Tactic_BVDecide_Reflect_verifyBVExpr_spec__0_spec__0_spec__1_spec__2_spec__3_spec__5_spec__9___redArg(
    mut v_state_682_: *mut crate::leanh::LeanObject,
    mut v_a_683_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_max_684_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_map_685_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_687_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_688_: u8 = 0;
    let mut v___x_689_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_690_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_691_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_692_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_694_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_695_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_697_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_698_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_699_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_max_684_ = crate::leanh::lean_ctor_get(v_state_682_, 0);
                v_map_685_ = crate::leanh::lean_ctor_get(v_state_682_, 1);
                v_isSharedCheck_699_ = (!crate::leanh::lean_is_exclusive(v_state_682_)) as u8;
                if v_isSharedCheck_699_ == 0 {
                    v___x_687_ = v_state_682_;
                    v_isShared_688_ = v_isSharedCheck_699_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_map_685_);
                    crate::leanh::lean_inc(v_max_684_);
                    crate::leanh::lean_dec(v_state_682_);
                    v___x_687_ = crate::leanh::lean_box(0);
                    v_isShared_688_ = v_isSharedCheck_699_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_689_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_relabelNat___at___00Std_Sat_AIG_Entrypoint_relabelNat___at___00Std_Tactic_BVDecide_Reflect_verifyBVExpr_spec__0_spec__0_spec__1_spec__3___redArg(v_map_685_, v_a_683_);
                if crate::leanh::lean_obj_tag(v___x_689_) == 0 {
                    v___x_690_ = crate::leanh::lean_unsigned_to_nat(1);
                    v___x_691_ = lean_nat_add(v_max_684_, v___x_690_);
                    v___x_692_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Sat_AIG_RelabelNat_State_addAtom___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux_go___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux___at___00Std_Sat_AIG_RelabelNat_State_ofAIG___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_relabelNat___at___00Std_Sat_AIG_Entrypoint_relabelNat___at___00Std_Tactic_BVDecide_Reflect_verifyBVExpr_spec__0_spec__0_spec__1_spec__2_spec__3_spec__5_spec__9_spec__12___redArg(v_map_685_, v_a_683_, v_max_684_);
                    if v_isShared_688_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_687_, 1, v___x_692_);
                        crate::leanh::lean_ctor_set(v___x_687_, 0, v___x_691_);
                        v___x_694_ = v___x_687_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_695_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_695_, 0, v___x_691_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_695_, 1, v___x_692_);
                        v___x_694_ = v_reuseFailAlloc_695_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec_ref_known(v___x_689_, 1);
                    crate::leanh::lean_dec_ref(v_a_683_);
                    if v_isShared_688_ == 0 {
                        v___x_697_ = v___x_687_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_698_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_698_, 0, v_max_684_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_698_, 1, v_map_685_);
                        v___x_697_ = v_reuseFailAlloc_698_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_694_;
            }
            3 => {
                return v___x_697_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Sat_AIG_RelabelNat_State_addGate___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux_go___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux___at___00Std_Sat_AIG_RelabelNat_State_ofAIG___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_relabelNat___at___00Std_Sat_AIG_Entrypoint_relabelNat___at___00Std_Tactic_BVDecide_Reflect_verifyBVExpr_spec__0_spec__0_spec__1_spec__2_spec__3_spec__5_spec__10___redArg(
    mut v_state_700_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_max_701_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_map_702_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_704_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_705_: u8 = 0;
    let mut v___x_707_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_708_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_709_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_max_701_ = crate::leanh::lean_ctor_get(v_state_700_, 0);
                v_map_702_ = crate::leanh::lean_ctor_get(v_state_700_, 1);
                v_isSharedCheck_709_ = (!crate::leanh::lean_is_exclusive(v_state_700_)) as u8;
                if v_isSharedCheck_709_ == 0 {
                    v___x_704_ = v_state_700_;
                    v_isShared_705_ = v_isSharedCheck_709_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_map_702_);
                    crate::leanh::lean_inc(v_max_701_);
                    crate::leanh::lean_dec(v_state_700_);
                    v___x_704_ = crate::leanh::lean_box(0);
                    v_isShared_705_ = v_isSharedCheck_709_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                if v_isShared_705_ == 0 {
                    v___x_707_ = v___x_704_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_708_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_708_, 0, v_max_701_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_708_, 1, v_map_702_);
                    v___x_707_ = v_reuseFailAlloc_708_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_707_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Sat_AIG_RelabelNat_State_ofAIGAux_go___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux___at___00Std_Sat_AIG_RelabelNat_State_ofAIG___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_relabelNat___at___00Std_Sat_AIG_Entrypoint_relabelNat___at___00Std_Tactic_BVDecide_Reflect_verifyBVExpr_spec__0_spec__0_spec__1_spec__2_spec__3_spec__5(
    mut v_decls_710_: *mut crate::leanh::LeanObject,
    mut v_idx_711_: *mut crate::leanh::LeanObject,
    mut v_state_712_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_713_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_714_: u8 = 0;
    let mut v_decl_715_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_716_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_717_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_718_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_idx_720_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_721_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_722_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_723_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_725_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_726_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_727_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_713_ = lean_array_get_size(v_decls_710_);
                v___x_714_ = lean_nat_dec_lt(v_idx_711_, v___x_713_);
                if v___x_714_ == 0 {
                    crate::leanh::lean_dec(v_idx_711_);
                    return v_state_712_;
                } else {
                    v_decl_715_ = lean_array_fget_borrowed(v_decls_710_, v_idx_711_);
                    match crate::leanh::lean_obj_tag(v_decl_715_) {
                        0 => {
                            v___x_716_ = crate::leanh::lean_unsigned_to_nat(1);
                            v___x_717_ = lean_nat_add(v_idx_711_, v___x_716_);
                            crate::leanh::lean_dec(v_idx_711_);
                            v___x_718_ = l_Std_Sat_AIG_RelabelNat_State_addFalse___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux_go___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux___at___00Std_Sat_AIG_RelabelNat_State_ofAIG___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_relabelNat___at___00Std_Sat_AIG_Entrypoint_relabelNat___at___00Std_Tactic_BVDecide_Reflect_verifyBVExpr_spec__0_spec__0_spec__1_spec__2_spec__3_spec__5_spec__8___redArg(v_state_712_);
                            v_idx_711_ = v___x_717_;
                            v_state_712_ = v___x_718_;
                            state = 0;
                            continue;
                        }
                        1 => {
                            v_idx_720_ = crate::leanh::lean_ctor_get(v_decl_715_, 0);
                            v___x_721_ = crate::leanh::lean_unsigned_to_nat(1);
                            v___x_722_ = lean_nat_add(v_idx_711_, v___x_721_);
                            crate::leanh::lean_dec(v_idx_711_);
                            crate::leanh::lean_inc(v_idx_720_);
                            v___x_723_ = l_Std_Sat_AIG_RelabelNat_State_addAtom___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux_go___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux___at___00Std_Sat_AIG_RelabelNat_State_ofAIG___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_relabelNat___at___00Std_Sat_AIG_Entrypoint_relabelNat___at___00Std_Tactic_BVDecide_Reflect_verifyBVExpr_spec__0_spec__0_spec__1_spec__2_spec__3_spec__5_spec__9___redArg(v_state_712_, v_idx_720_);
                            v_idx_711_ = v___x_722_;
                            v_state_712_ = v___x_723_;
                            state = 0;
                            continue;
                        }
                        _ => {
                            v___x_725_ = crate::leanh::lean_unsigned_to_nat(1);
                            v___x_726_ = lean_nat_add(v_idx_711_, v___x_725_);
                            crate::leanh::lean_dec(v_idx_711_);
                            v___x_727_ = l_Std_Sat_AIG_RelabelNat_State_addGate___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux_go___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux___at___00Std_Sat_AIG_RelabelNat_State_ofAIG___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_relabelNat___at___00Std_Sat_AIG_Entrypoint_relabelNat___at___00Std_Tactic_BVDecide_Reflect_verifyBVExpr_spec__0_spec__0_spec__1_spec__2_spec__3_spec__5_spec__10___redArg(v_state_712_);
                            v_idx_711_ = v___x_726_;
                            v_state_712_ = v___x_727_;
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
pub unsafe fn l_Std_Sat_AIG_RelabelNat_State_ofAIGAux_go___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux___at___00Std_Sat_AIG_RelabelNat_State_ofAIG___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_relabelNat___at___00Std_Sat_AIG_Entrypoint_relabelNat___at___00Std_Tactic_BVDecide_Reflect_verifyBVExpr_spec__0_spec__0_spec__1_spec__2_spec__3_spec__5___boxed(
    mut v_decls_729_: *mut crate::leanh::LeanObject,
    mut v_idx_730_: *mut crate::leanh::LeanObject,
    mut v_state_731_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_732_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_732_ = l_Std_Sat_AIG_RelabelNat_State_ofAIGAux_go___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux___at___00Std_Sat_AIG_RelabelNat_State_ofAIG___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_relabelNat___at___00Std_Sat_AIG_Entrypoint_relabelNat___at___00Std_Tactic_BVDecide_Reflect_verifyBVExpr_spec__0_spec__0_spec__1_spec__2_spec__3_spec__5(v_decls_729_, v_idx_730_, v_state_731_);
    crate::leanh::lean_dec_ref(v_decls_729_);
    return v_res_732_;
}
pub unsafe fn _init_l_Std_Sat_AIG_RelabelNat_State_empty___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux___at___00Std_Sat_AIG_RelabelNat_State_ofAIG___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_relabelNat___at___00Std_Sat_AIG_Entrypoint_relabelNat___at___00Std_Tactic_BVDecide_Reflect_verifyBVExpr_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___closed__0()
-> *mut crate::leanh::LeanObject {
    let mut v___x_733_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_734_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_735_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_733_ = crate::leanh::lean_box(0);
    v___x_734_ = crate::leanh::lean_unsigned_to_nat(16);
    v___x_735_ = lean_mk_array(v___x_734_, v___x_733_);
    return v___x_735_;
}
pub unsafe fn _init_l_Std_Sat_AIG_RelabelNat_State_empty___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux___at___00Std_Sat_AIG_RelabelNat_State_ofAIG___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_relabelNat___at___00Std_Sat_AIG_Entrypoint_relabelNat___at___00Std_Tactic_BVDecide_Reflect_verifyBVExpr_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_736_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_737_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_738_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_736_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Std_Sat_AIG_RelabelNat_State_empty___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux___at___00Std_Sat_AIG_RelabelNat_State_ofAIG___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_relabelNat___at___00Std_Sat_AIG_Entrypoint_relabelNat___at___00Std_Tactic_BVDecide_Reflect_verifyBVExpr_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___closed__0), core::ptr::addr_of_mut!(l_Std_Sat_AIG_RelabelNat_State_empty___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux___at___00Std_Sat_AIG_RelabelNat_State_ofAIG___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_relabelNat___at___00Std_Sat_AIG_Entrypoint_relabelNat___at___00Std_Tactic_BVDecide_Reflect_verifyBVExpr_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___closed__0_once), _init_l_Std_Sat_AIG_RelabelNat_State_empty___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux___at___00Std_Sat_AIG_RelabelNat_State_ofAIG___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_relabelNat___at___00Std_Sat_AIG_Entrypoint_relabelNat___at___00Std_Tactic_BVDecide_Reflect_verifyBVExpr_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___closed__0);
    v___x_737_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_738_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_738_, 0, v___x_737_);
    crate::leanh::lean_ctor_set(v___x_738_, 1, v___x_736_);
    return v___x_738_;
}
pub unsafe fn _init_l_Std_Sat_AIG_RelabelNat_State_empty___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux___at___00Std_Sat_AIG_RelabelNat_State_ofAIG___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_relabelNat___at___00Std_Sat_AIG_Entrypoint_relabelNat___at___00Std_Tactic_BVDecide_Reflect_verifyBVExpr_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___closed__2()
-> *mut crate::leanh::LeanObject {
    let mut v___x_739_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_740_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_741_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_739_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Std_Sat_AIG_RelabelNat_State_empty___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux___at___00Std_Sat_AIG_RelabelNat_State_ofAIG___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_relabelNat___at___00Std_Sat_AIG_Entrypoint_relabelNat___at___00Std_Tactic_BVDecide_Reflect_verifyBVExpr_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___closed__1), core::ptr::addr_of_mut!(l_Std_Sat_AIG_RelabelNat_State_empty___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux___at___00Std_Sat_AIG_RelabelNat_State_ofAIG___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_relabelNat___at___00Std_Sat_AIG_Entrypoint_relabelNat___at___00Std_Tactic_BVDecide_Reflect_verifyBVExpr_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___closed__1_once), _init_l_Std_Sat_AIG_RelabelNat_State_empty___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux___at___00Std_Sat_AIG_RelabelNat_State_ofAIG___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_relabelNat___at___00Std_Sat_AIG_Entrypoint_relabelNat___at___00Std_Tactic_BVDecide_Reflect_verifyBVExpr_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___closed__1);
    v___x_740_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_741_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_741_, 0, v___x_740_);
    crate::leanh::lean_ctor_set(v___x_741_, 1, v___x_739_);
    return v___x_741_;
}
pub unsafe fn l_Std_Sat_AIG_RelabelNat_State_empty___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux___at___00Std_Sat_AIG_RelabelNat_State_ofAIG___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_relabelNat___at___00Std_Sat_AIG_Entrypoint_relabelNat___at___00Std_Tactic_BVDecide_Reflect_verifyBVExpr_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4(
    mut v_decls_742_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_743_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_743_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Std_Sat_AIG_RelabelNat_State_empty___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux___at___00Std_Sat_AIG_RelabelNat_State_ofAIG___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_relabelNat___at___00Std_Sat_AIG_Entrypoint_relabelNat___at___00Std_Tactic_BVDecide_Reflect_verifyBVExpr_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___closed__2), core::ptr::addr_of_mut!(l_Std_Sat_AIG_RelabelNat_State_empty___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux___at___00Std_Sat_AIG_RelabelNat_State_ofAIG___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_relabelNat___at___00Std_Sat_AIG_Entrypoint_relabelNat___at___00Std_Tactic_BVDecide_Reflect_verifyBVExpr_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___closed__2_once), _init_l_Std_Sat_AIG_RelabelNat_State_empty___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux___at___00Std_Sat_AIG_RelabelNat_State_ofAIG___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_relabelNat___at___00Std_Sat_AIG_Entrypoint_relabelNat___at___00Std_Tactic_BVDecide_Reflect_verifyBVExpr_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___closed__2);
    return v___x_743_;
}
pub unsafe fn l_Std_Sat_AIG_RelabelNat_State_empty___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux___at___00Std_Sat_AIG_RelabelNat_State_ofAIG___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_relabelNat___at___00Std_Sat_AIG_Entrypoint_relabelNat___at___00Std_Tactic_BVDecide_Reflect_verifyBVExpr_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___boxed(
    mut v_decls_744_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_745_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_745_ = l_Std_Sat_AIG_RelabelNat_State_empty___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux___at___00Std_Sat_AIG_RelabelNat_State_ofAIG___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_relabelNat___at___00Std_Sat_AIG_Entrypoint_relabelNat___at___00Std_Tactic_BVDecide_Reflect_verifyBVExpr_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4(v_decls_744_);
    crate::leanh::lean_dec_ref(v_decls_744_);
    return v_res_745_;
}
pub unsafe fn l_Std_Sat_AIG_RelabelNat_State_ofAIGAux___at___00Std_Sat_AIG_RelabelNat_State_ofAIG___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_relabelNat___at___00Std_Sat_AIG_Entrypoint_relabelNat___at___00Std_Tactic_BVDecide_Reflect_verifyBVExpr_spec__0_spec__0_spec__1_spec__2_spec__3(
    mut v_aig_746_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_decls_747_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_748_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_749_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_750_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_decls_747_ = crate::leanh::lean_ctor_get(v_aig_746_, 0);
    v___x_748_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_749_ = l_Std_Sat_AIG_RelabelNat_State_empty___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux___at___00Std_Sat_AIG_RelabelNat_State_ofAIG___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_relabelNat___at___00Std_Sat_AIG_Entrypoint_relabelNat___at___00Std_Tactic_BVDecide_Reflect_verifyBVExpr_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4(v_decls_747_);
    v___x_750_ = l_Std_Sat_AIG_RelabelNat_State_ofAIGAux_go___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux___at___00Std_Sat_AIG_RelabelNat_State_ofAIG___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_relabelNat___at___00Std_Sat_AIG_Entrypoint_relabelNat___at___00Std_Tactic_BVDecide_Reflect_verifyBVExpr_spec__0_spec__0_spec__1_spec__2_spec__3_spec__5(v_decls_747_, v___x_748_, v___x_749_);
    return v___x_750_;
}
pub unsafe fn l_Std_Sat_AIG_RelabelNat_State_ofAIGAux___at___00Std_Sat_AIG_RelabelNat_State_ofAIG___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_relabelNat___at___00Std_Sat_AIG_Entrypoint_relabelNat___at___00Std_Tactic_BVDecide_Reflect_verifyBVExpr_spec__0_spec__0_spec__1_spec__2_spec__3___boxed(
    mut v_aig_751_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_752_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_752_ = l_Std_Sat_AIG_RelabelNat_State_ofAIGAux___at___00Std_Sat_AIG_RelabelNat_State_ofAIG___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_relabelNat___at___00Std_Sat_AIG_Entrypoint_relabelNat___at___00Std_Tactic_BVDecide_Reflect_verifyBVExpr_spec__0_spec__0_spec__1_spec__2_spec__3(v_aig_751_);
    crate::leanh::lean_dec_ref(v_aig_751_);
    return v_res_752_;
}
pub unsafe fn l_Std_Sat_AIG_RelabelNat_State_ofAIG___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_relabelNat___at___00Std_Sat_AIG_Entrypoint_relabelNat___at___00Std_Tactic_BVDecide_Reflect_verifyBVExpr_spec__0_spec__0_spec__1_spec__2(
    mut v_aig_753_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_754_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_map_755_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_754_ = l_Std_Sat_AIG_RelabelNat_State_ofAIGAux___at___00Std_Sat_AIG_RelabelNat_State_ofAIG___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_relabelNat___at___00Std_Sat_AIG_Entrypoint_relabelNat___at___00Std_Tactic_BVDecide_Reflect_verifyBVExpr_spec__0_spec__0_spec__1_spec__2_spec__3(v_aig_753_);
    v_map_755_ = crate::leanh::lean_ctor_get(v___x_754_, 1);
    crate::leanh::lean_inc_ref(v_map_755_);
    crate::leanh::lean_dec_ref(v___x_754_);
    return v_map_755_;
}
pub unsafe fn l_Std_Sat_AIG_RelabelNat_State_ofAIG___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_relabelNat___at___00Std_Sat_AIG_Entrypoint_relabelNat___at___00Std_Tactic_BVDecide_Reflect_verifyBVExpr_spec__0_spec__0_spec__1_spec__2___boxed(
    mut v_aig_756_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_757_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_757_ = l_Std_Sat_AIG_RelabelNat_State_ofAIG___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_relabelNat___at___00Std_Sat_AIG_Entrypoint_relabelNat___at___00Std_Tactic_BVDecide_Reflect_verifyBVExpr_spec__0_spec__0_spec__1_spec__2(v_aig_756_);
    crate::leanh::lean_dec_ref(v_aig_756_);
    return v_res_757_;
}
pub unsafe fn l_Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_relabelNat___at___00Std_Sat_AIG_Entrypoint_relabelNat___at___00Std_Tactic_BVDecide_Reflect_verifyBVExpr_spec__0_spec__0_spec__1___lam__0(
    mut v_map_758_: *mut crate::leanh::LeanObject,
    mut v_x_759_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_760_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_760_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_relabelNat___at___00Std_Sat_AIG_Entrypoint_relabelNat___at___00Std_Tactic_BVDecide_Reflect_verifyBVExpr_spec__0_spec__0_spec__1_spec__3___redArg(v_map_758_, v_x_759_);
    if crate::leanh::lean_obj_tag(v___x_760_) == 0 {
        let mut v___x_761_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_761_ = crate::leanh::lean_unsigned_to_nat(0);
        return v___x_761_;
    } else {
        let mut v_val_762_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_val_762_ = crate::leanh::lean_ctor_get(v___x_760_, 0);
        crate::leanh::lean_inc(v_val_762_);
        crate::leanh::lean_dec_ref_known(v___x_760_, 1);
        return v_val_762_;
    }
}
pub unsafe fn l_Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_relabelNat___at___00Std_Sat_AIG_Entrypoint_relabelNat___at___00Std_Tactic_BVDecide_Reflect_verifyBVExpr_spec__0_spec__0_spec__1___lam__0___boxed(
    mut v_map_763_: *mut crate::leanh::LeanObject,
    mut v_x_764_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_765_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_765_ = l_Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_relabelNat___at___00Std_Sat_AIG_Entrypoint_relabelNat___at___00Std_Tactic_BVDecide_Reflect_verifyBVExpr_spec__0_spec__0_spec__1___lam__0(v_map_763_, v_x_764_);
    crate::leanh::lean_dec_ref(v_x_764_);
    crate::leanh::lean_dec_ref(v_map_763_);
    return v_res_765_;
}
pub unsafe fn l_Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_relabelNat___at___00Std_Sat_AIG_Entrypoint_relabelNat___at___00Std_Tactic_BVDecide_Reflect_verifyBVExpr_spec__0_spec__0_spec__1(
    mut v_aig_766_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_map_767_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_768_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_aig_769_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_770_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_map_767_ = l_Std_Sat_AIG_RelabelNat_State_ofAIG___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_relabelNat___at___00Std_Sat_AIG_Entrypoint_relabelNat___at___00Std_Tactic_BVDecide_Reflect_verifyBVExpr_spec__0_spec__0_spec__1_spec__2(v_aig_766_);
    crate::leanh::lean_inc_ref(v_map_767_);
    v___f_768_ = crate::leanh::lean_alloc_closure(l_Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_relabelNat___at___00Std_Sat_AIG_Entrypoint_relabelNat___at___00Std_Tactic_BVDecide_Reflect_verifyBVExpr_spec__0_spec__0_spec__1___lam__0___boxed as *mut core::ffi::c_void, 2, 1);
    crate::leanh::lean_closure_set(v___f_768_, 0, v_map_767_);
    v_aig_769_ = l_Std_Sat_AIG_relabel___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_relabelNat___at___00Std_Sat_AIG_Entrypoint_relabelNat___at___00Std_Tactic_BVDecide_Reflect_verifyBVExpr_spec__0_spec__0_spec__1_spec__4(v___f_768_, v_aig_766_);
    v___x_770_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_770_, 0, v_aig_769_);
    crate::leanh::lean_ctor_set(v___x_770_, 1, v_map_767_);
    return v___x_770_;
}
pub unsafe fn l_Std_Sat_AIG_relabelNat___at___00Std_Sat_AIG_Entrypoint_relabelNat___at___00Std_Tactic_BVDecide_Reflect_verifyBVExpr_spec__0_spec__0(
    mut v_aig_771_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_772_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_773_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_772_ = l_Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_relabelNat___at___00Std_Sat_AIG_Entrypoint_relabelNat___at___00Std_Tactic_BVDecide_Reflect_verifyBVExpr_spec__0_spec__0_spec__1(v_aig_771_);
    v_fst_773_ = crate::leanh::lean_ctor_get(v___x_772_, 0);
    crate::leanh::lean_inc(v_fst_773_);
    crate::leanh::lean_dec_ref(v___x_772_);
    return v_fst_773_;
}
pub unsafe fn l_Std_Sat_AIG_Entrypoint_relabelNat___at___00Std_Tactic_BVDecide_Reflect_verifyBVExpr_spec__0(
    mut v_entry_774_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_ref_775_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_aig_776_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_778_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_779_: u8 = 0;
    let mut v_gate_780_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_invert_781_: u8 = 0;
    let mut v___x_783_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_784_: u8 = 0;
    let mut v___x_785_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_787_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_789_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_790_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_791_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_792_: u8 = 0;
    let mut v_isSharedCheck_793_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ref_775_ = crate::leanh::lean_ctor_get(v_entry_774_, 1);
                v_aig_776_ = crate::leanh::lean_ctor_get(v_entry_774_, 0);
                v_isSharedCheck_793_ = (!crate::leanh::lean_is_exclusive(v_entry_774_)) as u8;
                if v_isSharedCheck_793_ == 0 {
                    v___x_778_ = v_entry_774_;
                    v_isShared_779_ = v_isSharedCheck_793_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_ref_775_);
                    crate::leanh::lean_inc(v_aig_776_);
                    crate::leanh::lean_dec(v_entry_774_);
                    v___x_778_ = crate::leanh::lean_box(0);
                    v_isShared_779_ = v_isSharedCheck_793_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_gate_780_ = crate::leanh::lean_ctor_get(v_ref_775_, 0);
                v_invert_781_ = crate::leanh::lean_ctor_get_uint8(
                    v_ref_775_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                );
                v_isSharedCheck_792_ = (!crate::leanh::lean_is_exclusive(v_ref_775_)) as u8;
                if v_isSharedCheck_792_ == 0 {
                    v___x_783_ = v_ref_775_;
                    v_isShared_784_ = v_isSharedCheck_792_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_gate_780_);
                    crate::leanh::lean_dec(v_ref_775_);
                    v___x_783_ = crate::leanh::lean_box(0);
                    v_isShared_784_ = v_isSharedCheck_792_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_785_ = l_Std_Sat_AIG_relabelNat___at___00Std_Sat_AIG_Entrypoint_relabelNat___at___00Std_Tactic_BVDecide_Reflect_verifyBVExpr_spec__0_spec__0(v_aig_776_);
                if v_isShared_784_ == 0 {
                    v___x_787_ = v___x_783_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_791_ = crate::leanh::lean_alloc_ctor(0, 1, (1) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_791_, 0, v_gate_780_);
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_791_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                        v_invert_781_,
                    );
                    v___x_787_ = v_reuseFailAlloc_791_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_779_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_778_, 1, v___x_787_);
                    crate::leanh::lean_ctor_set(v___x_778_, 0, v___x_785_);
                    v___x_789_ = v___x_778_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_790_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_790_, 0, v___x_785_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_790_, 1, v___x_787_);
                    v___x_789_ = v_reuseFailAlloc_790_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_789_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Tactic_BVDecide_Reflect_verifyBVExpr(
    mut v_bv_794_: *mut crate::leanh::LeanObject,
    mut v_cert_795_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_796_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_797_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_798_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_799_: u8 = 0;
    v___x_796_ = l_Std_Tactic_BVDecide_BVLogicalExpr_bitblast(v_bv_794_);
    v___x_797_ = l_Std_Sat_AIG_Entrypoint_relabelNat___at___00Std_Tactic_BVDecide_Reflect_verifyBVExpr_spec__0(v___x_796_);
    v___x_798_ = l_Std_Sat_AIG_toCNF(v___x_797_);
    v___x_799_ = l_Std_Tactic_BVDecide_Reflect_verifyCert(v___x_798_, v_cert_795_);
    return v___x_799_;
}
pub unsafe fn l_Std_Tactic_BVDecide_Reflect_verifyBVExpr___boxed(
    mut v_bv_800_: *mut crate::leanh::LeanObject,
    mut v_cert_801_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_802_: u8 = 0;
    let mut v_r_803_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_802_ = l_Std_Tactic_BVDecide_Reflect_verifyBVExpr(v_bv_800_, v_cert_801_);
    crate::leanh::lean_dec_ref(v_cert_801_);
    v_r_803_ = crate::leanh::lean_box((v_res_802_) as usize);
    return v_r_803_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_relabelNat___at___00Std_Sat_AIG_Entrypoint_relabelNat___at___00Std_Tactic_BVDecide_Reflect_verifyBVExpr_spec__0_spec__0_spec__1_spec__3(
    mut v_00_u03b2_804_: *mut crate::leanh::LeanObject,
    mut v_m_805_: *mut crate::leanh::LeanObject,
    mut v_a_806_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_807_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_807_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_relabelNat___at___00Std_Sat_AIG_Entrypoint_relabelNat___at___00Std_Tactic_BVDecide_Reflect_verifyBVExpr_spec__0_spec__0_spec__1_spec__3___redArg(v_m_805_, v_a_806_);
    return v___x_807_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_relabelNat___at___00Std_Sat_AIG_Entrypoint_relabelNat___at___00Std_Tactic_BVDecide_Reflect_verifyBVExpr_spec__0_spec__0_spec__1_spec__3___boxed(
    mut v_00_u03b2_808_: *mut crate::leanh::LeanObject,
    mut v_m_809_: *mut crate::leanh::LeanObject,
    mut v_a_810_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_811_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_811_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_relabelNat___at___00Std_Sat_AIG_Entrypoint_relabelNat___at___00Std_Tactic_BVDecide_Reflect_verifyBVExpr_spec__0_spec__0_spec__1_spec__3(v_00_u03b2_808_, v_m_809_, v_a_810_);
    crate::leanh::lean_dec_ref(v_a_810_);
    crate::leanh::lean_dec_ref(v_m_809_);
    return v_res_811_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_relabelNat___at___00Std_Sat_AIG_Entrypoint_relabelNat___at___00Std_Tactic_BVDecide_Reflect_verifyBVExpr_spec__0_spec__0_spec__1_spec__3_spec__5(
    mut v_00_u03b2_812_: *mut crate::leanh::LeanObject,
    mut v_a_813_: *mut crate::leanh::LeanObject,
    mut v_x_814_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_815_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_815_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_relabelNat___at___00Std_Sat_AIG_Entrypoint_relabelNat___at___00Std_Tactic_BVDecide_Reflect_verifyBVExpr_spec__0_spec__0_spec__1_spec__3_spec__5___redArg(v_a_813_, v_x_814_);
    return v___x_815_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_relabelNat___at___00Std_Sat_AIG_Entrypoint_relabelNat___at___00Std_Tactic_BVDecide_Reflect_verifyBVExpr_spec__0_spec__0_spec__1_spec__3_spec__5___boxed(
    mut v_00_u03b2_816_: *mut crate::leanh::LeanObject,
    mut v_a_817_: *mut crate::leanh::LeanObject,
    mut v_x_818_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_819_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_819_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_relabelNat___at___00Std_Sat_AIG_Entrypoint_relabelNat___at___00Std_Tactic_BVDecide_Reflect_verifyBVExpr_spec__0_spec__0_spec__1_spec__3_spec__5(v_00_u03b2_816_, v_a_817_, v_x_818_);
    crate::leanh::lean_dec(v_x_818_);
    crate::leanh::lean_dec_ref(v_a_817_);
    return v_res_819_;
}
pub unsafe fn l_Std_Sat_AIG_RelabelNat_State_addFalse___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux_go___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux___at___00Std_Sat_AIG_RelabelNat_State_ofAIG___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_relabelNat___at___00Std_Sat_AIG_Entrypoint_relabelNat___at___00Std_Tactic_BVDecide_Reflect_verifyBVExpr_spec__0_spec__0_spec__1_spec__2_spec__3_spec__5_spec__8(
    mut v_idx_820_: *mut crate::leanh::LeanObject,
    mut v_decls_821_: *mut crate::leanh::LeanObject,
    mut v_hidx_822_: *mut crate::leanh::LeanObject,
    mut v_state_823_: *mut crate::leanh::LeanObject,
    mut v_h_824_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_825_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_825_ = l_Std_Sat_AIG_RelabelNat_State_addFalse___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux_go___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux___at___00Std_Sat_AIG_RelabelNat_State_ofAIG___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_relabelNat___at___00Std_Sat_AIG_Entrypoint_relabelNat___at___00Std_Tactic_BVDecide_Reflect_verifyBVExpr_spec__0_spec__0_spec__1_spec__2_spec__3_spec__5_spec__8___redArg(v_state_823_);
    return v___x_825_;
}
pub unsafe fn l_Std_Sat_AIG_RelabelNat_State_addFalse___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux_go___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux___at___00Std_Sat_AIG_RelabelNat_State_ofAIG___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_relabelNat___at___00Std_Sat_AIG_Entrypoint_relabelNat___at___00Std_Tactic_BVDecide_Reflect_verifyBVExpr_spec__0_spec__0_spec__1_spec__2_spec__3_spec__5_spec__8___boxed(
    mut v_idx_826_: *mut crate::leanh::LeanObject,
    mut v_decls_827_: *mut crate::leanh::LeanObject,
    mut v_hidx_828_: *mut crate::leanh::LeanObject,
    mut v_state_829_: *mut crate::leanh::LeanObject,
    mut v_h_830_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_831_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_831_ = l_Std_Sat_AIG_RelabelNat_State_addFalse___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux_go___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux___at___00Std_Sat_AIG_RelabelNat_State_ofAIG___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_relabelNat___at___00Std_Sat_AIG_Entrypoint_relabelNat___at___00Std_Tactic_BVDecide_Reflect_verifyBVExpr_spec__0_spec__0_spec__1_spec__2_spec__3_spec__5_spec__8(v_idx_826_, v_decls_827_, v_hidx_828_, v_state_829_, v_h_830_);
    crate::leanh::lean_dec_ref(v_decls_827_);
    crate::leanh::lean_dec(v_idx_826_);
    return v_res_831_;
}
pub unsafe fn l_Std_Sat_AIG_RelabelNat_State_addGate___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux_go___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux___at___00Std_Sat_AIG_RelabelNat_State_ofAIG___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_relabelNat___at___00Std_Sat_AIG_Entrypoint_relabelNat___at___00Std_Tactic_BVDecide_Reflect_verifyBVExpr_spec__0_spec__0_spec__1_spec__2_spec__3_spec__5_spec__10(
    mut v_idx_832_: *mut crate::leanh::LeanObject,
    mut v_decls_833_: *mut crate::leanh::LeanObject,
    mut v_hidx_834_: *mut crate::leanh::LeanObject,
    mut v_state_835_: *mut crate::leanh::LeanObject,
    mut v_lhs_836_: *mut crate::leanh::LeanObject,
    mut v_rhs_837_: *mut crate::leanh::LeanObject,
    mut v_h_838_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_839_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_839_ = l_Std_Sat_AIG_RelabelNat_State_addGate___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux_go___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux___at___00Std_Sat_AIG_RelabelNat_State_ofAIG___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_relabelNat___at___00Std_Sat_AIG_Entrypoint_relabelNat___at___00Std_Tactic_BVDecide_Reflect_verifyBVExpr_spec__0_spec__0_spec__1_spec__2_spec__3_spec__5_spec__10___redArg(v_state_835_);
    return v___x_839_;
}
pub unsafe fn l_Std_Sat_AIG_RelabelNat_State_addGate___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux_go___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux___at___00Std_Sat_AIG_RelabelNat_State_ofAIG___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_relabelNat___at___00Std_Sat_AIG_Entrypoint_relabelNat___at___00Std_Tactic_BVDecide_Reflect_verifyBVExpr_spec__0_spec__0_spec__1_spec__2_spec__3_spec__5_spec__10___boxed(
    mut v_idx_840_: *mut crate::leanh::LeanObject,
    mut v_decls_841_: *mut crate::leanh::LeanObject,
    mut v_hidx_842_: *mut crate::leanh::LeanObject,
    mut v_state_843_: *mut crate::leanh::LeanObject,
    mut v_lhs_844_: *mut crate::leanh::LeanObject,
    mut v_rhs_845_: *mut crate::leanh::LeanObject,
    mut v_h_846_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_847_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_847_ = l_Std_Sat_AIG_RelabelNat_State_addGate___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux_go___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux___at___00Std_Sat_AIG_RelabelNat_State_ofAIG___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_relabelNat___at___00Std_Sat_AIG_Entrypoint_relabelNat___at___00Std_Tactic_BVDecide_Reflect_verifyBVExpr_spec__0_spec__0_spec__1_spec__2_spec__3_spec__5_spec__10(v_idx_840_, v_decls_841_, v_hidx_842_, v_state_843_, v_lhs_844_, v_rhs_845_, v_h_846_);
    crate::leanh::lean_dec(v_rhs_845_);
    crate::leanh::lean_dec(v_lhs_844_);
    crate::leanh::lean_dec_ref(v_decls_841_);
    crate::leanh::lean_dec(v_idx_840_);
    return v_res_847_;
}
pub unsafe fn l_Std_Sat_AIG_RelabelNat_State_addAtom___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux_go___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux___at___00Std_Sat_AIG_RelabelNat_State_ofAIG___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_relabelNat___at___00Std_Sat_AIG_Entrypoint_relabelNat___at___00Std_Tactic_BVDecide_Reflect_verifyBVExpr_spec__0_spec__0_spec__1_spec__2_spec__3_spec__5_spec__9(
    mut v_idx_848_: *mut crate::leanh::LeanObject,
    mut v_decls_849_: *mut crate::leanh::LeanObject,
    mut v_hidx_850_: *mut crate::leanh::LeanObject,
    mut v_state_851_: *mut crate::leanh::LeanObject,
    mut v_a_852_: *mut crate::leanh::LeanObject,
    mut v_h_853_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_854_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_854_ = l_Std_Sat_AIG_RelabelNat_State_addAtom___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux_go___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux___at___00Std_Sat_AIG_RelabelNat_State_ofAIG___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_relabelNat___at___00Std_Sat_AIG_Entrypoint_relabelNat___at___00Std_Tactic_BVDecide_Reflect_verifyBVExpr_spec__0_spec__0_spec__1_spec__2_spec__3_spec__5_spec__9___redArg(v_state_851_, v_a_852_);
    return v___x_854_;
}
pub unsafe fn l_Std_Sat_AIG_RelabelNat_State_addAtom___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux_go___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux___at___00Std_Sat_AIG_RelabelNat_State_ofAIG___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_relabelNat___at___00Std_Sat_AIG_Entrypoint_relabelNat___at___00Std_Tactic_BVDecide_Reflect_verifyBVExpr_spec__0_spec__0_spec__1_spec__2_spec__3_spec__5_spec__9___boxed(
    mut v_idx_855_: *mut crate::leanh::LeanObject,
    mut v_decls_856_: *mut crate::leanh::LeanObject,
    mut v_hidx_857_: *mut crate::leanh::LeanObject,
    mut v_state_858_: *mut crate::leanh::LeanObject,
    mut v_a_859_: *mut crate::leanh::LeanObject,
    mut v_h_860_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_861_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_861_ = l_Std_Sat_AIG_RelabelNat_State_addAtom___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux_go___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux___at___00Std_Sat_AIG_RelabelNat_State_ofAIG___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_relabelNat___at___00Std_Sat_AIG_Entrypoint_relabelNat___at___00Std_Tactic_BVDecide_Reflect_verifyBVExpr_spec__0_spec__0_spec__1_spec__2_spec__3_spec__5_spec__9(v_idx_855_, v_decls_856_, v_hidx_857_, v_state_858_, v_a_859_, v_h_860_);
    crate::leanh::lean_dec_ref(v_decls_856_);
    crate::leanh::lean_dec(v_idx_855_);
    return v_res_861_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Sat_AIG_RelabelNat_State_addAtom___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux_go___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux___at___00Std_Sat_AIG_RelabelNat_State_ofAIG___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_relabelNat___at___00Std_Sat_AIG_Entrypoint_relabelNat___at___00Std_Tactic_BVDecide_Reflect_verifyBVExpr_spec__0_spec__0_spec__1_spec__2_spec__3_spec__5_spec__9_spec__12(
    mut v_00_u03b2_862_: *mut crate::leanh::LeanObject,
    mut v_m_863_: *mut crate::leanh::LeanObject,
    mut v_a_864_: *mut crate::leanh::LeanObject,
    mut v_b_865_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_866_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_866_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Sat_AIG_RelabelNat_State_addAtom___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux_go___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux___at___00Std_Sat_AIG_RelabelNat_State_ofAIG___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_relabelNat___at___00Std_Sat_AIG_Entrypoint_relabelNat___at___00Std_Tactic_BVDecide_Reflect_verifyBVExpr_spec__0_spec__0_spec__1_spec__2_spec__3_spec__5_spec__9_spec__12___redArg(v_m_863_, v_a_864_, v_b_865_);
    return v___x_866_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Sat_AIG_RelabelNat_State_addAtom___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux_go___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux___at___00Std_Sat_AIG_RelabelNat_State_ofAIG___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_relabelNat___at___00Std_Sat_AIG_Entrypoint_relabelNat___at___00Std_Tactic_BVDecide_Reflect_verifyBVExpr_spec__0_spec__0_spec__1_spec__2_spec__3_spec__5_spec__9_spec__12_spec__14(
    mut v_00_u03b2_867_: *mut crate::leanh::LeanObject,
    mut v_a_868_: *mut crate::leanh::LeanObject,
    mut v_x_869_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_870_: u8 = 0;
    v___x_870_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Sat_AIG_RelabelNat_State_addAtom___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux_go___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux___at___00Std_Sat_AIG_RelabelNat_State_ofAIG___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_relabelNat___at___00Std_Sat_AIG_Entrypoint_relabelNat___at___00Std_Tactic_BVDecide_Reflect_verifyBVExpr_spec__0_spec__0_spec__1_spec__2_spec__3_spec__5_spec__9_spec__12_spec__14___redArg(v_a_868_, v_x_869_);
    return v___x_870_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Sat_AIG_RelabelNat_State_addAtom___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux_go___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux___at___00Std_Sat_AIG_RelabelNat_State_ofAIG___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_relabelNat___at___00Std_Sat_AIG_Entrypoint_relabelNat___at___00Std_Tactic_BVDecide_Reflect_verifyBVExpr_spec__0_spec__0_spec__1_spec__2_spec__3_spec__5_spec__9_spec__12_spec__14___boxed(
    mut v_00_u03b2_871_: *mut crate::leanh::LeanObject,
    mut v_a_872_: *mut crate::leanh::LeanObject,
    mut v_x_873_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_874_: u8 = 0;
    let mut v_r_875_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_874_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Sat_AIG_RelabelNat_State_addAtom___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux_go___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux___at___00Std_Sat_AIG_RelabelNat_State_ofAIG___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_relabelNat___at___00Std_Sat_AIG_Entrypoint_relabelNat___at___00Std_Tactic_BVDecide_Reflect_verifyBVExpr_spec__0_spec__0_spec__1_spec__2_spec__3_spec__5_spec__9_spec__12_spec__14(v_00_u03b2_871_, v_a_872_, v_x_873_);
    crate::leanh::lean_dec(v_x_873_);
    crate::leanh::lean_dec_ref(v_a_872_);
    v_r_875_ = crate::leanh::lean_box((v_res_874_) as usize);
    return v_r_875_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Sat_AIG_RelabelNat_State_addAtom___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux_go___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux___at___00Std_Sat_AIG_RelabelNat_State_ofAIG___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_relabelNat___at___00Std_Sat_AIG_Entrypoint_relabelNat___at___00Std_Tactic_BVDecide_Reflect_verifyBVExpr_spec__0_spec__0_spec__1_spec__2_spec__3_spec__5_spec__9_spec__12_spec__15(
    mut v_00_u03b2_876_: *mut crate::leanh::LeanObject,
    mut v_data_877_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_878_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_878_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Sat_AIG_RelabelNat_State_addAtom___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux_go___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux___at___00Std_Sat_AIG_RelabelNat_State_ofAIG___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_relabelNat___at___00Std_Sat_AIG_Entrypoint_relabelNat___at___00Std_Tactic_BVDecide_Reflect_verifyBVExpr_spec__0_spec__0_spec__1_spec__2_spec__3_spec__5_spec__9_spec__12_spec__15___redArg(v_data_877_);
    return v___x_878_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Sat_AIG_RelabelNat_State_addAtom___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux_go___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux___at___00Std_Sat_AIG_RelabelNat_State_ofAIG___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_relabelNat___at___00Std_Sat_AIG_Entrypoint_relabelNat___at___00Std_Tactic_BVDecide_Reflect_verifyBVExpr_spec__0_spec__0_spec__1_spec__2_spec__3_spec__5_spec__9_spec__12_spec__16(
    mut v_00_u03b2_879_: *mut crate::leanh::LeanObject,
    mut v_a_880_: *mut crate::leanh::LeanObject,
    mut v_b_881_: *mut crate::leanh::LeanObject,
    mut v_x_882_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_883_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_883_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Sat_AIG_RelabelNat_State_addAtom___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux_go___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux___at___00Std_Sat_AIG_RelabelNat_State_ofAIG___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_relabelNat___at___00Std_Sat_AIG_Entrypoint_relabelNat___at___00Std_Tactic_BVDecide_Reflect_verifyBVExpr_spec__0_spec__0_spec__1_spec__2_spec__3_spec__5_spec__9_spec__12_spec__16___redArg(v_a_880_, v_b_881_, v_x_882_);
    return v___x_883_;
}
pub unsafe fn l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Sat_AIG_RelabelNat_State_addAtom___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux_go___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux___at___00Std_Sat_AIG_RelabelNat_State_ofAIG___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_relabelNat___at___00Std_Sat_AIG_Entrypoint_relabelNat___at___00Std_Tactic_BVDecide_Reflect_verifyBVExpr_spec__0_spec__0_spec__1_spec__2_spec__3_spec__5_spec__9_spec__12_spec__15_spec__16(
    mut v_00_u03b2_884_: *mut crate::leanh::LeanObject,
    mut v_i_885_: *mut crate::leanh::LeanObject,
    mut v_source_886_: *mut crate::leanh::LeanObject,
    mut v_target_887_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_888_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_888_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Sat_AIG_RelabelNat_State_addAtom___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux_go___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux___at___00Std_Sat_AIG_RelabelNat_State_ofAIG___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_relabelNat___at___00Std_Sat_AIG_Entrypoint_relabelNat___at___00Std_Tactic_BVDecide_Reflect_verifyBVExpr_spec__0_spec__0_spec__1_spec__2_spec__3_spec__5_spec__9_spec__12_spec__15_spec__16___redArg(v_i_885_, v_source_886_, v_target_887_);
    return v___x_888_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Sat_AIG_RelabelNat_State_addAtom___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux_go___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux___at___00Std_Sat_AIG_RelabelNat_State_ofAIG___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_relabelNat___at___00Std_Sat_AIG_Entrypoint_relabelNat___at___00Std_Tactic_BVDecide_Reflect_verifyBVExpr_spec__0_spec__0_spec__1_spec__2_spec__3_spec__5_spec__9_spec__12_spec__15_spec__16_spec__17(
    mut v_00_u03b2_889_: *mut crate::leanh::LeanObject,
    mut v_x_890_: *mut crate::leanh::LeanObject,
    mut v_x_891_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_892_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_892_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_Sat_AIG_RelabelNat_State_addAtom___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux_go___at___00Std_Sat_AIG_RelabelNat_State_ofAIGAux___at___00Std_Sat_AIG_RelabelNat_State_ofAIG___at___00Std_Sat_AIG_relabelNat_x27___at___00Std_Sat_AIG_relabelNat___at___00Std_Sat_AIG_Entrypoint_relabelNat___at___00Std_Tactic_BVDecide_Reflect_verifyBVExpr_spec__0_spec__0_spec__1_spec__2_spec__3_spec__5_spec__9_spec__12_spec__15_spec__16_spec__17___redArg(v_x_890_, v_x_891_);
    return v___x_892_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Std_Tactic_BVDecide_Reflect(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Std_Tactic_BVDecide_LRAT_Checker(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Std_Tactic_BVDecide_LRAT_Parser(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Std_Tactic_BVDecide_Bitblast(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Std_Sat_AIG_CNF(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Std_Sat_AIG_RelabelNat(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Std_Tactic_BVDecide_Reflect(
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
pub unsafe fn initialize_Std_Tactic_BVDecide_Reflect(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Std_Tactic_BVDecide_LRAT_Checker(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Std_Tactic_BVDecide_LRAT_Parser(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Std_Tactic_BVDecide_Bitblast(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Std_Sat_AIG_CNF(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Std_Sat_AIG_RelabelNat(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Std_Tactic_BVDecide_Reflect(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Std_Tactic_BVDecide_Reflect(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Std_Tactic_BVDecide_Reflect(builtin);
}
