// Lean compiler output
// Module: Std.Tactic.BVDecide.Bitblast.BVExpr.Circuit.Impl.Operations.Add
// Imports: Std.Tactic.BVDecide.Bitblast.BVExpr.Basic Std.Sat.AIG.LawfulVecOperator Init.Omega
use crate::ffi::{
    lean_array_fget_borrowed, lean_array_push, lean_mk_empty_array_with_capacity, lean_nat_add,
    lean_nat_dec_eq, lean_nat_dec_lt, lean_nat_land, lean_nat_lor, lean_nat_mul, lean_nat_shiftr,
};
use crate::r#gen::Init::Data::Bool::l_Bool_toNat;
use crate::r#gen::Init::Omega::{initialize_Init_Omega, runtime_initialize_Init_Omega};
use crate::r#gen::Std::Sat::AIG::Cached::l_Std_Sat_AIG_mkGateCached___redArg;
use crate::r#gen::Std::Sat::AIG::CachedGates::{
    l_Std_Sat_AIG_mkOrCached___redArg, l_Std_Sat_AIG_mkXorCached___redArg,
};
use crate::r#gen::Std::Sat::AIG::LawfulVecOperator::{
    initialize_Std_Sat_AIG_LawfulVecOperator, runtime_initialize_Std_Sat_AIG_LawfulVecOperator,
};
use crate::r#gen::Std::Sat::AIG::RefVec::l_Std_Sat_AIG_RefVec_countKnown___redArg;
use crate::r#gen::Std::Tactic::BVDecide::Bitblast::BVExpr::Basic::{
    initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Basic,
    runtime_initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Basic,
};
pub static l_Std_Tactic_BVDecide_BVExpr_bitblast_blastAdd_blast___redArg___closed__0_value:
    leanh::LeanCtorObject<2> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 1
            + 8) as u16,
        other: 1,
        tag: 0,
    },
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut leanh::LeanObject,
        0 as *mut leanh::LeanObject,
    ],
};
static mut l_Std_Tactic_BVDecide_BVExpr_bitblast_blastAdd_blast___redArg___closed__0:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Std_Tactic_BVDecide_BVExpr_bitblast_blastAdd_blast___redArg___closed__0_value
) as *mut leanh::LeanObject;
pub unsafe fn l_Std_Tactic_BVDecide_BVExpr_bitblast_FullAdderInput_cast___redArg(
    mut v_val_380_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_lhs_381_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_rhs_382_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_cin_383_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_385_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_386_: u8 = 0;
    let mut v_gate_387_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_invert_388_: u8 = 0;
    let mut v___x_390_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_391_: u8 = 0;
    let mut v_gate_392_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_invert_393_: u8 = 0;
    let mut v___x_395_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_396_: u8 = 0;
    let mut v_gate_397_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_invert_398_: u8 = 0;
    let mut v___x_400_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_401_: u8 = 0;
    let mut v___x_403_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_405_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_407_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_409_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_410_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_411_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_412_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_413_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_414_: u8 = 0;
    let mut v_isSharedCheck_415_: u8 = 0;
    let mut v_isSharedCheck_416_: u8 = 0;
    let mut v_isSharedCheck_417_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_lhs_381_ = leanh::lean_ctor_get(v_val_380_, 0);
                v_rhs_382_ = leanh::lean_ctor_get(v_val_380_, 1);
                v_cin_383_ = leanh::lean_ctor_get(v_val_380_, 2);
                v_isSharedCheck_417_ = (!leanh::lean_is_exclusive(v_val_380_)) as u8;
                if v_isSharedCheck_417_ == 0 {
                    v___x_385_ = v_val_380_;
                    v_isShared_386_ = v_isSharedCheck_417_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_cin_383_);
                    leanh::lean_inc(v_rhs_382_);
                    leanh::lean_inc(v_lhs_381_);
                    leanh::lean_dec(v_val_380_);
                    v___x_385_ = leanh::lean_box(0);
                    v_isShared_386_ = v_isSharedCheck_417_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_gate_387_ = leanh::lean_ctor_get(v_lhs_381_, 0);
                v_invert_388_ = leanh::lean_ctor_get_uint8(
                    v_lhs_381_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                );
                v_isSharedCheck_416_ = (!leanh::lean_is_exclusive(v_lhs_381_)) as u8;
                if v_isSharedCheck_416_ == 0 {
                    v___x_390_ = v_lhs_381_;
                    v_isShared_391_ = v_isSharedCheck_416_;
                    state = 2;
                    continue;
                } else {
                    leanh::lean_inc(v_gate_387_);
                    leanh::lean_dec(v_lhs_381_);
                    v___x_390_ = leanh::lean_box(0);
                    v_isShared_391_ = v_isSharedCheck_416_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v_gate_392_ = leanh::lean_ctor_get(v_rhs_382_, 0);
                v_invert_393_ = leanh::lean_ctor_get_uint8(
                    v_rhs_382_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                );
                v_isSharedCheck_415_ = (!leanh::lean_is_exclusive(v_rhs_382_)) as u8;
                if v_isSharedCheck_415_ == 0 {
                    v___x_395_ = v_rhs_382_;
                    v_isShared_396_ = v_isSharedCheck_415_;
                    state = 3;
                    continue;
                } else {
                    leanh::lean_inc(v_gate_392_);
                    leanh::lean_dec(v_rhs_382_);
                    v___x_395_ = leanh::lean_box(0);
                    v_isShared_396_ = v_isSharedCheck_415_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v_gate_397_ = leanh::lean_ctor_get(v_cin_383_, 0);
                v_invert_398_ = leanh::lean_ctor_get_uint8(
                    v_cin_383_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                );
                v_isSharedCheck_414_ = (!leanh::lean_is_exclusive(v_cin_383_)) as u8;
                if v_isSharedCheck_414_ == 0 {
                    v___x_400_ = v_cin_383_;
                    v_isShared_401_ = v_isSharedCheck_414_;
                    state = 4;
                    continue;
                } else {
                    leanh::lean_inc(v_gate_397_);
                    leanh::lean_dec(v_cin_383_);
                    v___x_400_ = leanh::lean_box(0);
                    v_isShared_401_ = v_isSharedCheck_414_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                if v_isShared_401_ == 0 {
                    leanh::lean_ctor_set(v___x_400_, 0, v_gate_387_);
                    v___x_403_ = v___x_400_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_413_ = leanh::lean_alloc_ctor(0, 1, (1) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_413_, 0, v_gate_387_);
                    v___x_403_ = v_reuseFailAlloc_413_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                leanh::lean_ctor_set_uint8(
                    v___x_403_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                    v_invert_388_,
                );
                if v_isShared_396_ == 0 {
                    v___x_405_ = v___x_395_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_412_ = leanh::lean_alloc_ctor(0, 1, (1) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_412_, 0, v_gate_392_);
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_412_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                        v_invert_393_,
                    );
                    v___x_405_ = v_reuseFailAlloc_412_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                if v_isShared_391_ == 0 {
                    leanh::lean_ctor_set(v___x_390_, 0, v_gate_397_);
                    v___x_407_ = v___x_390_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_411_ = leanh::lean_alloc_ctor(0, 1, (1) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_411_, 0, v_gate_397_);
                    v___x_407_ = v_reuseFailAlloc_411_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                leanh::lean_ctor_set_uint8(
                    v___x_407_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                    v_invert_398_,
                );
                if v_isShared_386_ == 0 {
                    leanh::lean_ctor_set(v___x_385_, 2, v___x_407_);
                    leanh::lean_ctor_set(v___x_385_, 1, v___x_405_);
                    leanh::lean_ctor_set(v___x_385_, 0, v___x_403_);
                    v___x_409_ = v___x_385_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_410_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_410_, 0, v___x_403_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_410_, 1, v___x_405_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_410_, 2, v___x_407_);
                    v___x_409_ = v_reuseFailAlloc_410_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_409_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Tactic_BVDecide_BVExpr_bitblast_FullAdderInput_cast(
    mut v_00_u03b1_418_: *mut leanh::LeanObject,
    mut v_inst_419_: *mut leanh::LeanObject,
    mut v_inst_420_: *mut leanh::LeanObject,
    mut v_aig1_421_: *mut leanh::LeanObject,
    mut v_aig2_422_: *mut leanh::LeanObject,
    mut v_val_423_: *mut leanh::LeanObject,
    mut v_h_424_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_425_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_425_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_FullAdderInput_cast___redArg(v_val_423_);
    return v___x_425_;
}
pub unsafe fn l_Std_Tactic_BVDecide_BVExpr_bitblast_FullAdderInput_cast___boxed(
    mut v_00_u03b1_426_: *mut leanh::LeanObject,
    mut v_inst_427_: *mut leanh::LeanObject,
    mut v_inst_428_: *mut leanh::LeanObject,
    mut v_aig1_429_: *mut leanh::LeanObject,
    mut v_aig2_430_: *mut leanh::LeanObject,
    mut v_val_431_: *mut leanh::LeanObject,
    mut v_h_432_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_433_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_433_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_FullAdderInput_cast(
        v_00_u03b1_426_,
        v_inst_427_,
        v_inst_428_,
        v_aig1_429_,
        v_aig2_430_,
        v_val_431_,
        v_h_432_,
    );
    leanh::lean_dec_ref(v_aig2_430_);
    leanh::lean_dec_ref(v_aig1_429_);
    leanh::lean_dec_ref(v_inst_428_);
    leanh::lean_dec_ref(v_inst_427_);
    return v_res_433_;
}
pub unsafe fn l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Operations_Add_0__Std_Tactic_BVDecide_BVExpr_bitblast_FullAdderInput_cast_match__1_splitter___redArg(
    mut v_val_434_: *mut leanh::LeanObject,
    mut v_h__1_435_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_lhs_436_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_rhs_437_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_cin_438_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_439_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_lhs_436_ = leanh::lean_ctor_get(v_val_434_, 0);
    leanh::lean_inc_ref(v_lhs_436_);
    v_rhs_437_ = leanh::lean_ctor_get(v_val_434_, 1);
    leanh::lean_inc_ref(v_rhs_437_);
    v_cin_438_ = leanh::lean_ctor_get(v_val_434_, 2);
    leanh::lean_inc_ref(v_cin_438_);
    leanh::lean_dec_ref(v_val_434_);
    v___x_439_ = leanh::lean_apply_3(v_h__1_435_, v_lhs_436_, v_rhs_437_, v_cin_438_);
    return v___x_439_;
}
pub unsafe fn l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Operations_Add_0__Std_Tactic_BVDecide_BVExpr_bitblast_FullAdderInput_cast_match__1_splitter(
    mut v_00_u03b1_440_: *mut leanh::LeanObject,
    mut v_inst_441_: *mut leanh::LeanObject,
    mut v_inst_442_: *mut leanh::LeanObject,
    mut v_aig1_443_: *mut leanh::LeanObject,
    mut v_motive_444_: *mut leanh::LeanObject,
    mut v_val_445_: *mut leanh::LeanObject,
    mut v_h__1_446_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_lhs_447_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_rhs_448_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_cin_449_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_450_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_lhs_447_ = leanh::lean_ctor_get(v_val_445_, 0);
    leanh::lean_inc_ref(v_lhs_447_);
    v_rhs_448_ = leanh::lean_ctor_get(v_val_445_, 1);
    leanh::lean_inc_ref(v_rhs_448_);
    v_cin_449_ = leanh::lean_ctor_get(v_val_445_, 2);
    leanh::lean_inc_ref(v_cin_449_);
    leanh::lean_dec_ref(v_val_445_);
    v___x_450_ = leanh::lean_apply_3(v_h__1_446_, v_lhs_447_, v_rhs_448_, v_cin_449_);
    return v___x_450_;
}
pub unsafe fn l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Operations_Add_0__Std_Tactic_BVDecide_BVExpr_bitblast_FullAdderInput_cast_match__1_splitter___boxed(
    mut v_00_u03b1_451_: *mut leanh::LeanObject,
    mut v_inst_452_: *mut leanh::LeanObject,
    mut v_inst_453_: *mut leanh::LeanObject,
    mut v_aig1_454_: *mut leanh::LeanObject,
    mut v_motive_455_: *mut leanh::LeanObject,
    mut v_val_456_: *mut leanh::LeanObject,
    mut v_h__1_457_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_458_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_458_ = l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Operations_Add_0__Std_Tactic_BVDecide_BVExpr_bitblast_FullAdderInput_cast_match__1_splitter(v_00_u03b1_451_, v_inst_452_, v_inst_453_, v_aig1_454_, v_motive_455_, v_val_456_, v_h__1_457_);
    leanh::lean_dec_ref(v_aig1_454_);
    leanh::lean_dec_ref(v_inst_453_);
    leanh::lean_dec_ref(v_inst_452_);
    return v_res_458_;
}
pub unsafe fn l_Std_Tactic_BVDecide_BVExpr_bitblast_mkFullAdderOut___redArg(
    mut v_inst_459_: *mut leanh::LeanObject,
    mut v_inst_460_: *mut leanh::LeanObject,
    mut v_aig_461_: *mut leanh::LeanObject,
    mut v_input_462_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_lhs_463_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_rhs_464_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_cin_465_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_466_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_res_467_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_aig_468_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_469_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_471_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_472_: u8 = 0;
    let mut v_gate_473_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_invert_474_: u8 = 0;
    let mut v___x_476_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_477_: u8 = 0;
    let mut v_cin_479_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_481_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_482_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_483_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_484_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_485_: u8 = 0;
    let mut v_isSharedCheck_486_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_lhs_463_ = leanh::lean_ctor_get(v_input_462_, 0);
                leanh::lean_inc_ref(v_lhs_463_);
                v_rhs_464_ = leanh::lean_ctor_get(v_input_462_, 1);
                leanh::lean_inc_ref(v_rhs_464_);
                v_cin_465_ = leanh::lean_ctor_get(v_input_462_, 2);
                leanh::lean_inc_ref(v_cin_465_);
                leanh::lean_dec_ref(v_input_462_);
                v___x_466_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_466_, 0, v_lhs_463_);
                leanh::lean_ctor_set(v___x_466_, 1, v_rhs_464_);
                leanh::lean_inc_ref(v_inst_460_);
                leanh::lean_inc_ref(v_inst_459_);
                v_res_467_ = l_Std_Sat_AIG_mkXorCached___redArg(
                    v_inst_459_,
                    v_inst_460_,
                    v_aig_461_,
                    v___x_466_,
                );
                v_aig_468_ = leanh::lean_ctor_get(v_res_467_, 0);
                v_ref_469_ = leanh::lean_ctor_get(v_res_467_, 1);
                v_isSharedCheck_486_ = (!leanh::lean_is_exclusive(v_res_467_)) as u8;
                if v_isSharedCheck_486_ == 0 {
                    v___x_471_ = v_res_467_;
                    v_isShared_472_ = v_isSharedCheck_486_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_ref_469_);
                    leanh::lean_inc(v_aig_468_);
                    leanh::lean_dec(v_res_467_);
                    v___x_471_ = leanh::lean_box(0);
                    v_isShared_472_ = v_isSharedCheck_486_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_gate_473_ = leanh::lean_ctor_get(v_cin_465_, 0);
                v_invert_474_ = leanh::lean_ctor_get_uint8(
                    v_cin_465_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                );
                v_isSharedCheck_485_ = (!leanh::lean_is_exclusive(v_cin_465_)) as u8;
                if v_isSharedCheck_485_ == 0 {
                    v___x_476_ = v_cin_465_;
                    v_isShared_477_ = v_isSharedCheck_485_;
                    state = 2;
                    continue;
                } else {
                    leanh::lean_inc(v_gate_473_);
                    leanh::lean_dec(v_cin_465_);
                    v___x_476_ = leanh::lean_box(0);
                    v_isShared_477_ = v_isSharedCheck_485_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                if v_isShared_477_ == 0 {
                    v_cin_479_ = v___x_476_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_484_ = leanh::lean_alloc_ctor(0, 1, (1) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_484_, 0, v_gate_473_);
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_484_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                        v_invert_474_,
                    );
                    v_cin_479_ = v_reuseFailAlloc_484_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_472_ == 0 {
                    leanh::lean_ctor_set(v___x_471_, 1, v_cin_479_);
                    leanh::lean_ctor_set(v___x_471_, 0, v_ref_469_);
                    v___x_481_ = v___x_471_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_483_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_483_, 0, v_ref_469_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_483_, 1, v_cin_479_);
                    v___x_481_ = v_reuseFailAlloc_483_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_482_ = l_Std_Sat_AIG_mkXorCached___redArg(
                    v_inst_459_,
                    v_inst_460_,
                    v_aig_468_,
                    v___x_481_,
                );
                return v___x_482_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Tactic_BVDecide_BVExpr_bitblast_mkFullAdderOut(
    mut v_00_u03b1_487_: *mut leanh::LeanObject,
    mut v_inst_488_: *mut leanh::LeanObject,
    mut v_inst_489_: *mut leanh::LeanObject,
    mut v_aig_490_: *mut leanh::LeanObject,
    mut v_input_491_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_492_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_492_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_mkFullAdderOut___redArg(
        v_inst_488_,
        v_inst_489_,
        v_aig_490_,
        v_input_491_,
    );
    return v___x_492_;
}
pub unsafe fn l_Std_Tactic_BVDecide_BVExpr_bitblast_mkFullAdderCarry___redArg(
    mut v_inst_493_: *mut leanh::LeanObject,
    mut v_inst_494_: *mut leanh::LeanObject,
    mut v_aig_495_: *mut leanh::LeanObject,
    mut v_input_496_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_lhs_497_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_rhs_498_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_cin_499_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_500_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_res_501_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_aig_502_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_503_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_505_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_506_: u8 = 0;
    let mut v_gate_507_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_invert_508_: u8 = 0;
    let mut v___x_510_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_511_: u8 = 0;
    let mut v_gate_512_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_invert_513_: u8 = 0;
    let mut v___x_515_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_516_: u8 = 0;
    let mut v_gate_517_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_invert_518_: u8 = 0;
    let mut v___x_520_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_521_: u8 = 0;
    let mut v_cin_523_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_525_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_res_526_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_aig_527_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_528_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_530_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_531_: u8 = 0;
    let mut v_lhs_533_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_rhs_535_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_537_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_res_538_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_aig_539_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_540_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_542_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_543_: u8 = 0;
    let mut v_gate_544_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_invert_545_: u8 = 0;
    let mut v___x_547_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_548_: u8 = 0;
    let mut v_lorRef_550_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_552_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_553_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_554_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_555_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_556_: u8 = 0;
    let mut v_isSharedCheck_557_: u8 = 0;
    let mut v_reuseFailAlloc_558_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_559_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_560_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_561_: u8 = 0;
    let mut v_reuseFailAlloc_562_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_563_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_564_: u8 = 0;
    let mut v_isSharedCheck_565_: u8 = 0;
    let mut v_isSharedCheck_566_: u8 = 0;
    let mut v_isSharedCheck_567_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_lhs_497_ = leanh::lean_ctor_get(v_input_496_, 0);
                leanh::lean_inc_ref_n(v_lhs_497_, 2);
                v_rhs_498_ = leanh::lean_ctor_get(v_input_496_, 1);
                leanh::lean_inc_ref_n(v_rhs_498_, 2);
                v_cin_499_ = leanh::lean_ctor_get(v_input_496_, 2);
                leanh::lean_inc_ref(v_cin_499_);
                leanh::lean_dec_ref(v_input_496_);
                v___x_500_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_500_, 0, v_lhs_497_);
                leanh::lean_ctor_set(v___x_500_, 1, v_rhs_498_);
                leanh::lean_inc_ref(v_inst_494_);
                leanh::lean_inc_ref(v_inst_493_);
                v_res_501_ = l_Std_Sat_AIG_mkXorCached___redArg(
                    v_inst_493_,
                    v_inst_494_,
                    v_aig_495_,
                    v___x_500_,
                );
                v_aig_502_ = leanh::lean_ctor_get(v_res_501_, 0);
                v_ref_503_ = leanh::lean_ctor_get(v_res_501_, 1);
                v_isSharedCheck_567_ = (!leanh::lean_is_exclusive(v_res_501_)) as u8;
                if v_isSharedCheck_567_ == 0 {
                    v___x_505_ = v_res_501_;
                    v_isShared_506_ = v_isSharedCheck_567_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_ref_503_);
                    leanh::lean_inc(v_aig_502_);
                    leanh::lean_dec(v_res_501_);
                    v___x_505_ = leanh::lean_box(0);
                    v_isShared_506_ = v_isSharedCheck_567_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_gate_507_ = leanh::lean_ctor_get(v_lhs_497_, 0);
                v_invert_508_ = leanh::lean_ctor_get_uint8(
                    v_lhs_497_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                );
                v_isSharedCheck_566_ = (!leanh::lean_is_exclusive(v_lhs_497_)) as u8;
                if v_isSharedCheck_566_ == 0 {
                    v___x_510_ = v_lhs_497_;
                    v_isShared_511_ = v_isSharedCheck_566_;
                    state = 2;
                    continue;
                } else {
                    leanh::lean_inc(v_gate_507_);
                    leanh::lean_dec(v_lhs_497_);
                    v___x_510_ = leanh::lean_box(0);
                    v_isShared_511_ = v_isSharedCheck_566_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v_gate_512_ = leanh::lean_ctor_get(v_rhs_498_, 0);
                v_invert_513_ = leanh::lean_ctor_get_uint8(
                    v_rhs_498_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                );
                v_isSharedCheck_565_ = (!leanh::lean_is_exclusive(v_rhs_498_)) as u8;
                if v_isSharedCheck_565_ == 0 {
                    v___x_515_ = v_rhs_498_;
                    v_isShared_516_ = v_isSharedCheck_565_;
                    state = 3;
                    continue;
                } else {
                    leanh::lean_inc(v_gate_512_);
                    leanh::lean_dec(v_rhs_498_);
                    v___x_515_ = leanh::lean_box(0);
                    v_isShared_516_ = v_isSharedCheck_565_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v_gate_517_ = leanh::lean_ctor_get(v_cin_499_, 0);
                v_invert_518_ = leanh::lean_ctor_get_uint8(
                    v_cin_499_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                );
                v_isSharedCheck_564_ = (!leanh::lean_is_exclusive(v_cin_499_)) as u8;
                if v_isSharedCheck_564_ == 0 {
                    v___x_520_ = v_cin_499_;
                    v_isShared_521_ = v_isSharedCheck_564_;
                    state = 4;
                    continue;
                } else {
                    leanh::lean_inc(v_gate_517_);
                    leanh::lean_dec(v_cin_499_);
                    v___x_520_ = leanh::lean_box(0);
                    v_isShared_521_ = v_isSharedCheck_564_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                if v_isShared_521_ == 0 {
                    v_cin_523_ = v___x_520_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_563_ = leanh::lean_alloc_ctor(0, 1, (1) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_563_, 0, v_gate_517_);
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_563_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                        v_invert_518_,
                    );
                    v_cin_523_ = v_reuseFailAlloc_563_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                if v_isShared_506_ == 0 {
                    leanh::lean_ctor_set(v___x_505_, 1, v_cin_523_);
                    leanh::lean_ctor_set(v___x_505_, 0, v_ref_503_);
                    v___x_525_ = v___x_505_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_562_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_562_, 0, v_ref_503_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_562_, 1, v_cin_523_);
                    v___x_525_ = v_reuseFailAlloc_562_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                leanh::lean_inc_ref(v_inst_494_);
                leanh::lean_inc_ref(v_inst_493_);
                v_res_526_ = l_Std_Sat_AIG_mkGateCached___redArg(
                    v_inst_493_,
                    v_inst_494_,
                    v_aig_502_,
                    v___x_525_,
                );
                v_aig_527_ = leanh::lean_ctor_get(v_res_526_, 0);
                v_ref_528_ = leanh::lean_ctor_get(v_res_526_, 1);
                v_isSharedCheck_561_ = (!leanh::lean_is_exclusive(v_res_526_)) as u8;
                if v_isSharedCheck_561_ == 0 {
                    v___x_530_ = v_res_526_;
                    v_isShared_531_ = v_isSharedCheck_561_;
                    state = 7;
                    continue;
                } else {
                    leanh::lean_inc(v_ref_528_);
                    leanh::lean_inc(v_aig_527_);
                    leanh::lean_dec(v_res_526_);
                    v___x_530_ = leanh::lean_box(0);
                    v_isShared_531_ = v_isSharedCheck_561_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                if v_isShared_516_ == 0 {
                    leanh::lean_ctor_set(v___x_515_, 0, v_gate_507_);
                    v_lhs_533_ = v___x_515_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_560_ = leanh::lean_alloc_ctor(0, 1, (1) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_560_, 0, v_gate_507_);
                    v_lhs_533_ = v_reuseFailAlloc_560_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                leanh::lean_ctor_set_uint8(
                    v_lhs_533_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                    v_invert_508_,
                );
                if v_isShared_511_ == 0 {
                    leanh::lean_ctor_set(v___x_510_, 0, v_gate_512_);
                    v_rhs_535_ = v___x_510_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_559_ = leanh::lean_alloc_ctor(0, 1, (1) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_559_, 0, v_gate_512_);
                    v_rhs_535_ = v_reuseFailAlloc_559_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                leanh::lean_ctor_set_uint8(
                    v_rhs_535_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                    v_invert_513_,
                );
                if v_isShared_531_ == 0 {
                    leanh::lean_ctor_set(v___x_530_, 1, v_rhs_535_);
                    leanh::lean_ctor_set(v___x_530_, 0, v_lhs_533_);
                    v___x_537_ = v___x_530_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_558_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_558_, 0, v_lhs_533_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_558_, 1, v_rhs_535_);
                    v___x_537_ = v_reuseFailAlloc_558_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                leanh::lean_inc_ref(v_inst_494_);
                leanh::lean_inc_ref(v_inst_493_);
                v_res_538_ = l_Std_Sat_AIG_mkGateCached___redArg(
                    v_inst_493_,
                    v_inst_494_,
                    v_aig_527_,
                    v___x_537_,
                );
                v_aig_539_ = leanh::lean_ctor_get(v_res_538_, 0);
                v_ref_540_ = leanh::lean_ctor_get(v_res_538_, 1);
                v_isSharedCheck_557_ = (!leanh::lean_is_exclusive(v_res_538_)) as u8;
                if v_isSharedCheck_557_ == 0 {
                    v___x_542_ = v_res_538_;
                    v_isShared_543_ = v_isSharedCheck_557_;
                    state = 11;
                    continue;
                } else {
                    leanh::lean_inc(v_ref_540_);
                    leanh::lean_inc(v_aig_539_);
                    leanh::lean_dec(v_res_538_);
                    v___x_542_ = leanh::lean_box(0);
                    v_isShared_543_ = v_isSharedCheck_557_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                v_gate_544_ = leanh::lean_ctor_get(v_ref_528_, 0);
                v_invert_545_ = leanh::lean_ctor_get_uint8(
                    v_ref_528_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                );
                v_isSharedCheck_556_ = (!leanh::lean_is_exclusive(v_ref_528_)) as u8;
                if v_isSharedCheck_556_ == 0 {
                    v___x_547_ = v_ref_528_;
                    v_isShared_548_ = v_isSharedCheck_556_;
                    state = 12;
                    continue;
                } else {
                    leanh::lean_inc(v_gate_544_);
                    leanh::lean_dec(v_ref_528_);
                    v___x_547_ = leanh::lean_box(0);
                    v_isShared_548_ = v_isSharedCheck_556_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                if v_isShared_548_ == 0 {
                    v_lorRef_550_ = v___x_547_;
                    state = 13;
                    continue;
                } else {
                    v_reuseFailAlloc_555_ = leanh::lean_alloc_ctor(0, 1, (1) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_555_, 0, v_gate_544_);
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_555_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                        v_invert_545_,
                    );
                    v_lorRef_550_ = v_reuseFailAlloc_555_;
                    state = 13;
                    continue;
                }
            }
            13 => {
                if v_isShared_543_ == 0 {
                    leanh::lean_ctor_set(v___x_542_, 0, v_lorRef_550_);
                    v___x_552_ = v___x_542_;
                    state = 14;
                    continue;
                } else {
                    v_reuseFailAlloc_554_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_554_, 0, v_lorRef_550_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_554_, 1, v_ref_540_);
                    v___x_552_ = v_reuseFailAlloc_554_;
                    state = 14;
                    continue;
                }
            }
            14 => {
                v___x_553_ = l_Std_Sat_AIG_mkOrCached___redArg(
                    v_inst_493_,
                    v_inst_494_,
                    v_aig_539_,
                    v___x_552_,
                );
                return v___x_553_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Tactic_BVDecide_BVExpr_bitblast_mkFullAdderCarry(
    mut v_00_u03b1_568_: *mut leanh::LeanObject,
    mut v_inst_569_: *mut leanh::LeanObject,
    mut v_inst_570_: *mut leanh::LeanObject,
    mut v_aig_571_: *mut leanh::LeanObject,
    mut v_input_572_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_573_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_573_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_mkFullAdderCarry___redArg(
        v_inst_569_,
        v_inst_570_,
        v_aig_571_,
        v_input_572_,
    );
    return v___x_573_;
}
pub unsafe fn l_Std_Tactic_BVDecide_BVExpr_bitblast_mkFullAdder___redArg(
    mut v_inst_574_: *mut leanh::LeanObject,
    mut v_inst_575_: *mut leanh::LeanObject,
    mut v_aig_576_: *mut leanh::LeanObject,
    mut v_input_577_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_578_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_aig_579_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_580_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_input_581_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_res_582_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_aig_583_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_584_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_gate_585_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_invert_586_: u8 = 0;
    let mut v___x_588_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_589_: u8 = 0;
    let mut v_outRef_591_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_592_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_593_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_594_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                leanh::lean_inc_ref(v_input_577_);
                leanh::lean_inc_ref(v_inst_575_);
                leanh::lean_inc_ref(v_inst_574_);
                v_res_578_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_mkFullAdderOut___redArg(
                    v_inst_574_,
                    v_inst_575_,
                    v_aig_576_,
                    v_input_577_,
                );
                v_aig_579_ = leanh::lean_ctor_get(v_res_578_, 0);
                leanh::lean_inc_ref(v_aig_579_);
                v_ref_580_ = leanh::lean_ctor_get(v_res_578_, 1);
                leanh::lean_inc_ref(v_ref_580_);
                leanh::lean_dec_ref(v_res_578_);
                v_input_581_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_FullAdderInput_cast___redArg(
                    v_input_577_,
                );
                v_res_582_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_mkFullAdderCarry___redArg(
                    v_inst_574_,
                    v_inst_575_,
                    v_aig_579_,
                    v_input_581_,
                );
                v_aig_583_ = leanh::lean_ctor_get(v_res_582_, 0);
                leanh::lean_inc_ref(v_aig_583_);
                v_ref_584_ = leanh::lean_ctor_get(v_res_582_, 1);
                leanh::lean_inc_ref(v_ref_584_);
                leanh::lean_dec_ref(v_res_582_);
                v_gate_585_ = leanh::lean_ctor_get(v_ref_580_, 0);
                v_invert_586_ = leanh::lean_ctor_get_uint8(
                    v_ref_580_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                );
                v_isSharedCheck_594_ = (!leanh::lean_is_exclusive(v_ref_580_)) as u8;
                if v_isSharedCheck_594_ == 0 {
                    v___x_588_ = v_ref_580_;
                    v_isShared_589_ = v_isSharedCheck_594_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_gate_585_);
                    leanh::lean_dec(v_ref_580_);
                    v___x_588_ = leanh::lean_box(0);
                    v_isShared_589_ = v_isSharedCheck_594_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                if v_isShared_589_ == 0 {
                    v_outRef_591_ = v___x_588_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_593_ = leanh::lean_alloc_ctor(0, 1, (1) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_593_, 0, v_gate_585_);
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_593_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                        v_invert_586_,
                    );
                    v_outRef_591_ = v_reuseFailAlloc_593_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_592_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
                leanh::lean_ctor_set(v___x_592_, 0, v_aig_583_);
                leanh::lean_ctor_set(v___x_592_, 1, v_outRef_591_);
                leanh::lean_ctor_set(v___x_592_, 2, v_ref_584_);
                return v___x_592_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Tactic_BVDecide_BVExpr_bitblast_mkFullAdder(
    mut v_00_u03b1_595_: *mut leanh::LeanObject,
    mut v_inst_596_: *mut leanh::LeanObject,
    mut v_inst_597_: *mut leanh::LeanObject,
    mut v_aig_598_: *mut leanh::LeanObject,
    mut v_input_599_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_600_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_600_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_mkFullAdder___redArg(
        v_inst_596_,
        v_inst_597_,
        v_aig_598_,
        v_input_599_,
    );
    return v___x_600_;
}
pub unsafe fn l_Std_Tactic_BVDecide_BVExpr_bitblast_blastAdd_go___redArg(
    mut v_inst_601_: *mut leanh::LeanObject,
    mut v_inst_602_: *mut leanh::LeanObject,
    mut v_w_603_: *mut leanh::LeanObject,
    mut v_aig_604_: *mut leanh::LeanObject,
    mut v_lhs_605_: *mut leanh::LeanObject,
    mut v_rhs_606_: *mut leanh::LeanObject,
    mut v_curr_607_: *mut leanh::LeanObject,
    mut v_cin_608_: *mut leanh::LeanObject,
    mut v_s_609_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___y_611_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_612_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_613_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_res_614_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_out_615_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_aig_616_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_cout_617_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_gate_618_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_invert_619_: u8 = 0;
    let mut v___x_620_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_621_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_622_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_623_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_624_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_625_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_s_626_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_628_: u8 = 0;
    let mut v___y_630_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_631_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_632_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_633_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_634_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_635_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_636_: u8 = 0;
    let mut v___x_637_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_638_: u8 = 0;
    let mut v___x_639_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_640_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_641_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_642_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_643_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_644_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_645_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_646_: u8 = 0;
    let mut v___x_647_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_648_: u8 = 0;
    let mut v___x_649_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_628_ = lean_nat_dec_lt(v_curr_607_, v_w_603_);
                if v___x_628_ == 0 {
                    leanh::lean_dec_ref(v_cin_608_);
                    leanh::lean_dec(v_curr_607_);
                    leanh::lean_dec_ref(v_inst_602_);
                    leanh::lean_dec_ref(v_inst_601_);
                    v___x_640_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_640_, 0, v_aig_604_);
                    leanh::lean_ctor_set(v___x_640_, 1, v_s_609_);
                    return v___x_640_;
                } else {
                    v_ref_641_ = lean_array_fget_borrowed(v_lhs_605_, v_curr_607_);
                    v___x_642_ = leanh::lean_unsigned_to_nat(1);
                    v___x_643_ = lean_nat_shiftr(v_ref_641_, v___x_642_);
                    v___x_644_ = lean_nat_land(v___x_642_, v_ref_641_);
                    v___x_645_ = leanh::lean_unsigned_to_nat(0);
                    v___x_646_ = lean_nat_dec_eq(v___x_644_, v___x_645_);
                    leanh::lean_dec(v___x_644_);
                    if v___x_646_ == 0 {
                        v___x_647_ = leanh::lean_alloc_ctor(0, 1, (1) as u32);
                        leanh::lean_ctor_set(v___x_647_, 0, v___x_643_);
                        leanh::lean_ctor_set_uint8(
                            v___x_647_,
                            (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                            v___x_628_,
                        );
                        v___y_630_ = v___x_647_;
                        state = 2;
                        continue;
                    } else {
                        v___x_648_ = 0;
                        v___x_649_ = leanh::lean_alloc_ctor(0, 1, (1) as u32);
                        leanh::lean_ctor_set(v___x_649_, 0, v___x_643_);
                        leanh::lean_ctor_set_uint8(
                            v___x_649_,
                            (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                            v___x_648_,
                        );
                        v___y_630_ = v___x_649_;
                        state = 2;
                        continue;
                    }
                }
            }
            1 => {
                v___x_613_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
                leanh::lean_ctor_set(v___x_613_, 0, v___y_611_);
                leanh::lean_ctor_set(v___x_613_, 1, v___y_612_);
                leanh::lean_ctor_set(v___x_613_, 2, v_cin_608_);
                leanh::lean_inc_ref(v_inst_602_);
                leanh::lean_inc_ref(v_inst_601_);
                v_res_614_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_mkFullAdder___redArg(
                    v_inst_601_,
                    v_inst_602_,
                    v_aig_604_,
                    v___x_613_,
                );
                v_out_615_ = leanh::lean_ctor_get(v_res_614_, 1);
                leanh::lean_inc_ref(v_out_615_);
                v_aig_616_ = leanh::lean_ctor_get(v_res_614_, 0);
                leanh::lean_inc_ref(v_aig_616_);
                v_cout_617_ = leanh::lean_ctor_get(v_res_614_, 2);
                leanh::lean_inc_ref(v_cout_617_);
                leanh::lean_dec_ref(v_res_614_);
                v_gate_618_ = leanh::lean_ctor_get(v_out_615_, 0);
                leanh::lean_inc(v_gate_618_);
                v_invert_619_ = leanh::lean_ctor_get_uint8(
                    v_out_615_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                );
                leanh::lean_dec_ref(v_out_615_);
                v___x_620_ = leanh::lean_unsigned_to_nat(1);
                v___x_621_ = lean_nat_add(v_curr_607_, v___x_620_);
                leanh::lean_dec(v_curr_607_);
                v___x_622_ = leanh::lean_unsigned_to_nat(2);
                v___x_623_ = lean_nat_mul(v_gate_618_, v___x_622_);
                leanh::lean_dec(v_gate_618_);
                v___x_624_ = l_Bool_toNat(v_invert_619_);
                v___x_625_ = lean_nat_lor(v___x_623_, v___x_624_);
                leanh::lean_dec(v___x_624_);
                leanh::lean_dec(v___x_623_);
                v_s_626_ = lean_array_push(v_s_609_, v___x_625_);
                v_aig_604_ = v_aig_616_;
                v_curr_607_ = v___x_621_;
                v_cin_608_ = v_cout_617_;
                v_s_609_ = v_s_626_;
                state = 0;
                continue;
            }
            2 => {
                v_ref_631_ = lean_array_fget_borrowed(v_rhs_606_, v_curr_607_);
                v___x_632_ = leanh::lean_unsigned_to_nat(1);
                v___x_633_ = lean_nat_shiftr(v_ref_631_, v___x_632_);
                v___x_634_ = lean_nat_land(v___x_632_, v_ref_631_);
                v___x_635_ = leanh::lean_unsigned_to_nat(0);
                v___x_636_ = lean_nat_dec_eq(v___x_634_, v___x_635_);
                leanh::lean_dec(v___x_634_);
                if v___x_636_ == 0 {
                    v___x_637_ = leanh::lean_alloc_ctor(0, 1, (1) as u32);
                    leanh::lean_ctor_set(v___x_637_, 0, v___x_633_);
                    leanh::lean_ctor_set_uint8(
                        v___x_637_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                        v___x_628_,
                    );
                    v___y_611_ = v___y_630_;
                    v___y_612_ = v___x_637_;
                    state = 1;
                    continue;
                } else {
                    v___x_638_ = 0;
                    v___x_639_ = leanh::lean_alloc_ctor(0, 1, (1) as u32);
                    leanh::lean_ctor_set(v___x_639_, 0, v___x_633_);
                    leanh::lean_ctor_set_uint8(
                        v___x_639_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                        v___x_638_,
                    );
                    v___y_611_ = v___y_630_;
                    v___y_612_ = v___x_639_;
                    state = 1;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Tactic_BVDecide_BVExpr_bitblast_blastAdd_go___redArg___boxed(
    mut v_inst_650_: *mut leanh::LeanObject,
    mut v_inst_651_: *mut leanh::LeanObject,
    mut v_w_652_: *mut leanh::LeanObject,
    mut v_aig_653_: *mut leanh::LeanObject,
    mut v_lhs_654_: *mut leanh::LeanObject,
    mut v_rhs_655_: *mut leanh::LeanObject,
    mut v_curr_656_: *mut leanh::LeanObject,
    mut v_cin_657_: *mut leanh::LeanObject,
    mut v_s_658_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_659_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_659_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastAdd_go___redArg(
        v_inst_650_,
        v_inst_651_,
        v_w_652_,
        v_aig_653_,
        v_lhs_654_,
        v_rhs_655_,
        v_curr_656_,
        v_cin_657_,
        v_s_658_,
    );
    leanh::lean_dec_ref(v_rhs_655_);
    leanh::lean_dec_ref(v_lhs_654_);
    leanh::lean_dec(v_w_652_);
    return v_res_659_;
}
pub unsafe fn l_Std_Tactic_BVDecide_BVExpr_bitblast_blastAdd_go(
    mut v_00_u03b1_660_: *mut leanh::LeanObject,
    mut v_inst_661_: *mut leanh::LeanObject,
    mut v_inst_662_: *mut leanh::LeanObject,
    mut v_w_663_: *mut leanh::LeanObject,
    mut v_aig_664_: *mut leanh::LeanObject,
    mut v_lhs_665_: *mut leanh::LeanObject,
    mut v_rhs_666_: *mut leanh::LeanObject,
    mut v_curr_667_: *mut leanh::LeanObject,
    mut v_hcurr_668_: *mut leanh::LeanObject,
    mut v_cin_669_: *mut leanh::LeanObject,
    mut v_s_670_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_671_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_671_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastAdd_go___redArg(
        v_inst_661_,
        v_inst_662_,
        v_w_663_,
        v_aig_664_,
        v_lhs_665_,
        v_rhs_666_,
        v_curr_667_,
        v_cin_669_,
        v_s_670_,
    );
    return v___x_671_;
}
pub unsafe fn l_Std_Tactic_BVDecide_BVExpr_bitblast_blastAdd_go___boxed(
    mut v_00_u03b1_672_: *mut leanh::LeanObject,
    mut v_inst_673_: *mut leanh::LeanObject,
    mut v_inst_674_: *mut leanh::LeanObject,
    mut v_w_675_: *mut leanh::LeanObject,
    mut v_aig_676_: *mut leanh::LeanObject,
    mut v_lhs_677_: *mut leanh::LeanObject,
    mut v_rhs_678_: *mut leanh::LeanObject,
    mut v_curr_679_: *mut leanh::LeanObject,
    mut v_hcurr_680_: *mut leanh::LeanObject,
    mut v_cin_681_: *mut leanh::LeanObject,
    mut v_s_682_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_683_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_683_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastAdd_go(
        v_00_u03b1_672_,
        v_inst_673_,
        v_inst_674_,
        v_w_675_,
        v_aig_676_,
        v_lhs_677_,
        v_rhs_678_,
        v_curr_679_,
        v_hcurr_680_,
        v_cin_681_,
        v_s_682_,
    );
    leanh::lean_dec_ref(v_rhs_678_);
    leanh::lean_dec_ref(v_lhs_677_);
    leanh::lean_dec(v_w_675_);
    return v_res_683_;
}
pub unsafe fn l_Std_Tactic_BVDecide_BVExpr_bitblast_blastAdd_blast___redArg(
    mut v_inst_687_: *mut leanh::LeanObject,
    mut v_inst_688_: *mut leanh::LeanObject,
    mut v_w_689_: *mut leanh::LeanObject,
    mut v_aig_690_: *mut leanh::LeanObject,
    mut v_input_691_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_lhs_692_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_rhs_693_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_694_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_cin_695_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_696_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_697_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_lhs_692_ = leanh::lean_ctor_get(v_input_691_, 0);
    v_rhs_693_ = leanh::lean_ctor_get(v_input_691_, 1);
    v___x_694_ = leanh::lean_unsigned_to_nat(0);
    v_cin_695_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastAdd_blast___redArg___closed__0;
    v___x_696_ = lean_mk_empty_array_with_capacity(v_w_689_);
    v___x_697_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastAdd_go___redArg(
        v_inst_687_,
        v_inst_688_,
        v_w_689_,
        v_aig_690_,
        v_lhs_692_,
        v_rhs_693_,
        v___x_694_,
        v_cin_695_,
        v___x_696_,
    );
    return v___x_697_;
}
pub unsafe fn l_Std_Tactic_BVDecide_BVExpr_bitblast_blastAdd_blast___redArg___boxed(
    mut v_inst_698_: *mut leanh::LeanObject,
    mut v_inst_699_: *mut leanh::LeanObject,
    mut v_w_700_: *mut leanh::LeanObject,
    mut v_aig_701_: *mut leanh::LeanObject,
    mut v_input_702_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_703_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_703_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastAdd_blast___redArg(
        v_inst_698_,
        v_inst_699_,
        v_w_700_,
        v_aig_701_,
        v_input_702_,
    );
    leanh::lean_dec_ref(v_input_702_);
    leanh::lean_dec(v_w_700_);
    return v_res_703_;
}
pub unsafe fn l_Std_Tactic_BVDecide_BVExpr_bitblast_blastAdd_blast(
    mut v_00_u03b1_704_: *mut leanh::LeanObject,
    mut v_inst_705_: *mut leanh::LeanObject,
    mut v_inst_706_: *mut leanh::LeanObject,
    mut v_w_707_: *mut leanh::LeanObject,
    mut v_aig_708_: *mut leanh::LeanObject,
    mut v_input_709_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_710_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_710_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastAdd_blast___redArg(
        v_inst_705_,
        v_inst_706_,
        v_w_707_,
        v_aig_708_,
        v_input_709_,
    );
    return v___x_710_;
}
pub unsafe fn l_Std_Tactic_BVDecide_BVExpr_bitblast_blastAdd_blast___boxed(
    mut v_00_u03b1_711_: *mut leanh::LeanObject,
    mut v_inst_712_: *mut leanh::LeanObject,
    mut v_inst_713_: *mut leanh::LeanObject,
    mut v_w_714_: *mut leanh::LeanObject,
    mut v_aig_715_: *mut leanh::LeanObject,
    mut v_input_716_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_717_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_717_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastAdd_blast(
        v_00_u03b1_711_,
        v_inst_712_,
        v_inst_713_,
        v_w_714_,
        v_aig_715_,
        v_input_716_,
    );
    leanh::lean_dec_ref(v_input_716_);
    leanh::lean_dec(v_w_714_);
    return v_res_717_;
}
pub unsafe fn l_Std_Tactic_BVDecide_BVExpr_bitblast_blastAdd___redArg(
    mut v_inst_718_: *mut leanh::LeanObject,
    mut v_inst_719_: *mut leanh::LeanObject,
    mut v_w_720_: *mut leanh::LeanObject,
    mut v_aig_721_: *mut leanh::LeanObject,
    mut v_input_722_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_lhs_723_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_rhs_724_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_725_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_726_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_727_: u8 = 0;
    let mut v___x_729_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_730_: u8 = 0;
    let mut v___x_732_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_733_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_734_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_735_: u8 = 0;
    let mut v_unused_736_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_737_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_738_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_lhs_723_ = leanh::lean_ctor_get(v_input_722_, 0);
                v_rhs_724_ = leanh::lean_ctor_get(v_input_722_, 1);
                v___x_725_ =
                    l_Std_Sat_AIG_RefVec_countKnown___redArg(v_w_720_, v_aig_721_, v_lhs_723_);
                v___x_726_ =
                    l_Std_Sat_AIG_RefVec_countKnown___redArg(v_w_720_, v_aig_721_, v_rhs_724_);
                v___x_727_ = lean_nat_dec_lt(v___x_725_, v___x_726_);
                leanh::lean_dec(v___x_726_);
                leanh::lean_dec(v___x_725_);
                if v___x_727_ == 0 {
                    leanh::lean_inc_ref(v_rhs_724_);
                    leanh::lean_inc_ref(v_lhs_723_);
                    v_isSharedCheck_735_ = (!leanh::lean_is_exclusive(v_input_722_)) as u8;
                    if v_isSharedCheck_735_ == 0 {
                        v_unused_736_ = leanh::lean_ctor_get(v_input_722_, 1);
                        leanh::lean_dec(v_unused_736_);
                        v_unused_737_ = leanh::lean_ctor_get(v_input_722_, 0);
                        leanh::lean_dec(v_unused_737_);
                        v___x_729_ = v_input_722_;
                        v_isShared_730_ = v_isSharedCheck_735_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_dec(v_input_722_);
                        v___x_729_ = leanh::lean_box(0);
                        v_isShared_730_ = v_isSharedCheck_735_;
                        state = 1;
                        continue;
                    }
                } else {
                    v___x_738_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastAdd_blast___redArg(
                        v_inst_718_,
                        v_inst_719_,
                        v_w_720_,
                        v_aig_721_,
                        v_input_722_,
                    );
                    leanh::lean_dec_ref(v_input_722_);
                    return v___x_738_;
                }
            }
            1 => {
                if v_isShared_730_ == 0 {
                    leanh::lean_ctor_set(v___x_729_, 1, v_lhs_723_);
                    leanh::lean_ctor_set(v___x_729_, 0, v_rhs_724_);
                    v___x_732_ = v___x_729_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_734_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_734_, 0, v_rhs_724_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_734_, 1, v_lhs_723_);
                    v___x_732_ = v_reuseFailAlloc_734_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_733_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastAdd_blast___redArg(
                    v_inst_718_,
                    v_inst_719_,
                    v_w_720_,
                    v_aig_721_,
                    v___x_732_,
                );
                leanh::lean_dec_ref(v___x_732_);
                return v___x_733_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Tactic_BVDecide_BVExpr_bitblast_blastAdd___redArg___boxed(
    mut v_inst_739_: *mut leanh::LeanObject,
    mut v_inst_740_: *mut leanh::LeanObject,
    mut v_w_741_: *mut leanh::LeanObject,
    mut v_aig_742_: *mut leanh::LeanObject,
    mut v_input_743_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_744_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_744_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastAdd___redArg(
        v_inst_739_,
        v_inst_740_,
        v_w_741_,
        v_aig_742_,
        v_input_743_,
    );
    leanh::lean_dec(v_w_741_);
    return v_res_744_;
}
pub unsafe fn l_Std_Tactic_BVDecide_BVExpr_bitblast_blastAdd(
    mut v_00_u03b1_745_: *mut leanh::LeanObject,
    mut v_inst_746_: *mut leanh::LeanObject,
    mut v_inst_747_: *mut leanh::LeanObject,
    mut v_w_748_: *mut leanh::LeanObject,
    mut v_aig_749_: *mut leanh::LeanObject,
    mut v_input_750_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_751_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_751_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastAdd___redArg(
        v_inst_746_,
        v_inst_747_,
        v_w_748_,
        v_aig_749_,
        v_input_750_,
    );
    return v___x_751_;
}
pub unsafe fn l_Std_Tactic_BVDecide_BVExpr_bitblast_blastAdd___boxed(
    mut v_00_u03b1_752_: *mut leanh::LeanObject,
    mut v_inst_753_: *mut leanh::LeanObject,
    mut v_inst_754_: *mut leanh::LeanObject,
    mut v_w_755_: *mut leanh::LeanObject,
    mut v_aig_756_: *mut leanh::LeanObject,
    mut v_input_757_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_758_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_758_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastAdd(
        v_00_u03b1_752_,
        v_inst_753_,
        v_inst_754_,
        v_w_755_,
        v_aig_756_,
        v_input_757_,
    );
    leanh::lean_dec(v_w_755_);
    return v_res_758_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Operations_Add(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Basic(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Std_Sat_AIG_LawfulVecOperator(builtin);
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
pub unsafe fn meta_initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Operations_Add(
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
pub unsafe fn initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Operations_Add(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Basic(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Std_Sat_AIG_LawfulVecOperator(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_Omega(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res =
        runtime_initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Operations_Add(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = meta_initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Operations_Add(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Operations_Add(builtin);
}