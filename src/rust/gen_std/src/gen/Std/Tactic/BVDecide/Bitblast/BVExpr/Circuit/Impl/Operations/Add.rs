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
    crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
            + 8) as u16,
        other: 1,
        tag: 0,
    },
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        0 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Std_Tactic_BVDecide_BVExpr_bitblast_blastAdd_blast___redArg___closed__0:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Std_Tactic_BVDecide_BVExpr_bitblast_blastAdd_blast___redArg___closed__0_value
) as *mut crate::leanh::LeanObject;
pub unsafe fn l_Std_Tactic_BVDecide_BVExpr_bitblast_FullAdderInput_cast___redArg(
    mut v_val_380_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_lhs_381_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_rhs_382_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_cin_383_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_385_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_386_: u8 = 0;
    let mut v_gate_387_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_invert_388_: u8 = 0;
    let mut v___x_390_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_391_: u8 = 0;
    let mut v_gate_392_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_invert_393_: u8 = 0;
    let mut v___x_395_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_396_: u8 = 0;
    let mut v_gate_397_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_invert_398_: u8 = 0;
    let mut v___x_400_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_401_: u8 = 0;
    let mut v___x_403_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_405_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_407_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_409_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_410_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_411_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_412_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_413_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_414_: u8 = 0;
    let mut v_isSharedCheck_415_: u8 = 0;
    let mut v_isSharedCheck_416_: u8 = 0;
    let mut v_isSharedCheck_417_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_lhs_381_ = crate::leanh::lean_ctor_get(v_val_380_, 0);
                v_rhs_382_ = crate::leanh::lean_ctor_get(v_val_380_, 1);
                v_cin_383_ = crate::leanh::lean_ctor_get(v_val_380_, 2);
                v_isSharedCheck_417_ = (!crate::leanh::lean_is_exclusive(v_val_380_)) as u8;
                if v_isSharedCheck_417_ == 0 {
                    v___x_385_ = v_val_380_;
                    v_isShared_386_ = v_isSharedCheck_417_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_cin_383_);
                    crate::leanh::lean_inc(v_rhs_382_);
                    crate::leanh::lean_inc(v_lhs_381_);
                    crate::leanh::lean_dec(v_val_380_);
                    v___x_385_ = crate::leanh::lean_box(0);
                    v_isShared_386_ = v_isSharedCheck_417_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_gate_387_ = crate::leanh::lean_ctor_get(v_lhs_381_, 0);
                v_invert_388_ = crate::leanh::lean_ctor_get_uint8(
                    v_lhs_381_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                );
                v_isSharedCheck_416_ = (!crate::leanh::lean_is_exclusive(v_lhs_381_)) as u8;
                if v_isSharedCheck_416_ == 0 {
                    v___x_390_ = v_lhs_381_;
                    v_isShared_391_ = v_isSharedCheck_416_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_gate_387_);
                    crate::leanh::lean_dec(v_lhs_381_);
                    v___x_390_ = crate::leanh::lean_box(0);
                    v_isShared_391_ = v_isSharedCheck_416_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v_gate_392_ = crate::leanh::lean_ctor_get(v_rhs_382_, 0);
                v_invert_393_ = crate::leanh::lean_ctor_get_uint8(
                    v_rhs_382_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                );
                v_isSharedCheck_415_ = (!crate::leanh::lean_is_exclusive(v_rhs_382_)) as u8;
                if v_isSharedCheck_415_ == 0 {
                    v___x_395_ = v_rhs_382_;
                    v_isShared_396_ = v_isSharedCheck_415_;
                    state = 3;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_gate_392_);
                    crate::leanh::lean_dec(v_rhs_382_);
                    v___x_395_ = crate::leanh::lean_box(0);
                    v_isShared_396_ = v_isSharedCheck_415_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v_gate_397_ = crate::leanh::lean_ctor_get(v_cin_383_, 0);
                v_invert_398_ = crate::leanh::lean_ctor_get_uint8(
                    v_cin_383_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                );
                v_isSharedCheck_414_ = (!crate::leanh::lean_is_exclusive(v_cin_383_)) as u8;
                if v_isSharedCheck_414_ == 0 {
                    v___x_400_ = v_cin_383_;
                    v_isShared_401_ = v_isSharedCheck_414_;
                    state = 4;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_gate_397_);
                    crate::leanh::lean_dec(v_cin_383_);
                    v___x_400_ = crate::leanh::lean_box(0);
                    v_isShared_401_ = v_isSharedCheck_414_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                if v_isShared_401_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_400_, 0, v_gate_387_);
                    v___x_403_ = v___x_400_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_413_ = crate::leanh::lean_alloc_ctor(0, 1, (1) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_413_, 0, v_gate_387_);
                    v___x_403_ = v_reuseFailAlloc_413_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                crate::leanh::lean_ctor_set_uint8(
                    v___x_403_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                    v_invert_388_,
                );
                if v_isShared_396_ == 0 {
                    v___x_405_ = v___x_395_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_412_ = crate::leanh::lean_alloc_ctor(0, 1, (1) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_412_, 0, v_gate_392_);
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_412_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                        v_invert_393_,
                    );
                    v___x_405_ = v_reuseFailAlloc_412_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                if v_isShared_391_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_390_, 0, v_gate_397_);
                    v___x_407_ = v___x_390_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_411_ = crate::leanh::lean_alloc_ctor(0, 1, (1) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_411_, 0, v_gate_397_);
                    v___x_407_ = v_reuseFailAlloc_411_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                crate::leanh::lean_ctor_set_uint8(
                    v___x_407_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                    v_invert_398_,
                );
                if v_isShared_386_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_385_, 2, v___x_407_);
                    crate::leanh::lean_ctor_set(v___x_385_, 1, v___x_405_);
                    crate::leanh::lean_ctor_set(v___x_385_, 0, v___x_403_);
                    v___x_409_ = v___x_385_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_410_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_410_, 0, v___x_403_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_410_, 1, v___x_405_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_410_, 2, v___x_407_);
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
    mut v_00_u03b1_418_: *mut crate::leanh::LeanObject,
    mut v_inst_419_: *mut crate::leanh::LeanObject,
    mut v_inst_420_: *mut crate::leanh::LeanObject,
    mut v_aig1_421_: *mut crate::leanh::LeanObject,
    mut v_aig2_422_: *mut crate::leanh::LeanObject,
    mut v_val_423_: *mut crate::leanh::LeanObject,
    mut v_h_424_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_425_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_425_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_FullAdderInput_cast___redArg(v_val_423_);
    return v___x_425_;
}
pub unsafe fn l_Std_Tactic_BVDecide_BVExpr_bitblast_FullAdderInput_cast___boxed(
    mut v_00_u03b1_426_: *mut crate::leanh::LeanObject,
    mut v_inst_427_: *mut crate::leanh::LeanObject,
    mut v_inst_428_: *mut crate::leanh::LeanObject,
    mut v_aig1_429_: *mut crate::leanh::LeanObject,
    mut v_aig2_430_: *mut crate::leanh::LeanObject,
    mut v_val_431_: *mut crate::leanh::LeanObject,
    mut v_h_432_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_433_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_433_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_FullAdderInput_cast(
        v_00_u03b1_426_,
        v_inst_427_,
        v_inst_428_,
        v_aig1_429_,
        v_aig2_430_,
        v_val_431_,
        v_h_432_,
    );
    crate::leanh::lean_dec_ref(v_aig2_430_);
    crate::leanh::lean_dec_ref(v_aig1_429_);
    crate::leanh::lean_dec_ref(v_inst_428_);
    crate::leanh::lean_dec_ref(v_inst_427_);
    return v_res_433_;
}
pub unsafe fn l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Operations_Add_0__Std_Tactic_BVDecide_BVExpr_bitblast_FullAdderInput_cast_match__1_splitter___redArg(
    mut v_val_434_: *mut crate::leanh::LeanObject,
    mut v_h__1_435_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_lhs_436_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_rhs_437_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_cin_438_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_439_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_lhs_436_ = crate::leanh::lean_ctor_get(v_val_434_, 0);
    crate::leanh::lean_inc_ref(v_lhs_436_);
    v_rhs_437_ = crate::leanh::lean_ctor_get(v_val_434_, 1);
    crate::leanh::lean_inc_ref(v_rhs_437_);
    v_cin_438_ = crate::leanh::lean_ctor_get(v_val_434_, 2);
    crate::leanh::lean_inc_ref(v_cin_438_);
    crate::leanh::lean_dec_ref(v_val_434_);
    v___x_439_ = crate::leanh::lean_apply_3(v_h__1_435_, v_lhs_436_, v_rhs_437_, v_cin_438_);
    return v___x_439_;
}
pub unsafe fn l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Operations_Add_0__Std_Tactic_BVDecide_BVExpr_bitblast_FullAdderInput_cast_match__1_splitter(
    mut v_00_u03b1_440_: *mut crate::leanh::LeanObject,
    mut v_inst_441_: *mut crate::leanh::LeanObject,
    mut v_inst_442_: *mut crate::leanh::LeanObject,
    mut v_aig1_443_: *mut crate::leanh::LeanObject,
    mut v_motive_444_: *mut crate::leanh::LeanObject,
    mut v_val_445_: *mut crate::leanh::LeanObject,
    mut v_h__1_446_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_lhs_447_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_rhs_448_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_cin_449_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_450_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_lhs_447_ = crate::leanh::lean_ctor_get(v_val_445_, 0);
    crate::leanh::lean_inc_ref(v_lhs_447_);
    v_rhs_448_ = crate::leanh::lean_ctor_get(v_val_445_, 1);
    crate::leanh::lean_inc_ref(v_rhs_448_);
    v_cin_449_ = crate::leanh::lean_ctor_get(v_val_445_, 2);
    crate::leanh::lean_inc_ref(v_cin_449_);
    crate::leanh::lean_dec_ref(v_val_445_);
    v___x_450_ = crate::leanh::lean_apply_3(v_h__1_446_, v_lhs_447_, v_rhs_448_, v_cin_449_);
    return v___x_450_;
}
pub unsafe fn l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Operations_Add_0__Std_Tactic_BVDecide_BVExpr_bitblast_FullAdderInput_cast_match__1_splitter___boxed(
    mut v_00_u03b1_451_: *mut crate::leanh::LeanObject,
    mut v_inst_452_: *mut crate::leanh::LeanObject,
    mut v_inst_453_: *mut crate::leanh::LeanObject,
    mut v_aig1_454_: *mut crate::leanh::LeanObject,
    mut v_motive_455_: *mut crate::leanh::LeanObject,
    mut v_val_456_: *mut crate::leanh::LeanObject,
    mut v_h__1_457_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_458_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_458_ = l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Operations_Add_0__Std_Tactic_BVDecide_BVExpr_bitblast_FullAdderInput_cast_match__1_splitter(v_00_u03b1_451_, v_inst_452_, v_inst_453_, v_aig1_454_, v_motive_455_, v_val_456_, v_h__1_457_);
    crate::leanh::lean_dec_ref(v_aig1_454_);
    crate::leanh::lean_dec_ref(v_inst_453_);
    crate::leanh::lean_dec_ref(v_inst_452_);
    return v_res_458_;
}
pub unsafe fn l_Std_Tactic_BVDecide_BVExpr_bitblast_mkFullAdderOut___redArg(
    mut v_inst_459_: *mut crate::leanh::LeanObject,
    mut v_inst_460_: *mut crate::leanh::LeanObject,
    mut v_aig_461_: *mut crate::leanh::LeanObject,
    mut v_input_462_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_lhs_463_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_rhs_464_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_cin_465_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_466_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_res_467_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_aig_468_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_469_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_471_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_472_: u8 = 0;
    let mut v_gate_473_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_invert_474_: u8 = 0;
    let mut v___x_476_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_477_: u8 = 0;
    let mut v_cin_479_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_481_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_482_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_483_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_484_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_485_: u8 = 0;
    let mut v_isSharedCheck_486_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_lhs_463_ = crate::leanh::lean_ctor_get(v_input_462_, 0);
                crate::leanh::lean_inc_ref(v_lhs_463_);
                v_rhs_464_ = crate::leanh::lean_ctor_get(v_input_462_, 1);
                crate::leanh::lean_inc_ref(v_rhs_464_);
                v_cin_465_ = crate::leanh::lean_ctor_get(v_input_462_, 2);
                crate::leanh::lean_inc_ref(v_cin_465_);
                crate::leanh::lean_dec_ref(v_input_462_);
                v___x_466_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_466_, 0, v_lhs_463_);
                crate::leanh::lean_ctor_set(v___x_466_, 1, v_rhs_464_);
                crate::leanh::lean_inc_ref(v_inst_460_);
                crate::leanh::lean_inc_ref(v_inst_459_);
                v_res_467_ = l_Std_Sat_AIG_mkXorCached___redArg(
                    v_inst_459_,
                    v_inst_460_,
                    v_aig_461_,
                    v___x_466_,
                );
                v_aig_468_ = crate::leanh::lean_ctor_get(v_res_467_, 0);
                v_ref_469_ = crate::leanh::lean_ctor_get(v_res_467_, 1);
                v_isSharedCheck_486_ = (!crate::leanh::lean_is_exclusive(v_res_467_)) as u8;
                if v_isSharedCheck_486_ == 0 {
                    v___x_471_ = v_res_467_;
                    v_isShared_472_ = v_isSharedCheck_486_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_ref_469_);
                    crate::leanh::lean_inc(v_aig_468_);
                    crate::leanh::lean_dec(v_res_467_);
                    v___x_471_ = crate::leanh::lean_box(0);
                    v_isShared_472_ = v_isSharedCheck_486_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_gate_473_ = crate::leanh::lean_ctor_get(v_cin_465_, 0);
                v_invert_474_ = crate::leanh::lean_ctor_get_uint8(
                    v_cin_465_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                );
                v_isSharedCheck_485_ = (!crate::leanh::lean_is_exclusive(v_cin_465_)) as u8;
                if v_isSharedCheck_485_ == 0 {
                    v___x_476_ = v_cin_465_;
                    v_isShared_477_ = v_isSharedCheck_485_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_gate_473_);
                    crate::leanh::lean_dec(v_cin_465_);
                    v___x_476_ = crate::leanh::lean_box(0);
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
                    v_reuseFailAlloc_484_ = crate::leanh::lean_alloc_ctor(0, 1, (1) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_484_, 0, v_gate_473_);
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_484_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                        v_invert_474_,
                    );
                    v_cin_479_ = v_reuseFailAlloc_484_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_472_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_471_, 1, v_cin_479_);
                    crate::leanh::lean_ctor_set(v___x_471_, 0, v_ref_469_);
                    v___x_481_ = v___x_471_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_483_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_483_, 0, v_ref_469_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_483_, 1, v_cin_479_);
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
    mut v_00_u03b1_487_: *mut crate::leanh::LeanObject,
    mut v_inst_488_: *mut crate::leanh::LeanObject,
    mut v_inst_489_: *mut crate::leanh::LeanObject,
    mut v_aig_490_: *mut crate::leanh::LeanObject,
    mut v_input_491_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_492_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_492_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_mkFullAdderOut___redArg(
        v_inst_488_,
        v_inst_489_,
        v_aig_490_,
        v_input_491_,
    );
    return v___x_492_;
}
pub unsafe fn l_Std_Tactic_BVDecide_BVExpr_bitblast_mkFullAdderCarry___redArg(
    mut v_inst_493_: *mut crate::leanh::LeanObject,
    mut v_inst_494_: *mut crate::leanh::LeanObject,
    mut v_aig_495_: *mut crate::leanh::LeanObject,
    mut v_input_496_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_lhs_497_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_rhs_498_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_cin_499_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_500_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_res_501_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_aig_502_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_503_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_505_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_506_: u8 = 0;
    let mut v_gate_507_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_invert_508_: u8 = 0;
    let mut v___x_510_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_511_: u8 = 0;
    let mut v_gate_512_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_invert_513_: u8 = 0;
    let mut v___x_515_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_516_: u8 = 0;
    let mut v_gate_517_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_invert_518_: u8 = 0;
    let mut v___x_520_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_521_: u8 = 0;
    let mut v_cin_523_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_525_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_res_526_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_aig_527_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_528_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_530_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_531_: u8 = 0;
    let mut v_lhs_533_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_rhs_535_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_537_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_res_538_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_aig_539_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_540_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_542_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_543_: u8 = 0;
    let mut v_gate_544_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_invert_545_: u8 = 0;
    let mut v___x_547_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_548_: u8 = 0;
    let mut v_lorRef_550_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_552_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_553_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_554_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_555_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_556_: u8 = 0;
    let mut v_isSharedCheck_557_: u8 = 0;
    let mut v_reuseFailAlloc_558_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_559_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_560_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_561_: u8 = 0;
    let mut v_reuseFailAlloc_562_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_563_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_564_: u8 = 0;
    let mut v_isSharedCheck_565_: u8 = 0;
    let mut v_isSharedCheck_566_: u8 = 0;
    let mut v_isSharedCheck_567_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_lhs_497_ = crate::leanh::lean_ctor_get(v_input_496_, 0);
                crate::leanh::lean_inc_ref_n(v_lhs_497_, 2);
                v_rhs_498_ = crate::leanh::lean_ctor_get(v_input_496_, 1);
                crate::leanh::lean_inc_ref_n(v_rhs_498_, 2);
                v_cin_499_ = crate::leanh::lean_ctor_get(v_input_496_, 2);
                crate::leanh::lean_inc_ref(v_cin_499_);
                crate::leanh::lean_dec_ref(v_input_496_);
                v___x_500_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_500_, 0, v_lhs_497_);
                crate::leanh::lean_ctor_set(v___x_500_, 1, v_rhs_498_);
                crate::leanh::lean_inc_ref(v_inst_494_);
                crate::leanh::lean_inc_ref(v_inst_493_);
                v_res_501_ = l_Std_Sat_AIG_mkXorCached___redArg(
                    v_inst_493_,
                    v_inst_494_,
                    v_aig_495_,
                    v___x_500_,
                );
                v_aig_502_ = crate::leanh::lean_ctor_get(v_res_501_, 0);
                v_ref_503_ = crate::leanh::lean_ctor_get(v_res_501_, 1);
                v_isSharedCheck_567_ = (!crate::leanh::lean_is_exclusive(v_res_501_)) as u8;
                if v_isSharedCheck_567_ == 0 {
                    v___x_505_ = v_res_501_;
                    v_isShared_506_ = v_isSharedCheck_567_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_ref_503_);
                    crate::leanh::lean_inc(v_aig_502_);
                    crate::leanh::lean_dec(v_res_501_);
                    v___x_505_ = crate::leanh::lean_box(0);
                    v_isShared_506_ = v_isSharedCheck_567_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_gate_507_ = crate::leanh::lean_ctor_get(v_lhs_497_, 0);
                v_invert_508_ = crate::leanh::lean_ctor_get_uint8(
                    v_lhs_497_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                );
                v_isSharedCheck_566_ = (!crate::leanh::lean_is_exclusive(v_lhs_497_)) as u8;
                if v_isSharedCheck_566_ == 0 {
                    v___x_510_ = v_lhs_497_;
                    v_isShared_511_ = v_isSharedCheck_566_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_gate_507_);
                    crate::leanh::lean_dec(v_lhs_497_);
                    v___x_510_ = crate::leanh::lean_box(0);
                    v_isShared_511_ = v_isSharedCheck_566_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v_gate_512_ = crate::leanh::lean_ctor_get(v_rhs_498_, 0);
                v_invert_513_ = crate::leanh::lean_ctor_get_uint8(
                    v_rhs_498_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                );
                v_isSharedCheck_565_ = (!crate::leanh::lean_is_exclusive(v_rhs_498_)) as u8;
                if v_isSharedCheck_565_ == 0 {
                    v___x_515_ = v_rhs_498_;
                    v_isShared_516_ = v_isSharedCheck_565_;
                    state = 3;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_gate_512_);
                    crate::leanh::lean_dec(v_rhs_498_);
                    v___x_515_ = crate::leanh::lean_box(0);
                    v_isShared_516_ = v_isSharedCheck_565_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v_gate_517_ = crate::leanh::lean_ctor_get(v_cin_499_, 0);
                v_invert_518_ = crate::leanh::lean_ctor_get_uint8(
                    v_cin_499_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                );
                v_isSharedCheck_564_ = (!crate::leanh::lean_is_exclusive(v_cin_499_)) as u8;
                if v_isSharedCheck_564_ == 0 {
                    v___x_520_ = v_cin_499_;
                    v_isShared_521_ = v_isSharedCheck_564_;
                    state = 4;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_gate_517_);
                    crate::leanh::lean_dec(v_cin_499_);
                    v___x_520_ = crate::leanh::lean_box(0);
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
                    v_reuseFailAlloc_563_ = crate::leanh::lean_alloc_ctor(0, 1, (1) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_563_, 0, v_gate_517_);
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_563_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                        v_invert_518_,
                    );
                    v_cin_523_ = v_reuseFailAlloc_563_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                if v_isShared_506_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_505_, 1, v_cin_523_);
                    crate::leanh::lean_ctor_set(v___x_505_, 0, v_ref_503_);
                    v___x_525_ = v___x_505_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_562_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_562_, 0, v_ref_503_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_562_, 1, v_cin_523_);
                    v___x_525_ = v_reuseFailAlloc_562_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                crate::leanh::lean_inc_ref(v_inst_494_);
                crate::leanh::lean_inc_ref(v_inst_493_);
                v_res_526_ = l_Std_Sat_AIG_mkGateCached___redArg(
                    v_inst_493_,
                    v_inst_494_,
                    v_aig_502_,
                    v___x_525_,
                );
                v_aig_527_ = crate::leanh::lean_ctor_get(v_res_526_, 0);
                v_ref_528_ = crate::leanh::lean_ctor_get(v_res_526_, 1);
                v_isSharedCheck_561_ = (!crate::leanh::lean_is_exclusive(v_res_526_)) as u8;
                if v_isSharedCheck_561_ == 0 {
                    v___x_530_ = v_res_526_;
                    v_isShared_531_ = v_isSharedCheck_561_;
                    state = 7;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_ref_528_);
                    crate::leanh::lean_inc(v_aig_527_);
                    crate::leanh::lean_dec(v_res_526_);
                    v___x_530_ = crate::leanh::lean_box(0);
                    v_isShared_531_ = v_isSharedCheck_561_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                if v_isShared_516_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_515_, 0, v_gate_507_);
                    v_lhs_533_ = v___x_515_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_560_ = crate::leanh::lean_alloc_ctor(0, 1, (1) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_560_, 0, v_gate_507_);
                    v_lhs_533_ = v_reuseFailAlloc_560_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                crate::leanh::lean_ctor_set_uint8(
                    v_lhs_533_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                    v_invert_508_,
                );
                if v_isShared_511_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_510_, 0, v_gate_512_);
                    v_rhs_535_ = v___x_510_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_559_ = crate::leanh::lean_alloc_ctor(0, 1, (1) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_559_, 0, v_gate_512_);
                    v_rhs_535_ = v_reuseFailAlloc_559_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                crate::leanh::lean_ctor_set_uint8(
                    v_rhs_535_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                    v_invert_513_,
                );
                if v_isShared_531_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_530_, 1, v_rhs_535_);
                    crate::leanh::lean_ctor_set(v___x_530_, 0, v_lhs_533_);
                    v___x_537_ = v___x_530_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_558_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_558_, 0, v_lhs_533_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_558_, 1, v_rhs_535_);
                    v___x_537_ = v_reuseFailAlloc_558_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                crate::leanh::lean_inc_ref(v_inst_494_);
                crate::leanh::lean_inc_ref(v_inst_493_);
                v_res_538_ = l_Std_Sat_AIG_mkGateCached___redArg(
                    v_inst_493_,
                    v_inst_494_,
                    v_aig_527_,
                    v___x_537_,
                );
                v_aig_539_ = crate::leanh::lean_ctor_get(v_res_538_, 0);
                v_ref_540_ = crate::leanh::lean_ctor_get(v_res_538_, 1);
                v_isSharedCheck_557_ = (!crate::leanh::lean_is_exclusive(v_res_538_)) as u8;
                if v_isSharedCheck_557_ == 0 {
                    v___x_542_ = v_res_538_;
                    v_isShared_543_ = v_isSharedCheck_557_;
                    state = 11;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_ref_540_);
                    crate::leanh::lean_inc(v_aig_539_);
                    crate::leanh::lean_dec(v_res_538_);
                    v___x_542_ = crate::leanh::lean_box(0);
                    v_isShared_543_ = v_isSharedCheck_557_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                v_gate_544_ = crate::leanh::lean_ctor_get(v_ref_528_, 0);
                v_invert_545_ = crate::leanh::lean_ctor_get_uint8(
                    v_ref_528_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                );
                v_isSharedCheck_556_ = (!crate::leanh::lean_is_exclusive(v_ref_528_)) as u8;
                if v_isSharedCheck_556_ == 0 {
                    v___x_547_ = v_ref_528_;
                    v_isShared_548_ = v_isSharedCheck_556_;
                    state = 12;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_gate_544_);
                    crate::leanh::lean_dec(v_ref_528_);
                    v___x_547_ = crate::leanh::lean_box(0);
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
                    v_reuseFailAlloc_555_ = crate::leanh::lean_alloc_ctor(0, 1, (1) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_555_, 0, v_gate_544_);
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_555_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                        v_invert_545_,
                    );
                    v_lorRef_550_ = v_reuseFailAlloc_555_;
                    state = 13;
                    continue;
                }
            }
            13 => {
                if v_isShared_543_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_542_, 0, v_lorRef_550_);
                    v___x_552_ = v___x_542_;
                    state = 14;
                    continue;
                } else {
                    v_reuseFailAlloc_554_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_554_, 0, v_lorRef_550_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_554_, 1, v_ref_540_);
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
    mut v_00_u03b1_568_: *mut crate::leanh::LeanObject,
    mut v_inst_569_: *mut crate::leanh::LeanObject,
    mut v_inst_570_: *mut crate::leanh::LeanObject,
    mut v_aig_571_: *mut crate::leanh::LeanObject,
    mut v_input_572_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_573_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_573_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_mkFullAdderCarry___redArg(
        v_inst_569_,
        v_inst_570_,
        v_aig_571_,
        v_input_572_,
    );
    return v___x_573_;
}
pub unsafe fn l_Std_Tactic_BVDecide_BVExpr_bitblast_mkFullAdder___redArg(
    mut v_inst_574_: *mut crate::leanh::LeanObject,
    mut v_inst_575_: *mut crate::leanh::LeanObject,
    mut v_aig_576_: *mut crate::leanh::LeanObject,
    mut v_input_577_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_578_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_aig_579_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_580_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_input_581_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_res_582_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_aig_583_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_584_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_gate_585_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_invert_586_: u8 = 0;
    let mut v___x_588_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_589_: u8 = 0;
    let mut v_outRef_591_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_592_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_593_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_594_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                crate::leanh::lean_inc_ref(v_input_577_);
                crate::leanh::lean_inc_ref(v_inst_575_);
                crate::leanh::lean_inc_ref(v_inst_574_);
                v_res_578_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_mkFullAdderOut___redArg(
                    v_inst_574_,
                    v_inst_575_,
                    v_aig_576_,
                    v_input_577_,
                );
                v_aig_579_ = crate::leanh::lean_ctor_get(v_res_578_, 0);
                crate::leanh::lean_inc_ref(v_aig_579_);
                v_ref_580_ = crate::leanh::lean_ctor_get(v_res_578_, 1);
                crate::leanh::lean_inc_ref(v_ref_580_);
                crate::leanh::lean_dec_ref(v_res_578_);
                v_input_581_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_FullAdderInput_cast___redArg(
                    v_input_577_,
                );
                v_res_582_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_mkFullAdderCarry___redArg(
                    v_inst_574_,
                    v_inst_575_,
                    v_aig_579_,
                    v_input_581_,
                );
                v_aig_583_ = crate::leanh::lean_ctor_get(v_res_582_, 0);
                crate::leanh::lean_inc_ref(v_aig_583_);
                v_ref_584_ = crate::leanh::lean_ctor_get(v_res_582_, 1);
                crate::leanh::lean_inc_ref(v_ref_584_);
                crate::leanh::lean_dec_ref(v_res_582_);
                v_gate_585_ = crate::leanh::lean_ctor_get(v_ref_580_, 0);
                v_invert_586_ = crate::leanh::lean_ctor_get_uint8(
                    v_ref_580_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                );
                v_isSharedCheck_594_ = (!crate::leanh::lean_is_exclusive(v_ref_580_)) as u8;
                if v_isSharedCheck_594_ == 0 {
                    v___x_588_ = v_ref_580_;
                    v_isShared_589_ = v_isSharedCheck_594_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_gate_585_);
                    crate::leanh::lean_dec(v_ref_580_);
                    v___x_588_ = crate::leanh::lean_box(0);
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
                    v_reuseFailAlloc_593_ = crate::leanh::lean_alloc_ctor(0, 1, (1) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_593_, 0, v_gate_585_);
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_593_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                        v_invert_586_,
                    );
                    v_outRef_591_ = v_reuseFailAlloc_593_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_592_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_592_, 0, v_aig_583_);
                crate::leanh::lean_ctor_set(v___x_592_, 1, v_outRef_591_);
                crate::leanh::lean_ctor_set(v___x_592_, 2, v_ref_584_);
                return v___x_592_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Tactic_BVDecide_BVExpr_bitblast_mkFullAdder(
    mut v_00_u03b1_595_: *mut crate::leanh::LeanObject,
    mut v_inst_596_: *mut crate::leanh::LeanObject,
    mut v_inst_597_: *mut crate::leanh::LeanObject,
    mut v_aig_598_: *mut crate::leanh::LeanObject,
    mut v_input_599_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_600_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_600_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_mkFullAdder___redArg(
        v_inst_596_,
        v_inst_597_,
        v_aig_598_,
        v_input_599_,
    );
    return v___x_600_;
}
pub unsafe fn l_Std_Tactic_BVDecide_BVExpr_bitblast_blastAdd_go___redArg(
    mut v_inst_601_: *mut crate::leanh::LeanObject,
    mut v_inst_602_: *mut crate::leanh::LeanObject,
    mut v_w_603_: *mut crate::leanh::LeanObject,
    mut v_aig_604_: *mut crate::leanh::LeanObject,
    mut v_lhs_605_: *mut crate::leanh::LeanObject,
    mut v_rhs_606_: *mut crate::leanh::LeanObject,
    mut v_curr_607_: *mut crate::leanh::LeanObject,
    mut v_cin_608_: *mut crate::leanh::LeanObject,
    mut v_s_609_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___y_611_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_612_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_613_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_res_614_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_out_615_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_aig_616_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_cout_617_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_gate_618_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_invert_619_: u8 = 0;
    let mut v___x_620_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_621_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_622_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_623_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_624_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_625_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_s_626_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_628_: u8 = 0;
    let mut v___y_630_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_631_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_632_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_633_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_634_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_635_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_636_: u8 = 0;
    let mut v___x_637_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_638_: u8 = 0;
    let mut v___x_639_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_640_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_641_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_642_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_643_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_644_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_645_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_646_: u8 = 0;
    let mut v___x_647_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_648_: u8 = 0;
    let mut v___x_649_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_628_ = lean_nat_dec_lt(v_curr_607_, v_w_603_);
                if v___x_628_ == 0 {
                    crate::leanh::lean_dec_ref(v_cin_608_);
                    crate::leanh::lean_dec(v_curr_607_);
                    crate::leanh::lean_dec_ref(v_inst_602_);
                    crate::leanh::lean_dec_ref(v_inst_601_);
                    v___x_640_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_640_, 0, v_aig_604_);
                    crate::leanh::lean_ctor_set(v___x_640_, 1, v_s_609_);
                    return v___x_640_;
                } else {
                    v_ref_641_ = lean_array_fget_borrowed(v_lhs_605_, v_curr_607_);
                    v___x_642_ = crate::leanh::lean_unsigned_to_nat(1);
                    v___x_643_ = lean_nat_shiftr(v_ref_641_, v___x_642_);
                    v___x_644_ = lean_nat_land(v___x_642_, v_ref_641_);
                    v___x_645_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___x_646_ = lean_nat_dec_eq(v___x_644_, v___x_645_);
                    crate::leanh::lean_dec(v___x_644_);
                    if v___x_646_ == 0 {
                        v___x_647_ = crate::leanh::lean_alloc_ctor(0, 1, (1) as u32);
                        crate::leanh::lean_ctor_set(v___x_647_, 0, v___x_643_);
                        crate::leanh::lean_ctor_set_uint8(
                            v___x_647_,
                            (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                            v___x_628_,
                        );
                        v___y_630_ = v___x_647_;
                        state = 2;
                        continue;
                    } else {
                        v___x_648_ = 0;
                        v___x_649_ = crate::leanh::lean_alloc_ctor(0, 1, (1) as u32);
                        crate::leanh::lean_ctor_set(v___x_649_, 0, v___x_643_);
                        crate::leanh::lean_ctor_set_uint8(
                            v___x_649_,
                            (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                            v___x_648_,
                        );
                        v___y_630_ = v___x_649_;
                        state = 2;
                        continue;
                    }
                }
            }
            1 => {
                v___x_613_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_613_, 0, v___y_611_);
                crate::leanh::lean_ctor_set(v___x_613_, 1, v___y_612_);
                crate::leanh::lean_ctor_set(v___x_613_, 2, v_cin_608_);
                crate::leanh::lean_inc_ref(v_inst_602_);
                crate::leanh::lean_inc_ref(v_inst_601_);
                v_res_614_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_mkFullAdder___redArg(
                    v_inst_601_,
                    v_inst_602_,
                    v_aig_604_,
                    v___x_613_,
                );
                v_out_615_ = crate::leanh::lean_ctor_get(v_res_614_, 1);
                crate::leanh::lean_inc_ref(v_out_615_);
                v_aig_616_ = crate::leanh::lean_ctor_get(v_res_614_, 0);
                crate::leanh::lean_inc_ref(v_aig_616_);
                v_cout_617_ = crate::leanh::lean_ctor_get(v_res_614_, 2);
                crate::leanh::lean_inc_ref(v_cout_617_);
                crate::leanh::lean_dec_ref(v_res_614_);
                v_gate_618_ = crate::leanh::lean_ctor_get(v_out_615_, 0);
                crate::leanh::lean_inc(v_gate_618_);
                v_invert_619_ = crate::leanh::lean_ctor_get_uint8(
                    v_out_615_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                );
                crate::leanh::lean_dec_ref(v_out_615_);
                v___x_620_ = crate::leanh::lean_unsigned_to_nat(1);
                v___x_621_ = lean_nat_add(v_curr_607_, v___x_620_);
                crate::leanh::lean_dec(v_curr_607_);
                v___x_622_ = crate::leanh::lean_unsigned_to_nat(2);
                v___x_623_ = lean_nat_mul(v_gate_618_, v___x_622_);
                crate::leanh::lean_dec(v_gate_618_);
                v___x_624_ = l_Bool_toNat(v_invert_619_);
                v___x_625_ = lean_nat_lor(v___x_623_, v___x_624_);
                crate::leanh::lean_dec(v___x_624_);
                crate::leanh::lean_dec(v___x_623_);
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
                v___x_632_ = crate::leanh::lean_unsigned_to_nat(1);
                v___x_633_ = lean_nat_shiftr(v_ref_631_, v___x_632_);
                v___x_634_ = lean_nat_land(v___x_632_, v_ref_631_);
                v___x_635_ = crate::leanh::lean_unsigned_to_nat(0);
                v___x_636_ = lean_nat_dec_eq(v___x_634_, v___x_635_);
                crate::leanh::lean_dec(v___x_634_);
                if v___x_636_ == 0 {
                    v___x_637_ = crate::leanh::lean_alloc_ctor(0, 1, (1) as u32);
                    crate::leanh::lean_ctor_set(v___x_637_, 0, v___x_633_);
                    crate::leanh::lean_ctor_set_uint8(
                        v___x_637_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                        v___x_628_,
                    );
                    v___y_611_ = v___y_630_;
                    v___y_612_ = v___x_637_;
                    state = 1;
                    continue;
                } else {
                    v___x_638_ = 0;
                    v___x_639_ = crate::leanh::lean_alloc_ctor(0, 1, (1) as u32);
                    crate::leanh::lean_ctor_set(v___x_639_, 0, v___x_633_);
                    crate::leanh::lean_ctor_set_uint8(
                        v___x_639_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
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
    mut v_inst_650_: *mut crate::leanh::LeanObject,
    mut v_inst_651_: *mut crate::leanh::LeanObject,
    mut v_w_652_: *mut crate::leanh::LeanObject,
    mut v_aig_653_: *mut crate::leanh::LeanObject,
    mut v_lhs_654_: *mut crate::leanh::LeanObject,
    mut v_rhs_655_: *mut crate::leanh::LeanObject,
    mut v_curr_656_: *mut crate::leanh::LeanObject,
    mut v_cin_657_: *mut crate::leanh::LeanObject,
    mut v_s_658_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_659_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
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
    crate::leanh::lean_dec_ref(v_rhs_655_);
    crate::leanh::lean_dec_ref(v_lhs_654_);
    crate::leanh::lean_dec(v_w_652_);
    return v_res_659_;
}
pub unsafe fn l_Std_Tactic_BVDecide_BVExpr_bitblast_blastAdd_go(
    mut v_00_u03b1_660_: *mut crate::leanh::LeanObject,
    mut v_inst_661_: *mut crate::leanh::LeanObject,
    mut v_inst_662_: *mut crate::leanh::LeanObject,
    mut v_w_663_: *mut crate::leanh::LeanObject,
    mut v_aig_664_: *mut crate::leanh::LeanObject,
    mut v_lhs_665_: *mut crate::leanh::LeanObject,
    mut v_rhs_666_: *mut crate::leanh::LeanObject,
    mut v_curr_667_: *mut crate::leanh::LeanObject,
    mut v_hcurr_668_: *mut crate::leanh::LeanObject,
    mut v_cin_669_: *mut crate::leanh::LeanObject,
    mut v_s_670_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_671_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
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
    mut v_00_u03b1_672_: *mut crate::leanh::LeanObject,
    mut v_inst_673_: *mut crate::leanh::LeanObject,
    mut v_inst_674_: *mut crate::leanh::LeanObject,
    mut v_w_675_: *mut crate::leanh::LeanObject,
    mut v_aig_676_: *mut crate::leanh::LeanObject,
    mut v_lhs_677_: *mut crate::leanh::LeanObject,
    mut v_rhs_678_: *mut crate::leanh::LeanObject,
    mut v_curr_679_: *mut crate::leanh::LeanObject,
    mut v_hcurr_680_: *mut crate::leanh::LeanObject,
    mut v_cin_681_: *mut crate::leanh::LeanObject,
    mut v_s_682_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_683_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
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
    crate::leanh::lean_dec_ref(v_rhs_678_);
    crate::leanh::lean_dec_ref(v_lhs_677_);
    crate::leanh::lean_dec(v_w_675_);
    return v_res_683_;
}
pub unsafe fn l_Std_Tactic_BVDecide_BVExpr_bitblast_blastAdd_blast___redArg(
    mut v_inst_687_: *mut crate::leanh::LeanObject,
    mut v_inst_688_: *mut crate::leanh::LeanObject,
    mut v_w_689_: *mut crate::leanh::LeanObject,
    mut v_aig_690_: *mut crate::leanh::LeanObject,
    mut v_input_691_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_lhs_692_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_rhs_693_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_694_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_cin_695_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_696_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_697_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_lhs_692_ = crate::leanh::lean_ctor_get(v_input_691_, 0);
    v_rhs_693_ = crate::leanh::lean_ctor_get(v_input_691_, 1);
    v___x_694_ = crate::leanh::lean_unsigned_to_nat(0);
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
    mut v_inst_698_: *mut crate::leanh::LeanObject,
    mut v_inst_699_: *mut crate::leanh::LeanObject,
    mut v_w_700_: *mut crate::leanh::LeanObject,
    mut v_aig_701_: *mut crate::leanh::LeanObject,
    mut v_input_702_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_703_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_703_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastAdd_blast___redArg(
        v_inst_698_,
        v_inst_699_,
        v_w_700_,
        v_aig_701_,
        v_input_702_,
    );
    crate::leanh::lean_dec_ref(v_input_702_);
    crate::leanh::lean_dec(v_w_700_);
    return v_res_703_;
}
pub unsafe fn l_Std_Tactic_BVDecide_BVExpr_bitblast_blastAdd_blast(
    mut v_00_u03b1_704_: *mut crate::leanh::LeanObject,
    mut v_inst_705_: *mut crate::leanh::LeanObject,
    mut v_inst_706_: *mut crate::leanh::LeanObject,
    mut v_w_707_: *mut crate::leanh::LeanObject,
    mut v_aig_708_: *mut crate::leanh::LeanObject,
    mut v_input_709_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_710_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
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
    mut v_00_u03b1_711_: *mut crate::leanh::LeanObject,
    mut v_inst_712_: *mut crate::leanh::LeanObject,
    mut v_inst_713_: *mut crate::leanh::LeanObject,
    mut v_w_714_: *mut crate::leanh::LeanObject,
    mut v_aig_715_: *mut crate::leanh::LeanObject,
    mut v_input_716_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_717_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_717_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastAdd_blast(
        v_00_u03b1_711_,
        v_inst_712_,
        v_inst_713_,
        v_w_714_,
        v_aig_715_,
        v_input_716_,
    );
    crate::leanh::lean_dec_ref(v_input_716_);
    crate::leanh::lean_dec(v_w_714_);
    return v_res_717_;
}
pub unsafe fn l_Std_Tactic_BVDecide_BVExpr_bitblast_blastAdd___redArg(
    mut v_inst_718_: *mut crate::leanh::LeanObject,
    mut v_inst_719_: *mut crate::leanh::LeanObject,
    mut v_w_720_: *mut crate::leanh::LeanObject,
    mut v_aig_721_: *mut crate::leanh::LeanObject,
    mut v_input_722_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_lhs_723_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_rhs_724_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_725_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_726_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_727_: u8 = 0;
    let mut v___x_729_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_730_: u8 = 0;
    let mut v___x_732_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_733_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_734_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_735_: u8 = 0;
    let mut v_unused_736_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_737_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_738_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_lhs_723_ = crate::leanh::lean_ctor_get(v_input_722_, 0);
                v_rhs_724_ = crate::leanh::lean_ctor_get(v_input_722_, 1);
                v___x_725_ =
                    l_Std_Sat_AIG_RefVec_countKnown___redArg(v_w_720_, v_aig_721_, v_lhs_723_);
                v___x_726_ =
                    l_Std_Sat_AIG_RefVec_countKnown___redArg(v_w_720_, v_aig_721_, v_rhs_724_);
                v___x_727_ = lean_nat_dec_lt(v___x_725_, v___x_726_);
                crate::leanh::lean_dec(v___x_726_);
                crate::leanh::lean_dec(v___x_725_);
                if v___x_727_ == 0 {
                    crate::leanh::lean_inc_ref(v_rhs_724_);
                    crate::leanh::lean_inc_ref(v_lhs_723_);
                    v_isSharedCheck_735_ = (!crate::leanh::lean_is_exclusive(v_input_722_)) as u8;
                    if v_isSharedCheck_735_ == 0 {
                        v_unused_736_ = crate::leanh::lean_ctor_get(v_input_722_, 1);
                        crate::leanh::lean_dec(v_unused_736_);
                        v_unused_737_ = crate::leanh::lean_ctor_get(v_input_722_, 0);
                        crate::leanh::lean_dec(v_unused_737_);
                        v___x_729_ = v_input_722_;
                        v_isShared_730_ = v_isSharedCheck_735_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v_input_722_);
                        v___x_729_ = crate::leanh::lean_box(0);
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
                    crate::leanh::lean_dec_ref(v_input_722_);
                    return v___x_738_;
                }
            }
            1 => {
                if v_isShared_730_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_729_, 1, v_lhs_723_);
                    crate::leanh::lean_ctor_set(v___x_729_, 0, v_rhs_724_);
                    v___x_732_ = v___x_729_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_734_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_734_, 0, v_rhs_724_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_734_, 1, v_lhs_723_);
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
                crate::leanh::lean_dec_ref(v___x_732_);
                return v___x_733_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Tactic_BVDecide_BVExpr_bitblast_blastAdd___redArg___boxed(
    mut v_inst_739_: *mut crate::leanh::LeanObject,
    mut v_inst_740_: *mut crate::leanh::LeanObject,
    mut v_w_741_: *mut crate::leanh::LeanObject,
    mut v_aig_742_: *mut crate::leanh::LeanObject,
    mut v_input_743_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_744_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_744_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastAdd___redArg(
        v_inst_739_,
        v_inst_740_,
        v_w_741_,
        v_aig_742_,
        v_input_743_,
    );
    crate::leanh::lean_dec(v_w_741_);
    return v_res_744_;
}
pub unsafe fn l_Std_Tactic_BVDecide_BVExpr_bitblast_blastAdd(
    mut v_00_u03b1_745_: *mut crate::leanh::LeanObject,
    mut v_inst_746_: *mut crate::leanh::LeanObject,
    mut v_inst_747_: *mut crate::leanh::LeanObject,
    mut v_w_748_: *mut crate::leanh::LeanObject,
    mut v_aig_749_: *mut crate::leanh::LeanObject,
    mut v_input_750_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_751_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
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
    mut v_00_u03b1_752_: *mut crate::leanh::LeanObject,
    mut v_inst_753_: *mut crate::leanh::LeanObject,
    mut v_inst_754_: *mut crate::leanh::LeanObject,
    mut v_w_755_: *mut crate::leanh::LeanObject,
    mut v_aig_756_: *mut crate::leanh::LeanObject,
    mut v_input_757_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_758_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_758_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastAdd(
        v_00_u03b1_752_,
        v_inst_753_,
        v_inst_754_,
        v_w_755_,
        v_aig_756_,
        v_input_757_,
    );
    crate::leanh::lean_dec(v_w_755_);
    return v_res_758_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Operations_Add(
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
    res = runtime_initialize_Std_Sat_AIG_LawfulVecOperator(builtin);
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
pub unsafe fn meta_initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Operations_Add(
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
pub unsafe fn initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Operations_Add(
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
    res = initialize_Std_Sat_AIG_LawfulVecOperator(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Omega(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res =
        runtime_initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Operations_Add(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Operations_Add(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Operations_Add(builtin);
}
