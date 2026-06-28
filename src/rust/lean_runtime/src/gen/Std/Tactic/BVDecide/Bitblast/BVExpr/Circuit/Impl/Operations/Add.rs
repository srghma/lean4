// Lean compiler output
// Module: Std.Tactic.BVDecide.Bitblast.BVExpr.Circuit.Impl.Operations.Add
// Imports: Std.Tactic.BVDecide.Bitblast.BVExpr.Basic Std.Sat.AIG.LawfulVecOperator Init.Omega
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
use crate::lean_imports_rs::Init::Data::Nat::Bitwise::Basic::{
    lean_nat_land, lean_nat_lor, lean_nat_shiftr,
};
use crate::lean_imports_rs::Init::Prelude::{
    lean_array_fget_borrowed, lean_array_push, lean_mk_empty_array_with_capacity, lean_nat_add,
    lean_nat_dec_eq, lean_nat_dec_lt, lean_nat_mul,
};
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_alloc_ctor, lean_apply_3, lean_box, lean_ctor_get,
    lean_ctor_get_uint8, lean_ctor_set, lean_ctor_set_uint8, lean_dec, lean_dec_ref, lean_inc,
    lean_inc_ref, lean_inc_ref_n, lean_io_result_is_error, lean_io_result_mk_ok, lean_is_exclusive,
    lean_unsigned_to_nat,
};
pub static l_Std_Tactic_BVDecide_BVExpr_bitblast_blastAdd_blast___redArg___closed__0_value:
    LeanCtorObject<2> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 8) as u16,
        other: 1,
        tag: 0,
    },
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut LeanObject,
        0 as *mut LeanObject,
    ],
};
static mut l_Std_Tactic_BVDecide_BVExpr_bitblast_blastAdd_blast___redArg___closed__0:
    *mut LeanObject = core::ptr::addr_of!(
    l_Std_Tactic_BVDecide_BVExpr_bitblast_blastAdd_blast___redArg___closed__0_value
) as *mut LeanObject;
pub unsafe fn l_Std_Tactic_BVDecide_BVExpr_bitblast_FullAdderInput_cast___redArg(
    mut v_val_380_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_lhs_381_: *mut LeanObject = core::ptr::null_mut();
    let mut v_rhs_382_: *mut LeanObject = core::ptr::null_mut();
    let mut v_cin_383_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_385_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_386_: u8 = 0;
    let mut v_gate_387_: *mut LeanObject = core::ptr::null_mut();
    let mut v_invert_388_: u8 = 0;
    let mut v___x_390_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_391_: u8 = 0;
    let mut v_gate_392_: *mut LeanObject = core::ptr::null_mut();
    let mut v_invert_393_: u8 = 0;
    let mut v___x_395_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_396_: u8 = 0;
    let mut v_gate_397_: *mut LeanObject = core::ptr::null_mut();
    let mut v_invert_398_: u8 = 0;
    let mut v___x_400_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_401_: u8 = 0;
    let mut v___x_403_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_405_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_407_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_409_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_410_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_411_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_412_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_413_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_414_: u8 = 0;
    let mut v_isSharedCheck_415_: u8 = 0;
    let mut v_isSharedCheck_416_: u8 = 0;
    let mut v_isSharedCheck_417_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_lhs_381_ = lean_ctor_get(v_val_380_, 0);
                v_rhs_382_ = lean_ctor_get(v_val_380_, 1);
                v_cin_383_ = lean_ctor_get(v_val_380_, 2);
                v_isSharedCheck_417_ = (!lean_is_exclusive(v_val_380_)) as u8;
                if v_isSharedCheck_417_ == 0 {
                    v___x_385_ = v_val_380_;
                    v_isShared_386_ = v_isSharedCheck_417_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_cin_383_);
                    lean_inc(v_rhs_382_);
                    lean_inc(v_lhs_381_);
                    lean_dec(v_val_380_);
                    v___x_385_ = lean_box(0);
                    v_isShared_386_ = v_isSharedCheck_417_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_gate_387_ = lean_ctor_get(v_lhs_381_, 0);
                v_invert_388_ = lean_ctor_get_uint8(
                    v_lhs_381_,
                    (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                );
                v_isSharedCheck_416_ = (!lean_is_exclusive(v_lhs_381_)) as u8;
                if v_isSharedCheck_416_ == 0 {
                    v___x_390_ = v_lhs_381_;
                    v_isShared_391_ = v_isSharedCheck_416_;
                    state = 2;
                    continue;
                } else {
                    lean_inc(v_gate_387_);
                    lean_dec(v_lhs_381_);
                    v___x_390_ = lean_box(0);
                    v_isShared_391_ = v_isSharedCheck_416_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v_gate_392_ = lean_ctor_get(v_rhs_382_, 0);
                v_invert_393_ = lean_ctor_get_uint8(
                    v_rhs_382_,
                    (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                );
                v_isSharedCheck_415_ = (!lean_is_exclusive(v_rhs_382_)) as u8;
                if v_isSharedCheck_415_ == 0 {
                    v___x_395_ = v_rhs_382_;
                    v_isShared_396_ = v_isSharedCheck_415_;
                    state = 3;
                    continue;
                } else {
                    lean_inc(v_gate_392_);
                    lean_dec(v_rhs_382_);
                    v___x_395_ = lean_box(0);
                    v_isShared_396_ = v_isSharedCheck_415_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v_gate_397_ = lean_ctor_get(v_cin_383_, 0);
                v_invert_398_ = lean_ctor_get_uint8(
                    v_cin_383_,
                    (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                );
                v_isSharedCheck_414_ = (!lean_is_exclusive(v_cin_383_)) as u8;
                if v_isSharedCheck_414_ == 0 {
                    v___x_400_ = v_cin_383_;
                    v_isShared_401_ = v_isSharedCheck_414_;
                    state = 4;
                    continue;
                } else {
                    lean_inc(v_gate_397_);
                    lean_dec(v_cin_383_);
                    v___x_400_ = lean_box(0);
                    v_isShared_401_ = v_isSharedCheck_414_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                if v_isShared_401_ == 0 {
                    lean_ctor_set(v___x_400_, 0, v_gate_387_);
                    v___x_403_ = v___x_400_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_413_ = lean_alloc_ctor(0, 1, (1) as u32);
                    lean_ctor_set(v_reuseFailAlloc_413_, 0, v_gate_387_);
                    v___x_403_ = v_reuseFailAlloc_413_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                lean_ctor_set_uint8(
                    v___x_403_,
                    (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                    v_invert_388_,
                );
                if v_isShared_396_ == 0 {
                    v___x_405_ = v___x_395_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_412_ = lean_alloc_ctor(0, 1, (1) as u32);
                    lean_ctor_set(v_reuseFailAlloc_412_, 0, v_gate_392_);
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_412_,
                        (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                        v_invert_393_,
                    );
                    v___x_405_ = v_reuseFailAlloc_412_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                if v_isShared_391_ == 0 {
                    lean_ctor_set(v___x_390_, 0, v_gate_397_);
                    v___x_407_ = v___x_390_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_411_ = lean_alloc_ctor(0, 1, (1) as u32);
                    lean_ctor_set(v_reuseFailAlloc_411_, 0, v_gate_397_);
                    v___x_407_ = v_reuseFailAlloc_411_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                lean_ctor_set_uint8(
                    v___x_407_,
                    (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                    v_invert_398_,
                );
                if v_isShared_386_ == 0 {
                    lean_ctor_set(v___x_385_, 2, v___x_407_);
                    lean_ctor_set(v___x_385_, 1, v___x_405_);
                    lean_ctor_set(v___x_385_, 0, v___x_403_);
                    v___x_409_ = v___x_385_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_410_ = lean_alloc_ctor(0, 3, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_410_, 0, v___x_403_);
                    lean_ctor_set(v_reuseFailAlloc_410_, 1, v___x_405_);
                    lean_ctor_set(v_reuseFailAlloc_410_, 2, v___x_407_);
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
    mut v_00_u03b1_418_: *mut LeanObject,
    mut v_inst_419_: *mut LeanObject,
    mut v_inst_420_: *mut LeanObject,
    mut v_aig1_421_: *mut LeanObject,
    mut v_aig2_422_: *mut LeanObject,
    mut v_val_423_: *mut LeanObject,
    mut v_h_424_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_425_: *mut LeanObject = core::ptr::null_mut();
    v___x_425_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_FullAdderInput_cast___redArg(v_val_423_);
    return v___x_425_;
}
pub unsafe fn l_Std_Tactic_BVDecide_BVExpr_bitblast_FullAdderInput_cast___boxed(
    mut v_00_u03b1_426_: *mut LeanObject,
    mut v_inst_427_: *mut LeanObject,
    mut v_inst_428_: *mut LeanObject,
    mut v_aig1_429_: *mut LeanObject,
    mut v_aig2_430_: *mut LeanObject,
    mut v_val_431_: *mut LeanObject,
    mut v_h_432_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_433_: *mut LeanObject = core::ptr::null_mut();
    v_res_433_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_FullAdderInput_cast(
        v_00_u03b1_426_,
        v_inst_427_,
        v_inst_428_,
        v_aig1_429_,
        v_aig2_430_,
        v_val_431_,
        v_h_432_,
    );
    lean_dec_ref(v_aig2_430_);
    lean_dec_ref(v_aig1_429_);
    lean_dec_ref(v_inst_428_);
    lean_dec_ref(v_inst_427_);
    return v_res_433_;
}
pub unsafe fn l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Operations_Add_0__Std_Tactic_BVDecide_BVExpr_bitblast_FullAdderInput_cast_match__1_splitter___redArg(
    mut v_val_434_: *mut LeanObject,
    mut v_h__1_435_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_lhs_436_: *mut LeanObject = core::ptr::null_mut();
    let mut v_rhs_437_: *mut LeanObject = core::ptr::null_mut();
    let mut v_cin_438_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_439_: *mut LeanObject = core::ptr::null_mut();
    v_lhs_436_ = lean_ctor_get(v_val_434_, 0);
    lean_inc_ref(v_lhs_436_);
    v_rhs_437_ = lean_ctor_get(v_val_434_, 1);
    lean_inc_ref(v_rhs_437_);
    v_cin_438_ = lean_ctor_get(v_val_434_, 2);
    lean_inc_ref(v_cin_438_);
    lean_dec_ref(v_val_434_);
    v___x_439_ = lean_apply_3(v_h__1_435_, v_lhs_436_, v_rhs_437_, v_cin_438_);
    return v___x_439_;
}
pub unsafe fn l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Operations_Add_0__Std_Tactic_BVDecide_BVExpr_bitblast_FullAdderInput_cast_match__1_splitter(
    mut v_00_u03b1_440_: *mut LeanObject,
    mut v_inst_441_: *mut LeanObject,
    mut v_inst_442_: *mut LeanObject,
    mut v_aig1_443_: *mut LeanObject,
    mut v_motive_444_: *mut LeanObject,
    mut v_val_445_: *mut LeanObject,
    mut v_h__1_446_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_lhs_447_: *mut LeanObject = core::ptr::null_mut();
    let mut v_rhs_448_: *mut LeanObject = core::ptr::null_mut();
    let mut v_cin_449_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_450_: *mut LeanObject = core::ptr::null_mut();
    v_lhs_447_ = lean_ctor_get(v_val_445_, 0);
    lean_inc_ref(v_lhs_447_);
    v_rhs_448_ = lean_ctor_get(v_val_445_, 1);
    lean_inc_ref(v_rhs_448_);
    v_cin_449_ = lean_ctor_get(v_val_445_, 2);
    lean_inc_ref(v_cin_449_);
    lean_dec_ref(v_val_445_);
    v___x_450_ = lean_apply_3(v_h__1_446_, v_lhs_447_, v_rhs_448_, v_cin_449_);
    return v___x_450_;
}
pub unsafe fn l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Operations_Add_0__Std_Tactic_BVDecide_BVExpr_bitblast_FullAdderInput_cast_match__1_splitter___boxed(
    mut v_00_u03b1_451_: *mut LeanObject,
    mut v_inst_452_: *mut LeanObject,
    mut v_inst_453_: *mut LeanObject,
    mut v_aig1_454_: *mut LeanObject,
    mut v_motive_455_: *mut LeanObject,
    mut v_val_456_: *mut LeanObject,
    mut v_h__1_457_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_458_: *mut LeanObject = core::ptr::null_mut();
    v_res_458_ = l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Operations_Add_0__Std_Tactic_BVDecide_BVExpr_bitblast_FullAdderInput_cast_match__1_splitter(v_00_u03b1_451_, v_inst_452_, v_inst_453_, v_aig1_454_, v_motive_455_, v_val_456_, v_h__1_457_);
    lean_dec_ref(v_aig1_454_);
    lean_dec_ref(v_inst_453_);
    lean_dec_ref(v_inst_452_);
    return v_res_458_;
}
pub unsafe fn l_Std_Tactic_BVDecide_BVExpr_bitblast_mkFullAdderOut___redArg(
    mut v_inst_459_: *mut LeanObject,
    mut v_inst_460_: *mut LeanObject,
    mut v_aig_461_: *mut LeanObject,
    mut v_input_462_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_lhs_463_: *mut LeanObject = core::ptr::null_mut();
    let mut v_rhs_464_: *mut LeanObject = core::ptr::null_mut();
    let mut v_cin_465_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_466_: *mut LeanObject = core::ptr::null_mut();
    let mut v_res_467_: *mut LeanObject = core::ptr::null_mut();
    let mut v_aig_468_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ref_469_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_471_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_472_: u8 = 0;
    let mut v_gate_473_: *mut LeanObject = core::ptr::null_mut();
    let mut v_invert_474_: u8 = 0;
    let mut v___x_476_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_477_: u8 = 0;
    let mut v_cin_479_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_481_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_482_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_483_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_484_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_485_: u8 = 0;
    let mut v_isSharedCheck_486_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_lhs_463_ = lean_ctor_get(v_input_462_, 0);
                lean_inc_ref(v_lhs_463_);
                v_rhs_464_ = lean_ctor_get(v_input_462_, 1);
                lean_inc_ref(v_rhs_464_);
                v_cin_465_ = lean_ctor_get(v_input_462_, 2);
                lean_inc_ref(v_cin_465_);
                lean_dec_ref(v_input_462_);
                v___x_466_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_466_, 0, v_lhs_463_);
                lean_ctor_set(v___x_466_, 1, v_rhs_464_);
                lean_inc_ref(v_inst_460_);
                lean_inc_ref(v_inst_459_);
                v_res_467_ = l_Std_Sat_AIG_mkXorCached___redArg(
                    v_inst_459_,
                    v_inst_460_,
                    v_aig_461_,
                    v___x_466_,
                );
                v_aig_468_ = lean_ctor_get(v_res_467_, 0);
                v_ref_469_ = lean_ctor_get(v_res_467_, 1);
                v_isSharedCheck_486_ = (!lean_is_exclusive(v_res_467_)) as u8;
                if v_isSharedCheck_486_ == 0 {
                    v___x_471_ = v_res_467_;
                    v_isShared_472_ = v_isSharedCheck_486_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_ref_469_);
                    lean_inc(v_aig_468_);
                    lean_dec(v_res_467_);
                    v___x_471_ = lean_box(0);
                    v_isShared_472_ = v_isSharedCheck_486_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_gate_473_ = lean_ctor_get(v_cin_465_, 0);
                v_invert_474_ = lean_ctor_get_uint8(
                    v_cin_465_,
                    (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                );
                v_isSharedCheck_485_ = (!lean_is_exclusive(v_cin_465_)) as u8;
                if v_isSharedCheck_485_ == 0 {
                    v___x_476_ = v_cin_465_;
                    v_isShared_477_ = v_isSharedCheck_485_;
                    state = 2;
                    continue;
                } else {
                    lean_inc(v_gate_473_);
                    lean_dec(v_cin_465_);
                    v___x_476_ = lean_box(0);
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
                    v_reuseFailAlloc_484_ = lean_alloc_ctor(0, 1, (1) as u32);
                    lean_ctor_set(v_reuseFailAlloc_484_, 0, v_gate_473_);
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_484_,
                        (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                        v_invert_474_,
                    );
                    v_cin_479_ = v_reuseFailAlloc_484_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_472_ == 0 {
                    lean_ctor_set(v___x_471_, 1, v_cin_479_);
                    lean_ctor_set(v___x_471_, 0, v_ref_469_);
                    v___x_481_ = v___x_471_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_483_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_483_, 0, v_ref_469_);
                    lean_ctor_set(v_reuseFailAlloc_483_, 1, v_cin_479_);
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
    mut v_00_u03b1_487_: *mut LeanObject,
    mut v_inst_488_: *mut LeanObject,
    mut v_inst_489_: *mut LeanObject,
    mut v_aig_490_: *mut LeanObject,
    mut v_input_491_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_492_: *mut LeanObject = core::ptr::null_mut();
    v___x_492_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_mkFullAdderOut___redArg(
        v_inst_488_,
        v_inst_489_,
        v_aig_490_,
        v_input_491_,
    );
    return v___x_492_;
}
pub unsafe fn l_Std_Tactic_BVDecide_BVExpr_bitblast_mkFullAdderCarry___redArg(
    mut v_inst_493_: *mut LeanObject,
    mut v_inst_494_: *mut LeanObject,
    mut v_aig_495_: *mut LeanObject,
    mut v_input_496_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_lhs_497_: *mut LeanObject = core::ptr::null_mut();
    let mut v_rhs_498_: *mut LeanObject = core::ptr::null_mut();
    let mut v_cin_499_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_500_: *mut LeanObject = core::ptr::null_mut();
    let mut v_res_501_: *mut LeanObject = core::ptr::null_mut();
    let mut v_aig_502_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ref_503_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_505_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_506_: u8 = 0;
    let mut v_gate_507_: *mut LeanObject = core::ptr::null_mut();
    let mut v_invert_508_: u8 = 0;
    let mut v___x_510_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_511_: u8 = 0;
    let mut v_gate_512_: *mut LeanObject = core::ptr::null_mut();
    let mut v_invert_513_: u8 = 0;
    let mut v___x_515_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_516_: u8 = 0;
    let mut v_gate_517_: *mut LeanObject = core::ptr::null_mut();
    let mut v_invert_518_: u8 = 0;
    let mut v___x_520_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_521_: u8 = 0;
    let mut v_cin_523_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_525_: *mut LeanObject = core::ptr::null_mut();
    let mut v_res_526_: *mut LeanObject = core::ptr::null_mut();
    let mut v_aig_527_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ref_528_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_530_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_531_: u8 = 0;
    let mut v_lhs_533_: *mut LeanObject = core::ptr::null_mut();
    let mut v_rhs_535_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_537_: *mut LeanObject = core::ptr::null_mut();
    let mut v_res_538_: *mut LeanObject = core::ptr::null_mut();
    let mut v_aig_539_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ref_540_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_542_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_543_: u8 = 0;
    let mut v_gate_544_: *mut LeanObject = core::ptr::null_mut();
    let mut v_invert_545_: u8 = 0;
    let mut v___x_547_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_548_: u8 = 0;
    let mut v_lorRef_550_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_552_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_553_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_554_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_555_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_556_: u8 = 0;
    let mut v_isSharedCheck_557_: u8 = 0;
    let mut v_reuseFailAlloc_558_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_559_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_560_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_561_: u8 = 0;
    let mut v_reuseFailAlloc_562_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_563_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_564_: u8 = 0;
    let mut v_isSharedCheck_565_: u8 = 0;
    let mut v_isSharedCheck_566_: u8 = 0;
    let mut v_isSharedCheck_567_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_lhs_497_ = lean_ctor_get(v_input_496_, 0);
                lean_inc_ref_n(v_lhs_497_, 2);
                v_rhs_498_ = lean_ctor_get(v_input_496_, 1);
                lean_inc_ref_n(v_rhs_498_, 2);
                v_cin_499_ = lean_ctor_get(v_input_496_, 2);
                lean_inc_ref(v_cin_499_);
                lean_dec_ref(v_input_496_);
                v___x_500_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_500_, 0, v_lhs_497_);
                lean_ctor_set(v___x_500_, 1, v_rhs_498_);
                lean_inc_ref(v_inst_494_);
                lean_inc_ref(v_inst_493_);
                v_res_501_ = l_Std_Sat_AIG_mkXorCached___redArg(
                    v_inst_493_,
                    v_inst_494_,
                    v_aig_495_,
                    v___x_500_,
                );
                v_aig_502_ = lean_ctor_get(v_res_501_, 0);
                v_ref_503_ = lean_ctor_get(v_res_501_, 1);
                v_isSharedCheck_567_ = (!lean_is_exclusive(v_res_501_)) as u8;
                if v_isSharedCheck_567_ == 0 {
                    v___x_505_ = v_res_501_;
                    v_isShared_506_ = v_isSharedCheck_567_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_ref_503_);
                    lean_inc(v_aig_502_);
                    lean_dec(v_res_501_);
                    v___x_505_ = lean_box(0);
                    v_isShared_506_ = v_isSharedCheck_567_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_gate_507_ = lean_ctor_get(v_lhs_497_, 0);
                v_invert_508_ = lean_ctor_get_uint8(
                    v_lhs_497_,
                    (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                );
                v_isSharedCheck_566_ = (!lean_is_exclusive(v_lhs_497_)) as u8;
                if v_isSharedCheck_566_ == 0 {
                    v___x_510_ = v_lhs_497_;
                    v_isShared_511_ = v_isSharedCheck_566_;
                    state = 2;
                    continue;
                } else {
                    lean_inc(v_gate_507_);
                    lean_dec(v_lhs_497_);
                    v___x_510_ = lean_box(0);
                    v_isShared_511_ = v_isSharedCheck_566_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v_gate_512_ = lean_ctor_get(v_rhs_498_, 0);
                v_invert_513_ = lean_ctor_get_uint8(
                    v_rhs_498_,
                    (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                );
                v_isSharedCheck_565_ = (!lean_is_exclusive(v_rhs_498_)) as u8;
                if v_isSharedCheck_565_ == 0 {
                    v___x_515_ = v_rhs_498_;
                    v_isShared_516_ = v_isSharedCheck_565_;
                    state = 3;
                    continue;
                } else {
                    lean_inc(v_gate_512_);
                    lean_dec(v_rhs_498_);
                    v___x_515_ = lean_box(0);
                    v_isShared_516_ = v_isSharedCheck_565_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v_gate_517_ = lean_ctor_get(v_cin_499_, 0);
                v_invert_518_ = lean_ctor_get_uint8(
                    v_cin_499_,
                    (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                );
                v_isSharedCheck_564_ = (!lean_is_exclusive(v_cin_499_)) as u8;
                if v_isSharedCheck_564_ == 0 {
                    v___x_520_ = v_cin_499_;
                    v_isShared_521_ = v_isSharedCheck_564_;
                    state = 4;
                    continue;
                } else {
                    lean_inc(v_gate_517_);
                    lean_dec(v_cin_499_);
                    v___x_520_ = lean_box(0);
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
                    v_reuseFailAlloc_563_ = lean_alloc_ctor(0, 1, (1) as u32);
                    lean_ctor_set(v_reuseFailAlloc_563_, 0, v_gate_517_);
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_563_,
                        (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                        v_invert_518_,
                    );
                    v_cin_523_ = v_reuseFailAlloc_563_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                if v_isShared_506_ == 0 {
                    lean_ctor_set(v___x_505_, 1, v_cin_523_);
                    lean_ctor_set(v___x_505_, 0, v_ref_503_);
                    v___x_525_ = v___x_505_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_562_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_562_, 0, v_ref_503_);
                    lean_ctor_set(v_reuseFailAlloc_562_, 1, v_cin_523_);
                    v___x_525_ = v_reuseFailAlloc_562_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                lean_inc_ref(v_inst_494_);
                lean_inc_ref(v_inst_493_);
                v_res_526_ = l_Std_Sat_AIG_mkGateCached___redArg(
                    v_inst_493_,
                    v_inst_494_,
                    v_aig_502_,
                    v___x_525_,
                );
                v_aig_527_ = lean_ctor_get(v_res_526_, 0);
                v_ref_528_ = lean_ctor_get(v_res_526_, 1);
                v_isSharedCheck_561_ = (!lean_is_exclusive(v_res_526_)) as u8;
                if v_isSharedCheck_561_ == 0 {
                    v___x_530_ = v_res_526_;
                    v_isShared_531_ = v_isSharedCheck_561_;
                    state = 7;
                    continue;
                } else {
                    lean_inc(v_ref_528_);
                    lean_inc(v_aig_527_);
                    lean_dec(v_res_526_);
                    v___x_530_ = lean_box(0);
                    v_isShared_531_ = v_isSharedCheck_561_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                if v_isShared_516_ == 0 {
                    lean_ctor_set(v___x_515_, 0, v_gate_507_);
                    v_lhs_533_ = v___x_515_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_560_ = lean_alloc_ctor(0, 1, (1) as u32);
                    lean_ctor_set(v_reuseFailAlloc_560_, 0, v_gate_507_);
                    v_lhs_533_ = v_reuseFailAlloc_560_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                lean_ctor_set_uint8(
                    v_lhs_533_,
                    (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                    v_invert_508_,
                );
                if v_isShared_511_ == 0 {
                    lean_ctor_set(v___x_510_, 0, v_gate_512_);
                    v_rhs_535_ = v___x_510_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_559_ = lean_alloc_ctor(0, 1, (1) as u32);
                    lean_ctor_set(v_reuseFailAlloc_559_, 0, v_gate_512_);
                    v_rhs_535_ = v_reuseFailAlloc_559_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                lean_ctor_set_uint8(
                    v_rhs_535_,
                    (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                    v_invert_513_,
                );
                if v_isShared_531_ == 0 {
                    lean_ctor_set(v___x_530_, 1, v_rhs_535_);
                    lean_ctor_set(v___x_530_, 0, v_lhs_533_);
                    v___x_537_ = v___x_530_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_558_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_558_, 0, v_lhs_533_);
                    lean_ctor_set(v_reuseFailAlloc_558_, 1, v_rhs_535_);
                    v___x_537_ = v_reuseFailAlloc_558_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                lean_inc_ref(v_inst_494_);
                lean_inc_ref(v_inst_493_);
                v_res_538_ = l_Std_Sat_AIG_mkGateCached___redArg(
                    v_inst_493_,
                    v_inst_494_,
                    v_aig_527_,
                    v___x_537_,
                );
                v_aig_539_ = lean_ctor_get(v_res_538_, 0);
                v_ref_540_ = lean_ctor_get(v_res_538_, 1);
                v_isSharedCheck_557_ = (!lean_is_exclusive(v_res_538_)) as u8;
                if v_isSharedCheck_557_ == 0 {
                    v___x_542_ = v_res_538_;
                    v_isShared_543_ = v_isSharedCheck_557_;
                    state = 11;
                    continue;
                } else {
                    lean_inc(v_ref_540_);
                    lean_inc(v_aig_539_);
                    lean_dec(v_res_538_);
                    v___x_542_ = lean_box(0);
                    v_isShared_543_ = v_isSharedCheck_557_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                v_gate_544_ = lean_ctor_get(v_ref_528_, 0);
                v_invert_545_ = lean_ctor_get_uint8(
                    v_ref_528_,
                    (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                );
                v_isSharedCheck_556_ = (!lean_is_exclusive(v_ref_528_)) as u8;
                if v_isSharedCheck_556_ == 0 {
                    v___x_547_ = v_ref_528_;
                    v_isShared_548_ = v_isSharedCheck_556_;
                    state = 12;
                    continue;
                } else {
                    lean_inc(v_gate_544_);
                    lean_dec(v_ref_528_);
                    v___x_547_ = lean_box(0);
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
                    v_reuseFailAlloc_555_ = lean_alloc_ctor(0, 1, (1) as u32);
                    lean_ctor_set(v_reuseFailAlloc_555_, 0, v_gate_544_);
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_555_,
                        (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                        v_invert_545_,
                    );
                    v_lorRef_550_ = v_reuseFailAlloc_555_;
                    state = 13;
                    continue;
                }
            }
            13 => {
                if v_isShared_543_ == 0 {
                    lean_ctor_set(v___x_542_, 0, v_lorRef_550_);
                    v___x_552_ = v___x_542_;
                    state = 14;
                    continue;
                } else {
                    v_reuseFailAlloc_554_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_554_, 0, v_lorRef_550_);
                    lean_ctor_set(v_reuseFailAlloc_554_, 1, v_ref_540_);
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
    mut v_00_u03b1_568_: *mut LeanObject,
    mut v_inst_569_: *mut LeanObject,
    mut v_inst_570_: *mut LeanObject,
    mut v_aig_571_: *mut LeanObject,
    mut v_input_572_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_573_: *mut LeanObject = core::ptr::null_mut();
    v___x_573_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_mkFullAdderCarry___redArg(
        v_inst_569_,
        v_inst_570_,
        v_aig_571_,
        v_input_572_,
    );
    return v___x_573_;
}
pub unsafe fn l_Std_Tactic_BVDecide_BVExpr_bitblast_mkFullAdder___redArg(
    mut v_inst_574_: *mut LeanObject,
    mut v_inst_575_: *mut LeanObject,
    mut v_aig_576_: *mut LeanObject,
    mut v_input_577_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_578_: *mut LeanObject = core::ptr::null_mut();
    let mut v_aig_579_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ref_580_: *mut LeanObject = core::ptr::null_mut();
    let mut v_input_581_: *mut LeanObject = core::ptr::null_mut();
    let mut v_res_582_: *mut LeanObject = core::ptr::null_mut();
    let mut v_aig_583_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ref_584_: *mut LeanObject = core::ptr::null_mut();
    let mut v_gate_585_: *mut LeanObject = core::ptr::null_mut();
    let mut v_invert_586_: u8 = 0;
    let mut v___x_588_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_589_: u8 = 0;
    let mut v_outRef_591_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_592_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_593_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_594_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                lean_inc_ref(v_input_577_);
                lean_inc_ref(v_inst_575_);
                lean_inc_ref(v_inst_574_);
                v_res_578_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_mkFullAdderOut___redArg(
                    v_inst_574_,
                    v_inst_575_,
                    v_aig_576_,
                    v_input_577_,
                );
                v_aig_579_ = lean_ctor_get(v_res_578_, 0);
                lean_inc_ref(v_aig_579_);
                v_ref_580_ = lean_ctor_get(v_res_578_, 1);
                lean_inc_ref(v_ref_580_);
                lean_dec_ref(v_res_578_);
                v_input_581_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_FullAdderInput_cast___redArg(
                    v_input_577_,
                );
                v_res_582_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_mkFullAdderCarry___redArg(
                    v_inst_574_,
                    v_inst_575_,
                    v_aig_579_,
                    v_input_581_,
                );
                v_aig_583_ = lean_ctor_get(v_res_582_, 0);
                lean_inc_ref(v_aig_583_);
                v_ref_584_ = lean_ctor_get(v_res_582_, 1);
                lean_inc_ref(v_ref_584_);
                lean_dec_ref(v_res_582_);
                v_gate_585_ = lean_ctor_get(v_ref_580_, 0);
                v_invert_586_ = lean_ctor_get_uint8(
                    v_ref_580_,
                    (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                );
                v_isSharedCheck_594_ = (!lean_is_exclusive(v_ref_580_)) as u8;
                if v_isSharedCheck_594_ == 0 {
                    v___x_588_ = v_ref_580_;
                    v_isShared_589_ = v_isSharedCheck_594_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_gate_585_);
                    lean_dec(v_ref_580_);
                    v___x_588_ = lean_box(0);
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
                    v_reuseFailAlloc_593_ = lean_alloc_ctor(0, 1, (1) as u32);
                    lean_ctor_set(v_reuseFailAlloc_593_, 0, v_gate_585_);
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_593_,
                        (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                        v_invert_586_,
                    );
                    v_outRef_591_ = v_reuseFailAlloc_593_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_592_ = lean_alloc_ctor(0, 3, (0) as u32);
                lean_ctor_set(v___x_592_, 0, v_aig_583_);
                lean_ctor_set(v___x_592_, 1, v_outRef_591_);
                lean_ctor_set(v___x_592_, 2, v_ref_584_);
                return v___x_592_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Tactic_BVDecide_BVExpr_bitblast_mkFullAdder(
    mut v_00_u03b1_595_: *mut LeanObject,
    mut v_inst_596_: *mut LeanObject,
    mut v_inst_597_: *mut LeanObject,
    mut v_aig_598_: *mut LeanObject,
    mut v_input_599_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_600_: *mut LeanObject = core::ptr::null_mut();
    v___x_600_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_mkFullAdder___redArg(
        v_inst_596_,
        v_inst_597_,
        v_aig_598_,
        v_input_599_,
    );
    return v___x_600_;
}
pub unsafe fn l_Std_Tactic_BVDecide_BVExpr_bitblast_blastAdd_go___redArg(
    mut v_inst_601_: *mut LeanObject,
    mut v_inst_602_: *mut LeanObject,
    mut v_w_603_: *mut LeanObject,
    mut v_aig_604_: *mut LeanObject,
    mut v_lhs_605_: *mut LeanObject,
    mut v_rhs_606_: *mut LeanObject,
    mut v_curr_607_: *mut LeanObject,
    mut v_cin_608_: *mut LeanObject,
    mut v_s_609_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___y_611_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_612_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_613_: *mut LeanObject = core::ptr::null_mut();
    let mut v_res_614_: *mut LeanObject = core::ptr::null_mut();
    let mut v_out_615_: *mut LeanObject = core::ptr::null_mut();
    let mut v_aig_616_: *mut LeanObject = core::ptr::null_mut();
    let mut v_cout_617_: *mut LeanObject = core::ptr::null_mut();
    let mut v_gate_618_: *mut LeanObject = core::ptr::null_mut();
    let mut v_invert_619_: u8 = 0;
    let mut v___x_620_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_621_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_622_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_623_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_624_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_625_: *mut LeanObject = core::ptr::null_mut();
    let mut v_s_626_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_628_: u8 = 0;
    let mut v___y_630_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ref_631_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_632_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_633_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_634_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_635_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_636_: u8 = 0;
    let mut v___x_637_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_638_: u8 = 0;
    let mut v___x_639_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_640_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ref_641_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_642_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_643_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_644_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_645_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_646_: u8 = 0;
    let mut v___x_647_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_648_: u8 = 0;
    let mut v___x_649_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_628_ = lean_nat_dec_lt(v_curr_607_, v_w_603_);
                if v___x_628_ == 0 {
                    lean_dec_ref(v_cin_608_);
                    lean_dec(v_curr_607_);
                    lean_dec_ref(v_inst_602_);
                    lean_dec_ref(v_inst_601_);
                    v___x_640_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v___x_640_, 0, v_aig_604_);
                    lean_ctor_set(v___x_640_, 1, v_s_609_);
                    return v___x_640_;
                } else {
                    v_ref_641_ = lean_array_fget_borrowed(v_lhs_605_, v_curr_607_);
                    v___x_642_ = lean_unsigned_to_nat(1);
                    v___x_643_ = lean_nat_shiftr(v_ref_641_, v___x_642_);
                    v___x_644_ = lean_nat_land(v___x_642_, v_ref_641_);
                    v___x_645_ = lean_unsigned_to_nat(0);
                    v___x_646_ = lean_nat_dec_eq(v___x_644_, v___x_645_);
                    lean_dec(v___x_644_);
                    if v___x_646_ == 0 {
                        v___x_647_ = lean_alloc_ctor(0, 1, (1) as u32);
                        lean_ctor_set(v___x_647_, 0, v___x_643_);
                        lean_ctor_set_uint8(
                            v___x_647_,
                            (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                            v___x_628_,
                        );
                        v___y_630_ = v___x_647_;
                        state = 2;
                        continue;
                    } else {
                        v___x_648_ = 0;
                        v___x_649_ = lean_alloc_ctor(0, 1, (1) as u32);
                        lean_ctor_set(v___x_649_, 0, v___x_643_);
                        lean_ctor_set_uint8(
                            v___x_649_,
                            (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                            v___x_648_,
                        );
                        v___y_630_ = v___x_649_;
                        state = 2;
                        continue;
                    }
                }
            }
            1 => {
                v___x_613_ = lean_alloc_ctor(0, 3, (0) as u32);
                lean_ctor_set(v___x_613_, 0, v___y_611_);
                lean_ctor_set(v___x_613_, 1, v___y_612_);
                lean_ctor_set(v___x_613_, 2, v_cin_608_);
                lean_inc_ref(v_inst_602_);
                lean_inc_ref(v_inst_601_);
                v_res_614_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_mkFullAdder___redArg(
                    v_inst_601_,
                    v_inst_602_,
                    v_aig_604_,
                    v___x_613_,
                );
                v_out_615_ = lean_ctor_get(v_res_614_, 1);
                lean_inc_ref(v_out_615_);
                v_aig_616_ = lean_ctor_get(v_res_614_, 0);
                lean_inc_ref(v_aig_616_);
                v_cout_617_ = lean_ctor_get(v_res_614_, 2);
                lean_inc_ref(v_cout_617_);
                lean_dec_ref(v_res_614_);
                v_gate_618_ = lean_ctor_get(v_out_615_, 0);
                lean_inc(v_gate_618_);
                v_invert_619_ = lean_ctor_get_uint8(
                    v_out_615_,
                    (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                );
                lean_dec_ref(v_out_615_);
                v___x_620_ = lean_unsigned_to_nat(1);
                v___x_621_ = lean_nat_add(v_curr_607_, v___x_620_);
                lean_dec(v_curr_607_);
                v___x_622_ = lean_unsigned_to_nat(2);
                v___x_623_ = lean_nat_mul(v_gate_618_, v___x_622_);
                lean_dec(v_gate_618_);
                v___x_624_ = l_Bool_toNat(v_invert_619_);
                v___x_625_ = lean_nat_lor(v___x_623_, v___x_624_);
                lean_dec(v___x_624_);
                lean_dec(v___x_623_);
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
                v___x_632_ = lean_unsigned_to_nat(1);
                v___x_633_ = lean_nat_shiftr(v_ref_631_, v___x_632_);
                v___x_634_ = lean_nat_land(v___x_632_, v_ref_631_);
                v___x_635_ = lean_unsigned_to_nat(0);
                v___x_636_ = lean_nat_dec_eq(v___x_634_, v___x_635_);
                lean_dec(v___x_634_);
                if v___x_636_ == 0 {
                    v___x_637_ = lean_alloc_ctor(0, 1, (1) as u32);
                    lean_ctor_set(v___x_637_, 0, v___x_633_);
                    lean_ctor_set_uint8(
                        v___x_637_,
                        (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                        v___x_628_,
                    );
                    v___y_611_ = v___y_630_;
                    v___y_612_ = v___x_637_;
                    state = 1;
                    continue;
                } else {
                    v___x_638_ = 0;
                    v___x_639_ = lean_alloc_ctor(0, 1, (1) as u32);
                    lean_ctor_set(v___x_639_, 0, v___x_633_);
                    lean_ctor_set_uint8(
                        v___x_639_,
                        (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
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
    mut v_inst_650_: *mut LeanObject,
    mut v_inst_651_: *mut LeanObject,
    mut v_w_652_: *mut LeanObject,
    mut v_aig_653_: *mut LeanObject,
    mut v_lhs_654_: *mut LeanObject,
    mut v_rhs_655_: *mut LeanObject,
    mut v_curr_656_: *mut LeanObject,
    mut v_cin_657_: *mut LeanObject,
    mut v_s_658_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_659_: *mut LeanObject = core::ptr::null_mut();
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
    lean_dec_ref(v_rhs_655_);
    lean_dec_ref(v_lhs_654_);
    lean_dec(v_w_652_);
    return v_res_659_;
}
pub unsafe fn l_Std_Tactic_BVDecide_BVExpr_bitblast_blastAdd_go(
    mut v_00_u03b1_660_: *mut LeanObject,
    mut v_inst_661_: *mut LeanObject,
    mut v_inst_662_: *mut LeanObject,
    mut v_w_663_: *mut LeanObject,
    mut v_aig_664_: *mut LeanObject,
    mut v_lhs_665_: *mut LeanObject,
    mut v_rhs_666_: *mut LeanObject,
    mut v_curr_667_: *mut LeanObject,
    mut v_hcurr_668_: *mut LeanObject,
    mut v_cin_669_: *mut LeanObject,
    mut v_s_670_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_671_: *mut LeanObject = core::ptr::null_mut();
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
    mut v_00_u03b1_672_: *mut LeanObject,
    mut v_inst_673_: *mut LeanObject,
    mut v_inst_674_: *mut LeanObject,
    mut v_w_675_: *mut LeanObject,
    mut v_aig_676_: *mut LeanObject,
    mut v_lhs_677_: *mut LeanObject,
    mut v_rhs_678_: *mut LeanObject,
    mut v_curr_679_: *mut LeanObject,
    mut v_hcurr_680_: *mut LeanObject,
    mut v_cin_681_: *mut LeanObject,
    mut v_s_682_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_683_: *mut LeanObject = core::ptr::null_mut();
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
    lean_dec_ref(v_rhs_678_);
    lean_dec_ref(v_lhs_677_);
    lean_dec(v_w_675_);
    return v_res_683_;
}
pub unsafe fn l_Std_Tactic_BVDecide_BVExpr_bitblast_blastAdd_blast___redArg(
    mut v_inst_687_: *mut LeanObject,
    mut v_inst_688_: *mut LeanObject,
    mut v_w_689_: *mut LeanObject,
    mut v_aig_690_: *mut LeanObject,
    mut v_input_691_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_lhs_692_: *mut LeanObject = core::ptr::null_mut();
    let mut v_rhs_693_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_694_: *mut LeanObject = core::ptr::null_mut();
    let mut v_cin_695_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_696_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_697_: *mut LeanObject = core::ptr::null_mut();
    v_lhs_692_ = lean_ctor_get(v_input_691_, 0);
    v_rhs_693_ = lean_ctor_get(v_input_691_, 1);
    v___x_694_ = lean_unsigned_to_nat(0);
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
    mut v_inst_698_: *mut LeanObject,
    mut v_inst_699_: *mut LeanObject,
    mut v_w_700_: *mut LeanObject,
    mut v_aig_701_: *mut LeanObject,
    mut v_input_702_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_703_: *mut LeanObject = core::ptr::null_mut();
    v_res_703_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastAdd_blast___redArg(
        v_inst_698_,
        v_inst_699_,
        v_w_700_,
        v_aig_701_,
        v_input_702_,
    );
    lean_dec_ref(v_input_702_);
    lean_dec(v_w_700_);
    return v_res_703_;
}
pub unsafe fn l_Std_Tactic_BVDecide_BVExpr_bitblast_blastAdd_blast(
    mut v_00_u03b1_704_: *mut LeanObject,
    mut v_inst_705_: *mut LeanObject,
    mut v_inst_706_: *mut LeanObject,
    mut v_w_707_: *mut LeanObject,
    mut v_aig_708_: *mut LeanObject,
    mut v_input_709_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_710_: *mut LeanObject = core::ptr::null_mut();
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
    mut v_00_u03b1_711_: *mut LeanObject,
    mut v_inst_712_: *mut LeanObject,
    mut v_inst_713_: *mut LeanObject,
    mut v_w_714_: *mut LeanObject,
    mut v_aig_715_: *mut LeanObject,
    mut v_input_716_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_717_: *mut LeanObject = core::ptr::null_mut();
    v_res_717_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastAdd_blast(
        v_00_u03b1_711_,
        v_inst_712_,
        v_inst_713_,
        v_w_714_,
        v_aig_715_,
        v_input_716_,
    );
    lean_dec_ref(v_input_716_);
    lean_dec(v_w_714_);
    return v_res_717_;
}
pub unsafe fn l_Std_Tactic_BVDecide_BVExpr_bitblast_blastAdd___redArg(
    mut v_inst_718_: *mut LeanObject,
    mut v_inst_719_: *mut LeanObject,
    mut v_w_720_: *mut LeanObject,
    mut v_aig_721_: *mut LeanObject,
    mut v_input_722_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_lhs_723_: *mut LeanObject = core::ptr::null_mut();
    let mut v_rhs_724_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_725_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_726_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_727_: u8 = 0;
    let mut v___x_729_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_730_: u8 = 0;
    let mut v___x_732_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_733_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_734_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_735_: u8 = 0;
    let mut v_unused_736_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_737_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_738_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_lhs_723_ = lean_ctor_get(v_input_722_, 0);
                v_rhs_724_ = lean_ctor_get(v_input_722_, 1);
                v___x_725_ =
                    l_Std_Sat_AIG_RefVec_countKnown___redArg(v_w_720_, v_aig_721_, v_lhs_723_);
                v___x_726_ =
                    l_Std_Sat_AIG_RefVec_countKnown___redArg(v_w_720_, v_aig_721_, v_rhs_724_);
                v___x_727_ = lean_nat_dec_lt(v___x_725_, v___x_726_);
                lean_dec(v___x_726_);
                lean_dec(v___x_725_);
                if v___x_727_ == 0 {
                    lean_inc_ref(v_rhs_724_);
                    lean_inc_ref(v_lhs_723_);
                    v_isSharedCheck_735_ = (!lean_is_exclusive(v_input_722_)) as u8;
                    if v_isSharedCheck_735_ == 0 {
                        v_unused_736_ = lean_ctor_get(v_input_722_, 1);
                        lean_dec(v_unused_736_);
                        v_unused_737_ = lean_ctor_get(v_input_722_, 0);
                        lean_dec(v_unused_737_);
                        v___x_729_ = v_input_722_;
                        v_isShared_730_ = v_isSharedCheck_735_;
                        state = 1;
                        continue;
                    } else {
                        lean_dec(v_input_722_);
                        v___x_729_ = lean_box(0);
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
                    lean_dec_ref(v_input_722_);
                    return v___x_738_;
                }
            }
            1 => {
                if v_isShared_730_ == 0 {
                    lean_ctor_set(v___x_729_, 1, v_lhs_723_);
                    lean_ctor_set(v___x_729_, 0, v_rhs_724_);
                    v___x_732_ = v___x_729_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_734_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_734_, 0, v_rhs_724_);
                    lean_ctor_set(v_reuseFailAlloc_734_, 1, v_lhs_723_);
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
                lean_dec_ref(v___x_732_);
                return v___x_733_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Tactic_BVDecide_BVExpr_bitblast_blastAdd___redArg___boxed(
    mut v_inst_739_: *mut LeanObject,
    mut v_inst_740_: *mut LeanObject,
    mut v_w_741_: *mut LeanObject,
    mut v_aig_742_: *mut LeanObject,
    mut v_input_743_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_744_: *mut LeanObject = core::ptr::null_mut();
    v_res_744_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastAdd___redArg(
        v_inst_739_,
        v_inst_740_,
        v_w_741_,
        v_aig_742_,
        v_input_743_,
    );
    lean_dec(v_w_741_);
    return v_res_744_;
}
pub unsafe fn l_Std_Tactic_BVDecide_BVExpr_bitblast_blastAdd(
    mut v_00_u03b1_745_: *mut LeanObject,
    mut v_inst_746_: *mut LeanObject,
    mut v_inst_747_: *mut LeanObject,
    mut v_w_748_: *mut LeanObject,
    mut v_aig_749_: *mut LeanObject,
    mut v_input_750_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_751_: *mut LeanObject = core::ptr::null_mut();
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
    mut v_00_u03b1_752_: *mut LeanObject,
    mut v_inst_753_: *mut LeanObject,
    mut v_inst_754_: *mut LeanObject,
    mut v_w_755_: *mut LeanObject,
    mut v_aig_756_: *mut LeanObject,
    mut v_input_757_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_758_: *mut LeanObject = core::ptr::null_mut();
    v_res_758_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastAdd(
        v_00_u03b1_752_,
        v_inst_753_,
        v_inst_754_,
        v_w_755_,
        v_aig_756_,
        v_input_757_,
    );
    lean_dec(v_w_755_);
    return v_res_758_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Operations_Add(
    builtin: u8,
) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Basic(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Std_Sat_AIG_LawfulVecOperator(builtin);
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
pub unsafe fn meta_initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Operations_Add(
    builtin: u8,
) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_meta_initialized = true;
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Operations_Add(
    builtin: u8,
) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Basic(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Std_Sat_AIG_LawfulVecOperator(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Omega(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res =
        runtime_initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Operations_Add(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Operations_Add(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Operations_Add(builtin);
}
