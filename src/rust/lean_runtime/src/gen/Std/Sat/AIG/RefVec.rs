// Lean compiler output
// Module: Std.Sat.AIG.RefVec
// Imports: Std.Sat.AIG.CachedGatesLemmas Init.Data.Vector.Lemmas Init.ByCases Init.Omega
use crate::r#gen::Init::ByCases::{initialize_Init_ByCases, runtime_initialize_Init_ByCases};
use crate::r#gen::Init::Data::Array::Basic::l_Array_append___redArg;
use crate::r#gen::Init::Data::Bool::l_Bool_toNat;
use crate::r#gen::Init::Data::Vector::Lemmas::{
    initialize_Init_Data_Vector_Lemmas, runtime_initialize_Init_Data_Vector_Lemmas,
};
use crate::r#gen::Init::Omega::{initialize_Init_Omega, runtime_initialize_Init_Omega};
use crate::r#gen::Std::Sat::AIG::CachedGatesLemmas::{
    initialize_Std_Sat_AIG_CachedGatesLemmas, runtime_initialize_Std_Sat_AIG_CachedGatesLemmas,
};
use crate::lean_imports_rs::Init::Data::Nat::Bitwise::Basic::{
    lean_nat_land, lean_nat_lor, lean_nat_shiftr,
};
use crate::lean_imports_rs::Init::Prelude::{
    lean_array_fget_borrowed, lean_array_push, lean_mk_empty_array_with_capacity, lean_nat_add,
    lean_nat_dec_eq, lean_nat_dec_lt, lean_nat_mul,
};
pub static l_Std_Sat_AIG_RefVec_empty___closed__0_value: crate::leanh::LeanArrayObject<0> =
    crate::leanh::LeanArrayObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<usize>() * 2
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0)
                as u16,
            other: 0,
            tag: 246,
        },
        m_size: 0,
        m_capacity: 0,
        m_data: [],
    };
static mut l_Std_Sat_AIG_RefVec_empty___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Sat_AIG_RefVec_empty___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub unsafe fn l_Std_Sat_AIG_RefVec_empty(
    mut v_00_u03b1_376_: *mut crate::leanh::LeanObject,
    mut v_inst_377_: *mut crate::leanh::LeanObject,
    mut v_inst_378_: *mut crate::leanh::LeanObject,
    mut v_aig_379_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_380_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_380_ = l_Std_Sat_AIG_RefVec_empty___closed__0;
    return v___x_380_;
}
pub unsafe fn l_Std_Sat_AIG_RefVec_empty___boxed(
    mut v_00_u03b1_381_: *mut crate::leanh::LeanObject,
    mut v_inst_382_: *mut crate::leanh::LeanObject,
    mut v_inst_383_: *mut crate::leanh::LeanObject,
    mut v_aig_384_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_385_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_385_ = l_Std_Sat_AIG_RefVec_empty(v_00_u03b1_381_, v_inst_382_, v_inst_383_, v_aig_384_);
    crate::leanh::lean_dec_ref(v_aig_384_);
    crate::leanh::lean_dec_ref(v_inst_383_);
    crate::leanh::lean_dec_ref(v_inst_382_);
    return v_res_385_;
}
pub unsafe fn l_Std_Sat_AIG_RefVec_emptyWithCapacity___redArg(
    mut v_c_386_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_387_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_387_ = lean_mk_empty_array_with_capacity(v_c_386_);
    return v___x_387_;
}
pub unsafe fn l_Std_Sat_AIG_RefVec_emptyWithCapacity___redArg___boxed(
    mut v_c_388_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_389_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_389_ = l_Std_Sat_AIG_RefVec_emptyWithCapacity___redArg(v_c_388_);
    crate::leanh::lean_dec(v_c_388_);
    return v_res_389_;
}
pub unsafe fn l_Std_Sat_AIG_RefVec_emptyWithCapacity(
    mut v_00_u03b1_390_: *mut crate::leanh::LeanObject,
    mut v_inst_391_: *mut crate::leanh::LeanObject,
    mut v_inst_392_: *mut crate::leanh::LeanObject,
    mut v_aig_393_: *mut crate::leanh::LeanObject,
    mut v_c_394_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_395_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_395_ = lean_mk_empty_array_with_capacity(v_c_394_);
    return v___x_395_;
}
pub unsafe fn l_Std_Sat_AIG_RefVec_emptyWithCapacity___boxed(
    mut v_00_u03b1_396_: *mut crate::leanh::LeanObject,
    mut v_inst_397_: *mut crate::leanh::LeanObject,
    mut v_inst_398_: *mut crate::leanh::LeanObject,
    mut v_aig_399_: *mut crate::leanh::LeanObject,
    mut v_c_400_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_401_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_401_ = l_Std_Sat_AIG_RefVec_emptyWithCapacity(
        v_00_u03b1_396_,
        v_inst_397_,
        v_inst_398_,
        v_aig_399_,
        v_c_400_,
    );
    crate::leanh::lean_dec(v_c_400_);
    crate::leanh::lean_dec_ref(v_aig_399_);
    crate::leanh::lean_dec_ref(v_inst_398_);
    crate::leanh::lean_dec_ref(v_inst_397_);
    return v_res_401_;
}
pub unsafe fn l_Std_Sat_AIG_RefVec_cast_x27___redArg(
    mut v_s_402_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc_ref(v_s_402_);
    return v_s_402_;
}
pub unsafe fn l_Std_Sat_AIG_RefVec_cast_x27___redArg___boxed(
    mut v_s_403_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_404_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_404_ = l_Std_Sat_AIG_RefVec_cast_x27___redArg(v_s_403_);
    crate::leanh::lean_dec_ref(v_s_403_);
    return v_res_404_;
}
pub unsafe fn l_Std_Sat_AIG_RefVec_cast_x27(
    mut v_00_u03b1_405_: *mut crate::leanh::LeanObject,
    mut v_inst_406_: *mut crate::leanh::LeanObject,
    mut v_inst_407_: *mut crate::leanh::LeanObject,
    mut v_len_408_: *mut crate::leanh::LeanObject,
    mut v_aig1_409_: *mut crate::leanh::LeanObject,
    mut v_aig2_410_: *mut crate::leanh::LeanObject,
    mut v_s_411_: *mut crate::leanh::LeanObject,
    mut v_h_412_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc_ref(v_s_411_);
    return v_s_411_;
}
pub unsafe fn l_Std_Sat_AIG_RefVec_cast_x27___boxed(
    mut v_00_u03b1_413_: *mut crate::leanh::LeanObject,
    mut v_inst_414_: *mut crate::leanh::LeanObject,
    mut v_inst_415_: *mut crate::leanh::LeanObject,
    mut v_len_416_: *mut crate::leanh::LeanObject,
    mut v_aig1_417_: *mut crate::leanh::LeanObject,
    mut v_aig2_418_: *mut crate::leanh::LeanObject,
    mut v_s_419_: *mut crate::leanh::LeanObject,
    mut v_h_420_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_421_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_421_ = l_Std_Sat_AIG_RefVec_cast_x27(
        v_00_u03b1_413_,
        v_inst_414_,
        v_inst_415_,
        v_len_416_,
        v_aig1_417_,
        v_aig2_418_,
        v_s_419_,
        v_h_420_,
    );
    crate::leanh::lean_dec_ref(v_s_419_);
    crate::leanh::lean_dec_ref(v_aig2_418_);
    crate::leanh::lean_dec_ref(v_aig1_417_);
    crate::leanh::lean_dec(v_len_416_);
    crate::leanh::lean_dec_ref(v_inst_415_);
    crate::leanh::lean_dec_ref(v_inst_414_);
    return v_res_421_;
}
pub unsafe fn l_Std_Sat_AIG_RefVec_cast___redArg(
    mut v_s_422_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc_ref(v_s_422_);
    return v_s_422_;
}
pub unsafe fn l_Std_Sat_AIG_RefVec_cast___redArg___boxed(
    mut v_s_423_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_424_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_424_ = l_Std_Sat_AIG_RefVec_cast___redArg(v_s_423_);
    crate::leanh::lean_dec_ref(v_s_423_);
    return v_res_424_;
}
pub unsafe fn l_Std_Sat_AIG_RefVec_cast(
    mut v_00_u03b1_425_: *mut crate::leanh::LeanObject,
    mut v_inst_426_: *mut crate::leanh::LeanObject,
    mut v_inst_427_: *mut crate::leanh::LeanObject,
    mut v_len_428_: *mut crate::leanh::LeanObject,
    mut v_aig1_429_: *mut crate::leanh::LeanObject,
    mut v_aig2_430_: *mut crate::leanh::LeanObject,
    mut v_s_431_: *mut crate::leanh::LeanObject,
    mut v_h_432_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc_ref(v_s_431_);
    return v_s_431_;
}
pub unsafe fn l_Std_Sat_AIG_RefVec_cast___boxed(
    mut v_00_u03b1_433_: *mut crate::leanh::LeanObject,
    mut v_inst_434_: *mut crate::leanh::LeanObject,
    mut v_inst_435_: *mut crate::leanh::LeanObject,
    mut v_len_436_: *mut crate::leanh::LeanObject,
    mut v_aig1_437_: *mut crate::leanh::LeanObject,
    mut v_aig2_438_: *mut crate::leanh::LeanObject,
    mut v_s_439_: *mut crate::leanh::LeanObject,
    mut v_h_440_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_441_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_441_ = l_Std_Sat_AIG_RefVec_cast(
        v_00_u03b1_433_,
        v_inst_434_,
        v_inst_435_,
        v_len_436_,
        v_aig1_437_,
        v_aig2_438_,
        v_s_439_,
        v_h_440_,
    );
    crate::leanh::lean_dec_ref(v_s_439_);
    crate::leanh::lean_dec_ref(v_aig2_438_);
    crate::leanh::lean_dec_ref(v_aig1_437_);
    crate::leanh::lean_dec(v_len_436_);
    crate::leanh::lean_dec_ref(v_inst_435_);
    crate::leanh::lean_dec_ref(v_inst_434_);
    return v_res_441_;
}
pub unsafe fn l_Std_Sat_AIG_RefVec_get___redArg(
    mut v_s_442_: *mut crate::leanh::LeanObject,
    mut v_idx_443_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_ref_444_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_445_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_446_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_447_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_448_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_449_: u8 = 0;
    v_ref_444_ = lean_array_fget_borrowed(v_s_442_, v_idx_443_);
    v___x_445_ = crate::leanh::lean_unsigned_to_nat(1);
    v___x_446_ = lean_nat_shiftr(v_ref_444_, v___x_445_);
    v___x_447_ = lean_nat_land(v___x_445_, v_ref_444_);
    v___x_448_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_449_ = lean_nat_dec_eq(v___x_447_, v___x_448_);
    crate::leanh::lean_dec(v___x_447_);
    if v___x_449_ == 0 {
        let mut v___x_450_: u8 = 0;
        let mut v___x_451_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_450_ = 1;
        v___x_451_ = crate::leanh::lean_alloc_ctor(0, 1, (1) as u32);
        crate::leanh::lean_ctor_set(v___x_451_, 0, v___x_446_);
        crate::leanh::lean_ctor_set_uint8(
            v___x_451_,
            (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
            v___x_450_,
        );
        return v___x_451_;
    } else {
        let mut v___x_452_: u8 = 0;
        let mut v___x_453_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_452_ = 0;
        v___x_453_ = crate::leanh::lean_alloc_ctor(0, 1, (1) as u32);
        crate::leanh::lean_ctor_set(v___x_453_, 0, v___x_446_);
        crate::leanh::lean_ctor_set_uint8(
            v___x_453_,
            (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
            v___x_452_,
        );
        return v___x_453_;
    }
}
pub unsafe fn l_Std_Sat_AIG_RefVec_get___redArg___boxed(
    mut v_s_454_: *mut crate::leanh::LeanObject,
    mut v_idx_455_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_456_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_456_ = l_Std_Sat_AIG_RefVec_get___redArg(v_s_454_, v_idx_455_);
    crate::leanh::lean_dec(v_idx_455_);
    crate::leanh::lean_dec_ref(v_s_454_);
    return v_res_456_;
}
pub unsafe fn l_Std_Sat_AIG_RefVec_get(
    mut v_00_u03b1_457_: *mut crate::leanh::LeanObject,
    mut v_inst_458_: *mut crate::leanh::LeanObject,
    mut v_inst_459_: *mut crate::leanh::LeanObject,
    mut v_aig_460_: *mut crate::leanh::LeanObject,
    mut v_len_461_: *mut crate::leanh::LeanObject,
    mut v_s_462_: *mut crate::leanh::LeanObject,
    mut v_idx_463_: *mut crate::leanh::LeanObject,
    mut v_hidx_464_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_ref_465_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_466_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_467_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_468_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_469_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_470_: u8 = 0;
    v_ref_465_ = lean_array_fget_borrowed(v_s_462_, v_idx_463_);
    v___x_466_ = crate::leanh::lean_unsigned_to_nat(1);
    v___x_467_ = lean_nat_shiftr(v_ref_465_, v___x_466_);
    v___x_468_ = lean_nat_land(v___x_466_, v_ref_465_);
    v___x_469_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_470_ = lean_nat_dec_eq(v___x_468_, v___x_469_);
    crate::leanh::lean_dec(v___x_468_);
    if v___x_470_ == 0 {
        let mut v___x_471_: u8 = 0;
        let mut v___x_472_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_471_ = 1;
        v___x_472_ = crate::leanh::lean_alloc_ctor(0, 1, (1) as u32);
        crate::leanh::lean_ctor_set(v___x_472_, 0, v___x_467_);
        crate::leanh::lean_ctor_set_uint8(
            v___x_472_,
            (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
            v___x_471_,
        );
        return v___x_472_;
    } else {
        let mut v___x_473_: u8 = 0;
        let mut v___x_474_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_473_ = 0;
        v___x_474_ = crate::leanh::lean_alloc_ctor(0, 1, (1) as u32);
        crate::leanh::lean_ctor_set(v___x_474_, 0, v___x_467_);
        crate::leanh::lean_ctor_set_uint8(
            v___x_474_,
            (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
            v___x_473_,
        );
        return v___x_474_;
    }
}
pub unsafe fn l_Std_Sat_AIG_RefVec_get___boxed(
    mut v_00_u03b1_475_: *mut crate::leanh::LeanObject,
    mut v_inst_476_: *mut crate::leanh::LeanObject,
    mut v_inst_477_: *mut crate::leanh::LeanObject,
    mut v_aig_478_: *mut crate::leanh::LeanObject,
    mut v_len_479_: *mut crate::leanh::LeanObject,
    mut v_s_480_: *mut crate::leanh::LeanObject,
    mut v_idx_481_: *mut crate::leanh::LeanObject,
    mut v_hidx_482_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_483_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_483_ = l_Std_Sat_AIG_RefVec_get(
        v_00_u03b1_475_,
        v_inst_476_,
        v_inst_477_,
        v_aig_478_,
        v_len_479_,
        v_s_480_,
        v_idx_481_,
        v_hidx_482_,
    );
    crate::leanh::lean_dec(v_idx_481_);
    crate::leanh::lean_dec_ref(v_s_480_);
    crate::leanh::lean_dec(v_len_479_);
    crate::leanh::lean_dec_ref(v_aig_478_);
    crate::leanh::lean_dec_ref(v_inst_477_);
    crate::leanh::lean_dec_ref(v_inst_476_);
    return v_res_483_;
}
pub unsafe fn l_Std_Sat_AIG_RefVec_push___redArg(
    mut v_s_484_: *mut crate::leanh::LeanObject,
    mut v_ref_485_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_gate_486_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_invert_487_: u8 = 0;
    let mut v___x_488_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_489_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_490_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_491_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_492_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_gate_486_ = crate::leanh::lean_ctor_get(v_ref_485_, 0);
    v_invert_487_ = crate::leanh::lean_ctor_get_uint8(
        v_ref_485_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
    );
    v___x_488_ = crate::leanh::lean_unsigned_to_nat(2);
    v___x_489_ = lean_nat_mul(v_gate_486_, v___x_488_);
    v___x_490_ = l_Bool_toNat(v_invert_487_);
    v___x_491_ = lean_nat_lor(v___x_489_, v___x_490_);
    crate::leanh::lean_dec(v___x_490_);
    crate::leanh::lean_dec(v___x_489_);
    v___x_492_ = lean_array_push(v_s_484_, v___x_491_);
    return v___x_492_;
}
pub unsafe fn l_Std_Sat_AIG_RefVec_push___redArg___boxed(
    mut v_s_493_: *mut crate::leanh::LeanObject,
    mut v_ref_494_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_495_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_495_ = l_Std_Sat_AIG_RefVec_push___redArg(v_s_493_, v_ref_494_);
    crate::leanh::lean_dec_ref(v_ref_494_);
    return v_res_495_;
}
pub unsafe fn l_Std_Sat_AIG_RefVec_push(
    mut v_00_u03b1_496_: *mut crate::leanh::LeanObject,
    mut v_inst_497_: *mut crate::leanh::LeanObject,
    mut v_inst_498_: *mut crate::leanh::LeanObject,
    mut v_aig_499_: *mut crate::leanh::LeanObject,
    mut v_len_500_: *mut crate::leanh::LeanObject,
    mut v_s_501_: *mut crate::leanh::LeanObject,
    mut v_ref_502_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_gate_503_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_invert_504_: u8 = 0;
    let mut v___x_505_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_506_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_507_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_508_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_509_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_gate_503_ = crate::leanh::lean_ctor_get(v_ref_502_, 0);
    v_invert_504_ = crate::leanh::lean_ctor_get_uint8(
        v_ref_502_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
    );
    v___x_505_ = crate::leanh::lean_unsigned_to_nat(2);
    v___x_506_ = lean_nat_mul(v_gate_503_, v___x_505_);
    v___x_507_ = l_Bool_toNat(v_invert_504_);
    v___x_508_ = lean_nat_lor(v___x_506_, v___x_507_);
    crate::leanh::lean_dec(v___x_507_);
    crate::leanh::lean_dec(v___x_506_);
    v___x_509_ = lean_array_push(v_s_501_, v___x_508_);
    return v___x_509_;
}
pub unsafe fn l_Std_Sat_AIG_RefVec_push___boxed(
    mut v_00_u03b1_510_: *mut crate::leanh::LeanObject,
    mut v_inst_511_: *mut crate::leanh::LeanObject,
    mut v_inst_512_: *mut crate::leanh::LeanObject,
    mut v_aig_513_: *mut crate::leanh::LeanObject,
    mut v_len_514_: *mut crate::leanh::LeanObject,
    mut v_s_515_: *mut crate::leanh::LeanObject,
    mut v_ref_516_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_517_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_517_ = l_Std_Sat_AIG_RefVec_push(
        v_00_u03b1_510_,
        v_inst_511_,
        v_inst_512_,
        v_aig_513_,
        v_len_514_,
        v_s_515_,
        v_ref_516_,
    );
    crate::leanh::lean_dec_ref(v_ref_516_);
    crate::leanh::lean_dec(v_len_514_);
    crate::leanh::lean_dec_ref(v_aig_513_);
    crate::leanh::lean_dec_ref(v_inst_512_);
    crate::leanh::lean_dec_ref(v_inst_511_);
    return v_res_517_;
}
pub unsafe fn l___private_Std_Sat_AIG_RefVec_0__Std_Sat_AIG_RefVec_get_match__1_splitter___redArg(
    mut v_s_518_: *mut crate::leanh::LeanObject,
    mut v_h__1_519_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_520_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_520_ = crate::leanh::lean_apply_2(v_h__1_519_, v_s_518_, crate::leanh::lean_box(0));
    return v___x_520_;
}
pub unsafe fn l___private_Std_Sat_AIG_RefVec_0__Std_Sat_AIG_RefVec_get_match__1_splitter(
    mut v_00_u03b1_521_: *mut crate::leanh::LeanObject,
    mut v_inst_522_: *mut crate::leanh::LeanObject,
    mut v_inst_523_: *mut crate::leanh::LeanObject,
    mut v_aig_524_: *mut crate::leanh::LeanObject,
    mut v_len_525_: *mut crate::leanh::LeanObject,
    mut v_motive_526_: *mut crate::leanh::LeanObject,
    mut v_s_527_: *mut crate::leanh::LeanObject,
    mut v_h__1_528_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_529_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_529_ = crate::leanh::lean_apply_2(v_h__1_528_, v_s_527_, crate::leanh::lean_box(0));
    return v___x_529_;
}
pub unsafe fn l___private_Std_Sat_AIG_RefVec_0__Std_Sat_AIG_RefVec_get_match__1_splitter___boxed(
    mut v_00_u03b1_530_: *mut crate::leanh::LeanObject,
    mut v_inst_531_: *mut crate::leanh::LeanObject,
    mut v_inst_532_: *mut crate::leanh::LeanObject,
    mut v_aig_533_: *mut crate::leanh::LeanObject,
    mut v_len_534_: *mut crate::leanh::LeanObject,
    mut v_motive_535_: *mut crate::leanh::LeanObject,
    mut v_s_536_: *mut crate::leanh::LeanObject,
    mut v_h__1_537_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_538_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_538_ = l___private_Std_Sat_AIG_RefVec_0__Std_Sat_AIG_RefVec_get_match__1_splitter(
        v_00_u03b1_530_,
        v_inst_531_,
        v_inst_532_,
        v_aig_533_,
        v_len_534_,
        v_motive_535_,
        v_s_536_,
        v_h__1_537_,
    );
    crate::leanh::lean_dec(v_len_534_);
    crate::leanh::lean_dec_ref(v_aig_533_);
    crate::leanh::lean_dec_ref(v_inst_532_);
    crate::leanh::lean_dec_ref(v_inst_531_);
    return v_res_538_;
}
pub unsafe fn l_Std_Sat_AIG_RefVec_append___redArg(
    mut v_lhs_539_: *mut crate::leanh::LeanObject,
    mut v_rhs_540_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_541_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_541_ = l_Array_append___redArg(v_lhs_539_, v_rhs_540_);
    return v___x_541_;
}
pub unsafe fn l_Std_Sat_AIG_RefVec_append___redArg___boxed(
    mut v_lhs_542_: *mut crate::leanh::LeanObject,
    mut v_rhs_543_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_544_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_544_ = l_Std_Sat_AIG_RefVec_append___redArg(v_lhs_542_, v_rhs_543_);
    crate::leanh::lean_dec_ref(v_rhs_543_);
    return v_res_544_;
}
pub unsafe fn l_Std_Sat_AIG_RefVec_append(
    mut v_00_u03b1_545_: *mut crate::leanh::LeanObject,
    mut v_inst_546_: *mut crate::leanh::LeanObject,
    mut v_inst_547_: *mut crate::leanh::LeanObject,
    mut v_aig_548_: *mut crate::leanh::LeanObject,
    mut v_lw_549_: *mut crate::leanh::LeanObject,
    mut v_rw_550_: *mut crate::leanh::LeanObject,
    mut v_lhs_551_: *mut crate::leanh::LeanObject,
    mut v_rhs_552_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_553_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_553_ = l_Array_append___redArg(v_lhs_551_, v_rhs_552_);
    return v___x_553_;
}
pub unsafe fn l_Std_Sat_AIG_RefVec_append___boxed(
    mut v_00_u03b1_554_: *mut crate::leanh::LeanObject,
    mut v_inst_555_: *mut crate::leanh::LeanObject,
    mut v_inst_556_: *mut crate::leanh::LeanObject,
    mut v_aig_557_: *mut crate::leanh::LeanObject,
    mut v_lw_558_: *mut crate::leanh::LeanObject,
    mut v_rw_559_: *mut crate::leanh::LeanObject,
    mut v_lhs_560_: *mut crate::leanh::LeanObject,
    mut v_rhs_561_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_562_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_562_ = l_Std_Sat_AIG_RefVec_append(
        v_00_u03b1_554_,
        v_inst_555_,
        v_inst_556_,
        v_aig_557_,
        v_lw_558_,
        v_rw_559_,
        v_lhs_560_,
        v_rhs_561_,
    );
    crate::leanh::lean_dec_ref(v_rhs_561_);
    crate::leanh::lean_dec(v_rw_559_);
    crate::leanh::lean_dec(v_lw_558_);
    crate::leanh::lean_dec_ref(v_aig_557_);
    crate::leanh::lean_dec_ref(v_inst_556_);
    crate::leanh::lean_dec_ref(v_inst_555_);
    return v_res_562_;
}
pub unsafe fn l_Std_Sat_AIG_RefVec_getD___redArg(
    mut v_len_563_: *mut crate::leanh::LeanObject,
    mut v_s_564_: *mut crate::leanh::LeanObject,
    mut v_idx_565_: *mut crate::leanh::LeanObject,
    mut v_alt_566_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_567_: u8 = 0;
    v___x_567_ = lean_nat_dec_lt(v_idx_565_, v_len_563_);
    if v___x_567_ == 0 {
        crate::leanh::lean_inc_ref(v_alt_566_);
        return v_alt_566_;
    } else {
        let mut v_ref_568_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_569_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_570_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_571_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_572_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_573_: u8 = 0;
        v_ref_568_ = lean_array_fget_borrowed(v_s_564_, v_idx_565_);
        v___x_569_ = crate::leanh::lean_unsigned_to_nat(1);
        v___x_570_ = lean_nat_shiftr(v_ref_568_, v___x_569_);
        v___x_571_ = lean_nat_land(v___x_569_, v_ref_568_);
        v___x_572_ = crate::leanh::lean_unsigned_to_nat(0);
        v___x_573_ = lean_nat_dec_eq(v___x_571_, v___x_572_);
        crate::leanh::lean_dec(v___x_571_);
        if v___x_573_ == 0 {
            let mut v___x_574_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_574_ = crate::leanh::lean_alloc_ctor(0, 1, (1) as u32);
            crate::leanh::lean_ctor_set(v___x_574_, 0, v___x_570_);
            crate::leanh::lean_ctor_set_uint8(
                v___x_574_,
                (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                v___x_567_,
            );
            return v___x_574_;
        } else {
            let mut v___x_575_: u8 = 0;
            let mut v___x_576_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_575_ = 0;
            v___x_576_ = crate::leanh::lean_alloc_ctor(0, 1, (1) as u32);
            crate::leanh::lean_ctor_set(v___x_576_, 0, v___x_570_);
            crate::leanh::lean_ctor_set_uint8(
                v___x_576_,
                (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                v___x_575_,
            );
            return v___x_576_;
        }
    }
}
pub unsafe fn l_Std_Sat_AIG_RefVec_getD___redArg___boxed(
    mut v_len_577_: *mut crate::leanh::LeanObject,
    mut v_s_578_: *mut crate::leanh::LeanObject,
    mut v_idx_579_: *mut crate::leanh::LeanObject,
    mut v_alt_580_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_581_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_581_ = l_Std_Sat_AIG_RefVec_getD___redArg(v_len_577_, v_s_578_, v_idx_579_, v_alt_580_);
    crate::leanh::lean_dec_ref(v_alt_580_);
    crate::leanh::lean_dec(v_idx_579_);
    crate::leanh::lean_dec_ref(v_s_578_);
    crate::leanh::lean_dec(v_len_577_);
    return v_res_581_;
}
pub unsafe fn l_Std_Sat_AIG_RefVec_getD(
    mut v_00_u03b1_582_: *mut crate::leanh::LeanObject,
    mut v_inst_583_: *mut crate::leanh::LeanObject,
    mut v_inst_584_: *mut crate::leanh::LeanObject,
    mut v_aig_585_: *mut crate::leanh::LeanObject,
    mut v_len_586_: *mut crate::leanh::LeanObject,
    mut v_s_587_: *mut crate::leanh::LeanObject,
    mut v_idx_588_: *mut crate::leanh::LeanObject,
    mut v_alt_589_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_590_: u8 = 0;
    v___x_590_ = lean_nat_dec_lt(v_idx_588_, v_len_586_);
    if v___x_590_ == 0 {
        crate::leanh::lean_inc_ref(v_alt_589_);
        return v_alt_589_;
    } else {
        let mut v_ref_591_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_592_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_593_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_594_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_595_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_596_: u8 = 0;
        v_ref_591_ = lean_array_fget_borrowed(v_s_587_, v_idx_588_);
        v___x_592_ = crate::leanh::lean_unsigned_to_nat(1);
        v___x_593_ = lean_nat_shiftr(v_ref_591_, v___x_592_);
        v___x_594_ = lean_nat_land(v___x_592_, v_ref_591_);
        v___x_595_ = crate::leanh::lean_unsigned_to_nat(0);
        v___x_596_ = lean_nat_dec_eq(v___x_594_, v___x_595_);
        crate::leanh::lean_dec(v___x_594_);
        if v___x_596_ == 0 {
            let mut v___x_597_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_597_ = crate::leanh::lean_alloc_ctor(0, 1, (1) as u32);
            crate::leanh::lean_ctor_set(v___x_597_, 0, v___x_593_);
            crate::leanh::lean_ctor_set_uint8(
                v___x_597_,
                (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                v___x_590_,
            );
            return v___x_597_;
        } else {
            let mut v___x_598_: u8 = 0;
            let mut v___x_599_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_598_ = 0;
            v___x_599_ = crate::leanh::lean_alloc_ctor(0, 1, (1) as u32);
            crate::leanh::lean_ctor_set(v___x_599_, 0, v___x_593_);
            crate::leanh::lean_ctor_set_uint8(
                v___x_599_,
                (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                v___x_598_,
            );
            return v___x_599_;
        }
    }
}
pub unsafe fn l_Std_Sat_AIG_RefVec_getD___boxed(
    mut v_00_u03b1_600_: *mut crate::leanh::LeanObject,
    mut v_inst_601_: *mut crate::leanh::LeanObject,
    mut v_inst_602_: *mut crate::leanh::LeanObject,
    mut v_aig_603_: *mut crate::leanh::LeanObject,
    mut v_len_604_: *mut crate::leanh::LeanObject,
    mut v_s_605_: *mut crate::leanh::LeanObject,
    mut v_idx_606_: *mut crate::leanh::LeanObject,
    mut v_alt_607_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_608_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_608_ = l_Std_Sat_AIG_RefVec_getD(
        v_00_u03b1_600_,
        v_inst_601_,
        v_inst_602_,
        v_aig_603_,
        v_len_604_,
        v_s_605_,
        v_idx_606_,
        v_alt_607_,
    );
    crate::leanh::lean_dec_ref(v_alt_607_);
    crate::leanh::lean_dec(v_idx_606_);
    crate::leanh::lean_dec_ref(v_s_605_);
    crate::leanh::lean_dec(v_len_604_);
    crate::leanh::lean_dec_ref(v_aig_603_);
    crate::leanh::lean_dec_ref(v_inst_602_);
    crate::leanh::lean_dec_ref(v_inst_601_);
    return v_res_608_;
}
pub unsafe fn l_Std_Sat_AIG_RefVec_countKnown_go___redArg(
    mut v_len_609_: *mut crate::leanh::LeanObject,
    mut v_aig_610_: *mut crate::leanh::LeanObject,
    mut v_s_611_: *mut crate::leanh::LeanObject,
    mut v_idx_612_: *mut crate::leanh::LeanObject,
    mut v_acc_613_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_614_: u8 = 0;
    let mut v_decls_615_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_616_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_617_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_618_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_decl_619_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_620_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_621_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_623_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_614_ = lean_nat_dec_lt(v_idx_612_, v_len_609_);
                if v___x_614_ == 0 {
                    crate::leanh::lean_dec(v_idx_612_);
                    return v_acc_613_;
                } else {
                    v_decls_615_ = crate::leanh::lean_ctor_get(v_aig_610_, 0);
                    v_ref_616_ = lean_array_fget_borrowed(v_s_611_, v_idx_612_);
                    v___x_617_ = crate::leanh::lean_unsigned_to_nat(1);
                    v___x_618_ = lean_nat_shiftr(v_ref_616_, v___x_617_);
                    v_decl_619_ = lean_array_fget_borrowed(v_decls_615_, v___x_618_);
                    crate::leanh::lean_dec(v___x_618_);
                    if crate::leanh::lean_obj_tag(v_decl_619_) == 0 {
                        v___x_620_ = lean_nat_add(v_idx_612_, v___x_617_);
                        crate::leanh::lean_dec(v_idx_612_);
                        v___x_621_ = lean_nat_add(v_acc_613_, v___x_617_);
                        crate::leanh::lean_dec(v_acc_613_);
                        v_idx_612_ = v___x_620_;
                        v_acc_613_ = v___x_621_;
                        state = 0;
                        continue;
                    } else {
                        v___x_623_ = lean_nat_add(v_idx_612_, v___x_617_);
                        crate::leanh::lean_dec(v_idx_612_);
                        v_idx_612_ = v___x_623_;
                        state = 0;
                        continue;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Sat_AIG_RefVec_countKnown_go___redArg___boxed(
    mut v_len_625_: *mut crate::leanh::LeanObject,
    mut v_aig_626_: *mut crate::leanh::LeanObject,
    mut v_s_627_: *mut crate::leanh::LeanObject,
    mut v_idx_628_: *mut crate::leanh::LeanObject,
    mut v_acc_629_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_630_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_630_ = l_Std_Sat_AIG_RefVec_countKnown_go___redArg(
        v_len_625_, v_aig_626_, v_s_627_, v_idx_628_, v_acc_629_,
    );
    crate::leanh::lean_dec_ref(v_s_627_);
    crate::leanh::lean_dec_ref(v_aig_626_);
    crate::leanh::lean_dec(v_len_625_);
    return v_res_630_;
}
pub unsafe fn l_Std_Sat_AIG_RefVec_countKnown_go(
    mut v_00_u03b1_631_: *mut crate::leanh::LeanObject,
    mut v_inst_632_: *mut crate::leanh::LeanObject,
    mut v_inst_633_: *mut crate::leanh::LeanObject,
    mut v_len_634_: *mut crate::leanh::LeanObject,
    mut v_aig_635_: *mut crate::leanh::LeanObject,
    mut v_s_636_: *mut crate::leanh::LeanObject,
    mut v_idx_637_: *mut crate::leanh::LeanObject,
    mut v_acc_638_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_639_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_639_ = l_Std_Sat_AIG_RefVec_countKnown_go___redArg(
        v_len_634_, v_aig_635_, v_s_636_, v_idx_637_, v_acc_638_,
    );
    return v___x_639_;
}
pub unsafe fn l_Std_Sat_AIG_RefVec_countKnown_go___boxed(
    mut v_00_u03b1_640_: *mut crate::leanh::LeanObject,
    mut v_inst_641_: *mut crate::leanh::LeanObject,
    mut v_inst_642_: *mut crate::leanh::LeanObject,
    mut v_len_643_: *mut crate::leanh::LeanObject,
    mut v_aig_644_: *mut crate::leanh::LeanObject,
    mut v_s_645_: *mut crate::leanh::LeanObject,
    mut v_idx_646_: *mut crate::leanh::LeanObject,
    mut v_acc_647_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_648_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_648_ = l_Std_Sat_AIG_RefVec_countKnown_go(
        v_00_u03b1_640_,
        v_inst_641_,
        v_inst_642_,
        v_len_643_,
        v_aig_644_,
        v_s_645_,
        v_idx_646_,
        v_acc_647_,
    );
    crate::leanh::lean_dec_ref(v_s_645_);
    crate::leanh::lean_dec_ref(v_aig_644_);
    crate::leanh::lean_dec(v_len_643_);
    crate::leanh::lean_dec_ref(v_inst_642_);
    crate::leanh::lean_dec_ref(v_inst_641_);
    return v_res_648_;
}
pub unsafe fn l___private_Std_Sat_AIG_RefVec_0__Std_Sat_AIG_RefVec_countKnown_go_match__1_splitter___redArg(
    mut v_decl_649_: *mut crate::leanh::LeanObject,
    mut v_h__1_650_: *mut crate::leanh::LeanObject,
    mut v_h__2_651_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_decl_649_) == 0 {
        let mut v___x_652_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_653_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_651_);
        v___x_652_ = crate::leanh::lean_box(0);
        v___x_653_ = crate::leanh::lean_apply_1(v_h__1_650_, v___x_652_);
        return v___x_653_;
    } else {
        let mut v___x_654_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_650_);
        v___x_654_ =
            crate::leanh::lean_apply_2(v_h__2_651_, v_decl_649_, crate::leanh::lean_box(0));
        return v___x_654_;
    }
}
pub unsafe fn l___private_Std_Sat_AIG_RefVec_0__Std_Sat_AIG_RefVec_countKnown_go_match__1_splitter(
    mut v_00_u03b1_655_: *mut crate::leanh::LeanObject,
    mut v_motive_656_: *mut crate::leanh::LeanObject,
    mut v_decl_657_: *mut crate::leanh::LeanObject,
    mut v_h__1_658_: *mut crate::leanh::LeanObject,
    mut v_h__2_659_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_decl_657_) == 0 {
        let mut v___x_660_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_661_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_659_);
        v___x_660_ = crate::leanh::lean_box(0);
        v___x_661_ = crate::leanh::lean_apply_1(v_h__1_658_, v___x_660_);
        return v___x_661_;
    } else {
        let mut v___x_662_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_658_);
        v___x_662_ =
            crate::leanh::lean_apply_2(v_h__2_659_, v_decl_657_, crate::leanh::lean_box(0));
        return v___x_662_;
    }
}
pub unsafe fn l_Std_Sat_AIG_RefVec_countKnown___redArg(
    mut v_len_663_: *mut crate::leanh::LeanObject,
    mut v_aig_664_: *mut crate::leanh::LeanObject,
    mut v_s_665_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_666_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_667_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_666_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_667_ = l_Std_Sat_AIG_RefVec_countKnown_go___redArg(
        v_len_663_, v_aig_664_, v_s_665_, v___x_666_, v___x_666_,
    );
    return v___x_667_;
}
pub unsafe fn l_Std_Sat_AIG_RefVec_countKnown___redArg___boxed(
    mut v_len_668_: *mut crate::leanh::LeanObject,
    mut v_aig_669_: *mut crate::leanh::LeanObject,
    mut v_s_670_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_671_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_671_ = l_Std_Sat_AIG_RefVec_countKnown___redArg(v_len_668_, v_aig_669_, v_s_670_);
    crate::leanh::lean_dec_ref(v_s_670_);
    crate::leanh::lean_dec_ref(v_aig_669_);
    crate::leanh::lean_dec(v_len_668_);
    return v_res_671_;
}
pub unsafe fn l_Std_Sat_AIG_RefVec_countKnown(
    mut v_00_u03b1_672_: *mut crate::leanh::LeanObject,
    mut v_inst_673_: *mut crate::leanh::LeanObject,
    mut v_inst_674_: *mut crate::leanh::LeanObject,
    mut v_len_675_: *mut crate::leanh::LeanObject,
    mut v_aig_676_: *mut crate::leanh::LeanObject,
    mut v_s_677_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_678_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_678_ = l_Std_Sat_AIG_RefVec_countKnown___redArg(v_len_675_, v_aig_676_, v_s_677_);
    return v___x_678_;
}
pub unsafe fn l_Std_Sat_AIG_RefVec_countKnown___boxed(
    mut v_00_u03b1_679_: *mut crate::leanh::LeanObject,
    mut v_inst_680_: *mut crate::leanh::LeanObject,
    mut v_inst_681_: *mut crate::leanh::LeanObject,
    mut v_len_682_: *mut crate::leanh::LeanObject,
    mut v_aig_683_: *mut crate::leanh::LeanObject,
    mut v_s_684_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_685_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_685_ = l_Std_Sat_AIG_RefVec_countKnown(
        v_00_u03b1_679_,
        v_inst_680_,
        v_inst_681_,
        v_len_682_,
        v_aig_683_,
        v_s_684_,
    );
    crate::leanh::lean_dec_ref(v_s_684_);
    crate::leanh::lean_dec_ref(v_aig_683_);
    crate::leanh::lean_dec(v_len_682_);
    crate::leanh::lean_dec_ref(v_inst_681_);
    crate::leanh::lean_dec_ref(v_inst_680_);
    return v_res_685_;
}
pub unsafe fn l_Std_Sat_AIG_BinaryRefVec_cast___redArg(
    mut v_s_686_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_lhs_687_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_rhs_688_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_690_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_691_: u8 = 0;
    let mut v___x_693_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_694_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_695_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_lhs_687_ = crate::leanh::lean_ctor_get(v_s_686_, 0);
                v_rhs_688_ = crate::leanh::lean_ctor_get(v_s_686_, 1);
                v_isSharedCheck_695_ = (!crate::leanh::lean_is_exclusive(v_s_686_)) as u8;
                if v_isSharedCheck_695_ == 0 {
                    v___x_690_ = v_s_686_;
                    v_isShared_691_ = v_isSharedCheck_695_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_rhs_688_);
                    crate::leanh::lean_inc(v_lhs_687_);
                    crate::leanh::lean_dec(v_s_686_);
                    v___x_690_ = crate::leanh::lean_box(0);
                    v_isShared_691_ = v_isSharedCheck_695_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                if v_isShared_691_ == 0 {
                    v___x_693_ = v___x_690_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_694_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_694_, 0, v_lhs_687_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_694_, 1, v_rhs_688_);
                    v___x_693_ = v_reuseFailAlloc_694_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_693_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Sat_AIG_BinaryRefVec_cast(
    mut v_00_u03b1_696_: *mut crate::leanh::LeanObject,
    mut v_inst_697_: *mut crate::leanh::LeanObject,
    mut v_inst_698_: *mut crate::leanh::LeanObject,
    mut v_len_699_: *mut crate::leanh::LeanObject,
    mut v_aig1_700_: *mut crate::leanh::LeanObject,
    mut v_aig2_701_: *mut crate::leanh::LeanObject,
    mut v_s_702_: *mut crate::leanh::LeanObject,
    mut v_h_703_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_lhs_704_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_rhs_705_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_707_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_708_: u8 = 0;
    let mut v___x_710_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_711_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_712_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_lhs_704_ = crate::leanh::lean_ctor_get(v_s_702_, 0);
                v_rhs_705_ = crate::leanh::lean_ctor_get(v_s_702_, 1);
                v_isSharedCheck_712_ = (!crate::leanh::lean_is_exclusive(v_s_702_)) as u8;
                if v_isSharedCheck_712_ == 0 {
                    v___x_707_ = v_s_702_;
                    v_isShared_708_ = v_isSharedCheck_712_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_rhs_705_);
                    crate::leanh::lean_inc(v_lhs_704_);
                    crate::leanh::lean_dec(v_s_702_);
                    v___x_707_ = crate::leanh::lean_box(0);
                    v_isShared_708_ = v_isSharedCheck_712_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                if v_isShared_708_ == 0 {
                    v___x_710_ = v___x_707_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_711_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_711_, 0, v_lhs_704_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_711_, 1, v_rhs_705_);
                    v___x_710_ = v_reuseFailAlloc_711_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_710_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Sat_AIG_BinaryRefVec_cast___boxed(
    mut v_00_u03b1_713_: *mut crate::leanh::LeanObject,
    mut v_inst_714_: *mut crate::leanh::LeanObject,
    mut v_inst_715_: *mut crate::leanh::LeanObject,
    mut v_len_716_: *mut crate::leanh::LeanObject,
    mut v_aig1_717_: *mut crate::leanh::LeanObject,
    mut v_aig2_718_: *mut crate::leanh::LeanObject,
    mut v_s_719_: *mut crate::leanh::LeanObject,
    mut v_h_720_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_721_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_721_ = l_Std_Sat_AIG_BinaryRefVec_cast(
        v_00_u03b1_713_,
        v_inst_714_,
        v_inst_715_,
        v_len_716_,
        v_aig1_717_,
        v_aig2_718_,
        v_s_719_,
        v_h_720_,
    );
    crate::leanh::lean_dec_ref(v_aig2_718_);
    crate::leanh::lean_dec_ref(v_aig1_717_);
    crate::leanh::lean_dec(v_len_716_);
    crate::leanh::lean_dec_ref(v_inst_715_);
    crate::leanh::lean_dec_ref(v_inst_714_);
    return v_res_721_;
}
pub unsafe fn l___private_Std_Sat_AIG_RefVec_0__Std_Sat_AIG_BinaryRefVec_cast_match__1_splitter___redArg(
    mut v_s_722_: *mut crate::leanh::LeanObject,
    mut v_h__1_723_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_lhs_724_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_rhs_725_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_726_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_lhs_724_ = crate::leanh::lean_ctor_get(v_s_722_, 0);
    crate::leanh::lean_inc_ref(v_lhs_724_);
    v_rhs_725_ = crate::leanh::lean_ctor_get(v_s_722_, 1);
    crate::leanh::lean_inc_ref(v_rhs_725_);
    crate::leanh::lean_dec_ref(v_s_722_);
    v___x_726_ = crate::leanh::lean_apply_2(v_h__1_723_, v_lhs_724_, v_rhs_725_);
    return v___x_726_;
}
pub unsafe fn l___private_Std_Sat_AIG_RefVec_0__Std_Sat_AIG_BinaryRefVec_cast_match__1_splitter(
    mut v_00_u03b1_727_: *mut crate::leanh::LeanObject,
    mut v_inst_728_: *mut crate::leanh::LeanObject,
    mut v_inst_729_: *mut crate::leanh::LeanObject,
    mut v_len_730_: *mut crate::leanh::LeanObject,
    mut v_aig1_731_: *mut crate::leanh::LeanObject,
    mut v_motive_732_: *mut crate::leanh::LeanObject,
    mut v_s_733_: *mut crate::leanh::LeanObject,
    mut v_h__1_734_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_lhs_735_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_rhs_736_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_737_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_lhs_735_ = crate::leanh::lean_ctor_get(v_s_733_, 0);
    crate::leanh::lean_inc_ref(v_lhs_735_);
    v_rhs_736_ = crate::leanh::lean_ctor_get(v_s_733_, 1);
    crate::leanh::lean_inc_ref(v_rhs_736_);
    crate::leanh::lean_dec_ref(v_s_733_);
    v___x_737_ = crate::leanh::lean_apply_2(v_h__1_734_, v_lhs_735_, v_rhs_736_);
    return v___x_737_;
}
pub unsafe fn l___private_Std_Sat_AIG_RefVec_0__Std_Sat_AIG_BinaryRefVec_cast_match__1_splitter___boxed(
    mut v_00_u03b1_738_: *mut crate::leanh::LeanObject,
    mut v_inst_739_: *mut crate::leanh::LeanObject,
    mut v_inst_740_: *mut crate::leanh::LeanObject,
    mut v_len_741_: *mut crate::leanh::LeanObject,
    mut v_aig1_742_: *mut crate::leanh::LeanObject,
    mut v_motive_743_: *mut crate::leanh::LeanObject,
    mut v_s_744_: *mut crate::leanh::LeanObject,
    mut v_h__1_745_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_746_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_746_ = l___private_Std_Sat_AIG_RefVec_0__Std_Sat_AIG_BinaryRefVec_cast_match__1_splitter(
        v_00_u03b1_738_,
        v_inst_739_,
        v_inst_740_,
        v_len_741_,
        v_aig1_742_,
        v_motive_743_,
        v_s_744_,
        v_h__1_745_,
    );
    crate::leanh::lean_dec_ref(v_aig1_742_);
    crate::leanh::lean_dec(v_len_741_);
    crate::leanh::lean_dec_ref(v_inst_740_);
    crate::leanh::lean_dec_ref(v_inst_739_);
    return v_res_746_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Std_Sat_AIG_RefVec(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Std_Sat_AIG_CachedGatesLemmas(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Vector_Lemmas(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_ByCases(builtin);
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
pub unsafe fn meta_initialize_Std_Sat_AIG_RefVec(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_meta_initialized = true;
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Std_Sat_AIG_RefVec(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Std_Sat_AIG_CachedGatesLemmas(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Vector_Lemmas(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_ByCases(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Omega(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Std_Sat_AIG_RefVec(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Std_Sat_AIG_RefVec(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Std_Sat_AIG_RefVec(builtin);
}
