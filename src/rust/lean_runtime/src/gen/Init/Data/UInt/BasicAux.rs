// Lean compiler output
// Module: Init.Data.UInt.BasicAux
// Imports: Init.Data.BitVec.BasicAux Init.Data.Fin.Basic Init.Data.Nat.Div.Basic
use crate::r#gen::Init::Data::BitVec::BasicAux::{
    initialize_Init_Data_BitVec_BasicAux, runtime_initialize_Init_Data_BitVec_BasicAux,
};
use crate::r#gen::Init::Data::Fin::Basic::{
    initialize_Init_Data_Fin_Basic, runtime_initialize_Init_Data_Fin_Basic,
};
use crate::r#gen::Init::Data::Nat::Div::Basic::{
    initialize_Init_Data_Nat_Div_Basic, runtime_initialize_Init_Data_Nat_Div_Basic,
};
use crate::r#gen::Init::Prelude::l_System_Platform_numBits;
use crate::lean_imports_rs::Init::Prelude::{
    lean_nat_dec_le, lean_nat_dec_lt, lean_nat_pow, lean_nat_sub, lean_uint8_of_nat,
    lean_uint8_to_nat, lean_uint16_of_nat, lean_uint16_to_nat, lean_uint32_of_nat,
    lean_uint32_to_nat, lean_uint64_of_nat, lean_uint64_to_nat, lean_usize_of_nat,
    lean_usize_to_nat,
};
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_box, lean_box_uint32, lean_box_uint64, lean_box_usize,
    lean_cstr_to_nat, lean_dec, lean_dec_ref, lean_io_result_is_error, lean_io_result_mk_ok,
    lean_mark_persistent, lean_obj_once, lean_uint8_once, lean_uint16_once, lean_uint32_once,
    lean_uint64_once, lean_unbox, lean_unbox_uint32, lean_unbox_uint64, lean_unbox_usize,
    lean_unsigned_to_nat, lean_usize_once,
};
static mut l_UInt8_ofNatClamp___closed__0_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_UInt8_ofNatClamp___closed__0: u8 = 0;
static mut l_UInt16_ofNatClamp___closed__0_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_UInt16_ofNatClamp___closed__0: u16 = 0;
static mut l_UInt32_ofNatClamp___closed__0_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_UInt32_ofNatClamp___closed__0: u32 = 0;
pub static l_instAddUInt32___closed__0_value: LeanClosureObject<0> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_UInt32_add___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_instAddUInt32___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_instAddUInt32___closed__0_value) as *mut LeanObject;
pub static mut l_instAddUInt32: *mut LeanObject =
    core::ptr::addr_of!(l_instAddUInt32___closed__0_value) as *mut LeanObject;
pub static l_instSubUInt32___closed__0_value: LeanClosureObject<0> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_UInt32_sub___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_instSubUInt32___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_instSubUInt32___closed__0_value) as *mut LeanObject;
pub static mut l_instSubUInt32: *mut LeanObject =
    core::ptr::addr_of!(l_instSubUInt32___closed__0_value) as *mut LeanObject;
static mut l_UInt64_ofNatClamp___closed__0_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_UInt64_ofNatClamp___closed__0: *mut LeanObject = core::ptr::null_mut();
static mut l_UInt64_ofNatClamp___closed__1_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_UInt64_ofNatClamp___closed__1: *mut LeanObject = core::ptr::null_mut();
static mut l_UInt64_ofNatClamp___closed__2_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_UInt64_ofNatClamp___closed__2: u64 = 0;
static mut l_USize_ofNatClamp___closed__0_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_USize_ofNatClamp___closed__0: *mut LeanObject = core::ptr::null_mut();
static mut l_USize_ofNatClamp___closed__1_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_USize_ofNatClamp___closed__1: *mut LeanObject = core::ptr::null_mut();
static mut l_USize_ofNatClamp___closed__2_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_USize_ofNatClamp___closed__2: usize = 0;
pub static l_instAddUSize___closed__0_value: LeanClosureObject<0> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_USize_add___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_instAddUSize___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_instAddUSize___closed__0_value) as *mut LeanObject;
pub static mut l_instAddUSize: *mut LeanObject =
    core::ptr::addr_of!(l_instAddUSize___closed__0_value) as *mut LeanObject;
pub static l_instSubUSize___closed__0_value: LeanClosureObject<0> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_USize_sub___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_instSubUSize___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_instSubUSize___closed__0_value) as *mut LeanObject;
pub static mut l_instSubUSize: *mut LeanObject =
    core::ptr::addr_of!(l_instSubUSize___closed__0_value) as *mut LeanObject;
pub static mut l_instLTUSize: *mut LeanObject = core::ptr::null_mut();
pub static mut l_instLEUSize: *mut LeanObject = core::ptr::null_mut();
pub unsafe fn l_UInt8_toFin(mut v_x_331_: u8) -> *mut LeanObject {
    let mut v___x_332_: *mut LeanObject = core::ptr::null_mut();
    v___x_332_ = lean_uint8_to_nat(v_x_331_);
    return v___x_332_;
}
pub unsafe fn l_UInt8_toFin___boxed(mut v_x_333_: *mut LeanObject) -> *mut LeanObject {
    let mut v_x_boxed_334_: u8 = 0;
    let mut v_res_335_: *mut LeanObject = core::ptr::null_mut();
    v_x_boxed_334_ = (lean_unbox(v_x_333_) as u8);
    v_res_335_ = l_UInt8_toFin(v_x_boxed_334_);
    return v_res_335_;
}
pub unsafe fn _init_l_UInt8_ofNatClamp___closed__0() -> u8 {
    let mut v___x_336_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_337_: u8 = 0;
    v___x_336_ = lean_unsigned_to_nat(255);
    v___x_337_ = lean_uint8_of_nat(v___x_336_);
    return v___x_337_;
}
pub unsafe fn l_UInt8_ofNatClamp(mut v_n_338_: *mut LeanObject) -> u8 {
    let mut v___x_339_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_340_: u8 = 0;
    v___x_339_ = lean_unsigned_to_nat(256);
    v___x_340_ = lean_nat_dec_lt(v_n_338_, v___x_339_);
    if v___x_340_ == 0 {
        let mut v___x_341_: u8 = 0;
        v___x_341_ = lean_uint8_once(
            core::ptr::addr_of_mut!(l_UInt8_ofNatClamp___closed__0),
            core::ptr::addr_of_mut!(l_UInt8_ofNatClamp___closed__0_once),
            _init_l_UInt8_ofNatClamp___closed__0,
        );
        return v___x_341_;
    } else {
        let mut v___x_342_: u8 = 0;
        v___x_342_ = lean_uint8_of_nat(v_n_338_);
        return v___x_342_;
    }
}
pub unsafe fn l_UInt8_ofNatClamp___boxed(mut v_n_343_: *mut LeanObject) -> *mut LeanObject {
    let mut v_res_344_: u8 = 0;
    let mut v_r_345_: *mut LeanObject = core::ptr::null_mut();
    v_res_344_ = l_UInt8_ofNatClamp(v_n_343_);
    lean_dec(v_n_343_);
    v_r_345_ = lean_box((v_res_344_) as usize);
    return v_r_345_;
}
pub unsafe fn l_UInt8_ofNatTruncate(mut v_n_346_: *mut LeanObject) -> u8 {
    let mut v___x_347_: u8 = 0;
    v___x_347_ = l_UInt8_ofNatClamp(v_n_346_);
    return v___x_347_;
}
pub unsafe fn l_UInt8_ofNatTruncate___boxed(mut v_n_348_: *mut LeanObject) -> *mut LeanObject {
    let mut v_res_349_: u8 = 0;
    let mut v_r_350_: *mut LeanObject = core::ptr::null_mut();
    v_res_349_ = l_UInt8_ofNatTruncate(v_n_348_);
    lean_dec(v_n_348_);
    v_r_350_ = lean_box((v_res_349_) as usize);
    return v_r_350_;
}
pub unsafe fn l_Nat_toUInt8(mut v_n_351_: *mut LeanObject) -> u8 {
    let mut v___x_352_: u8 = 0;
    v___x_352_ = lean_uint8_of_nat(v_n_351_);
    return v___x_352_;
}
pub unsafe fn l_Nat_toUInt8___boxed(mut v_n_353_: *mut LeanObject) -> *mut LeanObject {
    let mut v_res_354_: u8 = 0;
    let mut v_r_355_: *mut LeanObject = core::ptr::null_mut();
    v_res_354_ = l_Nat_toUInt8(v_n_353_);
    lean_dec(v_n_353_);
    v_r_355_ = lean_box((v_res_354_) as usize);
    return v_r_355_;
}
pub unsafe fn l_UInt8_toNat___boxed(mut v_n_357_: *mut LeanObject) -> *mut LeanObject {
    let mut v_n_boxed_358_: u8 = 0;
    let mut v_res_359_: *mut LeanObject = core::ptr::null_mut();
    v_n_boxed_358_ = (lean_unbox(v_n_357_) as u8);
    v_res_359_ = lean_uint8_to_nat(v_n_boxed_358_);
    return v_res_359_;
}
pub unsafe fn l_UInt8_instOfNat(mut v_n_360_: *mut LeanObject) -> u8 {
    let mut v___x_361_: u8 = 0;
    v___x_361_ = lean_uint8_of_nat(v_n_360_);
    return v___x_361_;
}
pub unsafe fn l_UInt8_instOfNat___boxed(mut v_n_362_: *mut LeanObject) -> *mut LeanObject {
    let mut v_res_363_: u8 = 0;
    let mut v_r_364_: *mut LeanObject = core::ptr::null_mut();
    v_res_363_ = l_UInt8_instOfNat(v_n_362_);
    lean_dec(v_n_362_);
    v_r_364_ = lean_box((v_res_363_) as usize);
    return v_r_364_;
}
pub unsafe fn l_UInt16_toFin(mut v_x_365_: u16) -> *mut LeanObject {
    let mut v___x_366_: *mut LeanObject = core::ptr::null_mut();
    v___x_366_ = lean_uint16_to_nat(v_x_365_);
    return v___x_366_;
}
pub unsafe fn l_UInt16_toFin___boxed(mut v_x_367_: *mut LeanObject) -> *mut LeanObject {
    let mut v_x_boxed_368_: u16 = 0;
    let mut v_res_369_: *mut LeanObject = core::ptr::null_mut();
    v_x_boxed_368_ = (lean_unbox(v_x_367_) as u16);
    v_res_369_ = l_UInt16_toFin(v_x_boxed_368_);
    return v_res_369_;
}
pub unsafe fn l_UInt16_ofNat___boxed(mut v_n_371_: *mut LeanObject) -> *mut LeanObject {
    let mut v_res_372_: u16 = 0;
    let mut v_r_373_: *mut LeanObject = core::ptr::null_mut();
    v_res_372_ = lean_uint16_of_nat(v_n_371_);
    lean_dec(v_n_371_);
    v_r_373_ = lean_box((v_res_372_) as usize);
    return v_r_373_;
}
pub unsafe fn _init_l_UInt16_ofNatClamp___closed__0() -> u16 {
    let mut v___x_374_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_375_: u16 = 0;
    v___x_374_ = lean_unsigned_to_nat(65535);
    v___x_375_ = lean_uint16_of_nat(v___x_374_);
    return v___x_375_;
}
pub unsafe fn l_UInt16_ofNatClamp(mut v_n_376_: *mut LeanObject) -> u16 {
    let mut v___x_377_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_378_: u8 = 0;
    v___x_377_ = lean_unsigned_to_nat(65536);
    v___x_378_ = lean_nat_dec_lt(v_n_376_, v___x_377_);
    if v___x_378_ == 0 {
        let mut v___x_379_: u16 = 0;
        v___x_379_ = lean_uint16_once(
            core::ptr::addr_of_mut!(l_UInt16_ofNatClamp___closed__0),
            core::ptr::addr_of_mut!(l_UInt16_ofNatClamp___closed__0_once),
            _init_l_UInt16_ofNatClamp___closed__0,
        );
        return v___x_379_;
    } else {
        let mut v___x_380_: u16 = 0;
        v___x_380_ = lean_uint16_of_nat(v_n_376_);
        return v___x_380_;
    }
}
pub unsafe fn l_UInt16_ofNatClamp___boxed(mut v_n_381_: *mut LeanObject) -> *mut LeanObject {
    let mut v_res_382_: u16 = 0;
    let mut v_r_383_: *mut LeanObject = core::ptr::null_mut();
    v_res_382_ = l_UInt16_ofNatClamp(v_n_381_);
    lean_dec(v_n_381_);
    v_r_383_ = lean_box((v_res_382_) as usize);
    return v_r_383_;
}
pub unsafe fn l_UInt16_ofNatTruncate(mut v_n_384_: *mut LeanObject) -> u16 {
    let mut v___x_385_: u16 = 0;
    v___x_385_ = l_UInt16_ofNatClamp(v_n_384_);
    return v___x_385_;
}
pub unsafe fn l_UInt16_ofNatTruncate___boxed(mut v_n_386_: *mut LeanObject) -> *mut LeanObject {
    let mut v_res_387_: u16 = 0;
    let mut v_r_388_: *mut LeanObject = core::ptr::null_mut();
    v_res_387_ = l_UInt16_ofNatTruncate(v_n_386_);
    lean_dec(v_n_386_);
    v_r_388_ = lean_box((v_res_387_) as usize);
    return v_r_388_;
}
pub unsafe fn l_Nat_toUInt16(mut v_n_389_: *mut LeanObject) -> u16 {
    let mut v___x_390_: u16 = 0;
    v___x_390_ = lean_uint16_of_nat(v_n_389_);
    return v___x_390_;
}
pub unsafe fn l_Nat_toUInt16___boxed(mut v_n_391_: *mut LeanObject) -> *mut LeanObject {
    let mut v_res_392_: u16 = 0;
    let mut v_r_393_: *mut LeanObject = core::ptr::null_mut();
    v_res_392_ = l_Nat_toUInt16(v_n_391_);
    lean_dec(v_n_391_);
    v_r_393_ = lean_box((v_res_392_) as usize);
    return v_r_393_;
}
pub unsafe fn l_UInt16_toNat___boxed(mut v_n_395_: *mut LeanObject) -> *mut LeanObject {
    let mut v_n_boxed_396_: u16 = 0;
    let mut v_res_397_: *mut LeanObject = core::ptr::null_mut();
    v_n_boxed_396_ = (lean_unbox(v_n_395_) as u16);
    v_res_397_ = lean_uint16_to_nat(v_n_boxed_396_);
    return v_res_397_;
}
pub unsafe fn l_UInt16_toUInt8___boxed(mut v_a_399_: *mut LeanObject) -> *mut LeanObject {
    let mut v_a_boxed_400_: u16 = 0;
    let mut v_res_401_: u8 = 0;
    let mut v_r_402_: *mut LeanObject = core::ptr::null_mut();
    v_a_boxed_400_ = (lean_unbox(v_a_399_) as u16);
    v_res_401_ = lean_uint16_to_uint8(v_a_boxed_400_);
    v_r_402_ = lean_box((v_res_401_) as usize);
    return v_r_402_;
}
pub unsafe fn l_UInt8_toUInt16___boxed(mut v_a_404_: *mut LeanObject) -> *mut LeanObject {
    let mut v_a_boxed_405_: u8 = 0;
    let mut v_res_406_: u16 = 0;
    let mut v_r_407_: *mut LeanObject = core::ptr::null_mut();
    v_a_boxed_405_ = (lean_unbox(v_a_404_) as u8);
    v_res_406_ = lean_uint8_to_uint16(v_a_boxed_405_);
    v_r_407_ = lean_box((v_res_406_) as usize);
    return v_r_407_;
}
pub unsafe fn l_UInt16_instOfNat(mut v_n_408_: *mut LeanObject) -> u16 {
    let mut v___x_409_: u16 = 0;
    v___x_409_ = lean_uint16_of_nat(v_n_408_);
    return v___x_409_;
}
pub unsafe fn l_UInt16_instOfNat___boxed(mut v_n_410_: *mut LeanObject) -> *mut LeanObject {
    let mut v_res_411_: u16 = 0;
    let mut v_r_412_: *mut LeanObject = core::ptr::null_mut();
    v_res_411_ = l_UInt16_instOfNat(v_n_410_);
    lean_dec(v_n_410_);
    v_r_412_ = lean_box((v_res_411_) as usize);
    return v_r_412_;
}
pub unsafe fn l_UInt32_toFin(mut v_x_413_: u32) -> *mut LeanObject {
    let mut v___x_414_: *mut LeanObject = core::ptr::null_mut();
    v___x_414_ = lean_uint32_to_nat(v_x_413_);
    return v___x_414_;
}
pub unsafe fn l_UInt32_toFin___boxed(mut v_x_415_: *mut LeanObject) -> *mut LeanObject {
    let mut v_x_boxed_416_: u32 = 0;
    let mut v_res_417_: *mut LeanObject = core::ptr::null_mut();
    v_x_boxed_416_ = lean_unbox_uint32(v_x_415_);
    lean_dec(v_x_415_);
    v_res_417_ = l_UInt32_toFin(v_x_boxed_416_);
    return v_res_417_;
}
pub unsafe fn l_UInt32_ofNat___boxed(mut v_n_419_: *mut LeanObject) -> *mut LeanObject {
    let mut v_res_420_: u32 = 0;
    let mut v_r_421_: *mut LeanObject = core::ptr::null_mut();
    v_res_420_ = lean_uint32_of_nat(v_n_419_);
    lean_dec(v_n_419_);
    v_r_421_ = lean_box_uint32(v_res_420_);
    return v_r_421_;
}
pub unsafe fn _init_l_UInt32_ofNatClamp___closed__0() -> u32 {
    let mut v___x_422_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_423_: u32 = 0;
    v___x_422_ = lean_unsigned_to_nat(4294967295);
    v___x_423_ = lean_uint32_of_nat(v___x_422_);
    return v___x_423_;
}
pub unsafe fn l_UInt32_ofNatClamp(mut v_n_424_: *mut LeanObject) -> u32 {
    let mut v___x_425_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_426_: u8 = 0;
    v___x_425_ = lean_cstr_to_nat(b"4294967296\0".as_ptr().cast());
    v___x_426_ = lean_nat_dec_lt(v_n_424_, v___x_425_);
    if v___x_426_ == 0 {
        let mut v___x_427_: u32 = 0;
        v___x_427_ = lean_uint32_once(
            core::ptr::addr_of_mut!(l_UInt32_ofNatClamp___closed__0),
            core::ptr::addr_of_mut!(l_UInt32_ofNatClamp___closed__0_once),
            _init_l_UInt32_ofNatClamp___closed__0,
        );
        return v___x_427_;
    } else {
        let mut v___x_428_: u32 = 0;
        v___x_428_ = lean_uint32_of_nat(v_n_424_);
        return v___x_428_;
    }
}
pub unsafe fn l_UInt32_ofNatClamp___boxed(mut v_n_429_: *mut LeanObject) -> *mut LeanObject {
    let mut v_res_430_: u32 = 0;
    let mut v_r_431_: *mut LeanObject = core::ptr::null_mut();
    v_res_430_ = l_UInt32_ofNatClamp(v_n_429_);
    lean_dec(v_n_429_);
    v_r_431_ = lean_box_uint32(v_res_430_);
    return v_r_431_;
}
pub unsafe fn l_UInt32_ofNatTruncate(mut v_n_432_: *mut LeanObject) -> u32 {
    let mut v___x_433_: u32 = 0;
    v___x_433_ = l_UInt32_ofNatClamp(v_n_432_);
    return v___x_433_;
}
pub unsafe fn l_UInt32_ofNatTruncate___boxed(mut v_n_434_: *mut LeanObject) -> *mut LeanObject {
    let mut v_res_435_: u32 = 0;
    let mut v_r_436_: *mut LeanObject = core::ptr::null_mut();
    v_res_435_ = l_UInt32_ofNatTruncate(v_n_434_);
    lean_dec(v_n_434_);
    v_r_436_ = lean_box_uint32(v_res_435_);
    return v_r_436_;
}
pub unsafe fn l_Nat_toUInt32(mut v_n_437_: *mut LeanObject) -> u32 {
    let mut v___x_438_: u32 = 0;
    v___x_438_ = lean_uint32_of_nat(v_n_437_);
    return v___x_438_;
}
pub unsafe fn l_Nat_toUInt32___boxed(mut v_n_439_: *mut LeanObject) -> *mut LeanObject {
    let mut v_res_440_: u32 = 0;
    let mut v_r_441_: *mut LeanObject = core::ptr::null_mut();
    v_res_440_ = l_Nat_toUInt32(v_n_439_);
    lean_dec(v_n_439_);
    v_r_441_ = lean_box_uint32(v_res_440_);
    return v_r_441_;
}
pub unsafe fn l_UInt32_toUInt8___boxed(mut v_a_443_: *mut LeanObject) -> *mut LeanObject {
    let mut v_a_boxed_444_: u32 = 0;
    let mut v_res_445_: u8 = 0;
    let mut v_r_446_: *mut LeanObject = core::ptr::null_mut();
    v_a_boxed_444_ = lean_unbox_uint32(v_a_443_);
    lean_dec(v_a_443_);
    v_res_445_ = lean_uint32_to_uint8(v_a_boxed_444_);
    v_r_446_ = lean_box((v_res_445_) as usize);
    return v_r_446_;
}
pub unsafe fn l_UInt32_toUInt16___boxed(mut v_a_448_: *mut LeanObject) -> *mut LeanObject {
    let mut v_a_boxed_449_: u32 = 0;
    let mut v_res_450_: u16 = 0;
    let mut v_r_451_: *mut LeanObject = core::ptr::null_mut();
    v_a_boxed_449_ = lean_unbox_uint32(v_a_448_);
    lean_dec(v_a_448_);
    v_res_450_ = lean_uint32_to_uint16(v_a_boxed_449_);
    v_r_451_ = lean_box((v_res_450_) as usize);
    return v_r_451_;
}
pub unsafe fn l_UInt8_toUInt32___boxed(mut v_a_453_: *mut LeanObject) -> *mut LeanObject {
    let mut v_a_boxed_454_: u8 = 0;
    let mut v_res_455_: u32 = 0;
    let mut v_r_456_: *mut LeanObject = core::ptr::null_mut();
    v_a_boxed_454_ = (lean_unbox(v_a_453_) as u8);
    v_res_455_ = lean_uint8_to_uint32(v_a_boxed_454_);
    v_r_456_ = lean_box_uint32(v_res_455_);
    return v_r_456_;
}
pub unsafe fn l_UInt16_toUInt32___boxed(mut v_a_458_: *mut LeanObject) -> *mut LeanObject {
    let mut v_a_boxed_459_: u16 = 0;
    let mut v_res_460_: u32 = 0;
    let mut v_r_461_: *mut LeanObject = core::ptr::null_mut();
    v_a_boxed_459_ = (lean_unbox(v_a_458_) as u16);
    v_res_460_ = lean_uint16_to_uint32(v_a_boxed_459_);
    v_r_461_ = lean_box_uint32(v_res_460_);
    return v_r_461_;
}
pub unsafe fn l_UInt32_instOfNat(mut v_n_462_: *mut LeanObject) -> u32 {
    let mut v___x_463_: u32 = 0;
    v___x_463_ = lean_uint32_of_nat(v_n_462_);
    return v___x_463_;
}
pub unsafe fn l_UInt32_instOfNat___boxed(mut v_n_464_: *mut LeanObject) -> *mut LeanObject {
    let mut v_res_465_: u32 = 0;
    let mut v_r_466_: *mut LeanObject = core::ptr::null_mut();
    v_res_465_ = l_UInt32_instOfNat(v_n_464_);
    lean_dec(v_n_464_);
    v_r_466_ = lean_box_uint32(v_res_465_);
    return v_r_466_;
}
pub unsafe fn l_UInt32_add___boxed(
    mut v_a_469_: *mut LeanObject,
    mut v_b_470_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_boxed_471_: u32 = 0;
    let mut v_b_boxed_472_: u32 = 0;
    let mut v_res_473_: u32 = 0;
    let mut v_r_474_: *mut LeanObject = core::ptr::null_mut();
    v_a_boxed_471_ = lean_unbox_uint32(v_a_469_);
    lean_dec(v_a_469_);
    v_b_boxed_472_ = lean_unbox_uint32(v_b_470_);
    lean_dec(v_b_470_);
    v_res_473_ = lean_uint32_add(v_a_boxed_471_, v_b_boxed_472_);
    v_r_474_ = lean_box_uint32(v_res_473_);
    return v_r_474_;
}
pub unsafe fn l_UInt32_sub___boxed(
    mut v_a_477_: *mut LeanObject,
    mut v_b_478_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_boxed_479_: u32 = 0;
    let mut v_b_boxed_480_: u32 = 0;
    let mut v_res_481_: u32 = 0;
    let mut v_r_482_: *mut LeanObject = core::ptr::null_mut();
    v_a_boxed_479_ = lean_unbox_uint32(v_a_477_);
    lean_dec(v_a_477_);
    v_b_boxed_480_ = lean_unbox_uint32(v_b_478_);
    lean_dec(v_b_478_);
    v_res_481_ = lean_uint32_sub(v_a_boxed_479_, v_b_boxed_480_);
    v_r_482_ = lean_box_uint32(v_res_481_);
    return v_r_482_;
}
pub unsafe fn l_UInt64_toFin(mut v_x_487_: u64) -> *mut LeanObject {
    let mut v___x_488_: *mut LeanObject = core::ptr::null_mut();
    v___x_488_ = lean_uint64_to_nat(v_x_487_);
    return v___x_488_;
}
pub unsafe fn l_UInt64_toFin___boxed(mut v_x_489_: *mut LeanObject) -> *mut LeanObject {
    let mut v_x_boxed_490_: u64 = 0;
    let mut v_res_491_: *mut LeanObject = core::ptr::null_mut();
    v_x_boxed_490_ = lean_unbox_uint64(v_x_489_);
    lean_dec_ref(v_x_489_);
    v_res_491_ = l_UInt64_toFin(v_x_boxed_490_);
    return v_res_491_;
}
pub unsafe fn l_UInt64_ofNat___boxed(mut v_n_493_: *mut LeanObject) -> *mut LeanObject {
    let mut v_res_494_: u64 = 0;
    let mut v_r_495_: *mut LeanObject = core::ptr::null_mut();
    v_res_494_ = lean_uint64_of_nat(v_n_493_);
    lean_dec(v_n_493_);
    v_r_495_ = lean_box_uint64(v_res_494_);
    return v_r_495_;
}
pub unsafe fn _init_l_UInt64_ofNatClamp___closed__0() -> *mut LeanObject {
    let mut v___x_496_: *mut LeanObject = core::ptr::null_mut();
    v___x_496_ = lean_cstr_to_nat(b"18446744073709551616\0".as_ptr().cast());
    return v___x_496_;
}
pub unsafe fn _init_l_UInt64_ofNatClamp___closed__1() -> *mut LeanObject {
    let mut v___x_497_: *mut LeanObject = core::ptr::null_mut();
    v___x_497_ = lean_cstr_to_nat(b"18446744073709551615\0".as_ptr().cast());
    return v___x_497_;
}
pub unsafe fn _init_l_UInt64_ofNatClamp___closed__2() -> u64 {
    let mut v___x_498_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_499_: u64 = 0;
    v___x_498_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_UInt64_ofNatClamp___closed__1),
        core::ptr::addr_of_mut!(l_UInt64_ofNatClamp___closed__1_once),
        _init_l_UInt64_ofNatClamp___closed__1,
    );
    v___x_499_ = lean_uint64_of_nat(v___x_498_);
    return v___x_499_;
}
pub unsafe fn l_UInt64_ofNatClamp(mut v_n_500_: *mut LeanObject) -> u64 {
    let mut v___x_501_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_502_: u8 = 0;
    v___x_501_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_UInt64_ofNatClamp___closed__0),
        core::ptr::addr_of_mut!(l_UInt64_ofNatClamp___closed__0_once),
        _init_l_UInt64_ofNatClamp___closed__0,
    );
    v___x_502_ = lean_nat_dec_lt(v_n_500_, v___x_501_);
    if v___x_502_ == 0 {
        let mut v___x_503_: u64 = 0;
        v___x_503_ = lean_uint64_once(
            core::ptr::addr_of_mut!(l_UInt64_ofNatClamp___closed__2),
            core::ptr::addr_of_mut!(l_UInt64_ofNatClamp___closed__2_once),
            _init_l_UInt64_ofNatClamp___closed__2,
        );
        return v___x_503_;
    } else {
        let mut v___x_504_: u64 = 0;
        v___x_504_ = lean_uint64_of_nat(v_n_500_);
        return v___x_504_;
    }
}
pub unsafe fn l_UInt64_ofNatClamp___boxed(mut v_n_505_: *mut LeanObject) -> *mut LeanObject {
    let mut v_res_506_: u64 = 0;
    let mut v_r_507_: *mut LeanObject = core::ptr::null_mut();
    v_res_506_ = l_UInt64_ofNatClamp(v_n_505_);
    lean_dec(v_n_505_);
    v_r_507_ = lean_box_uint64(v_res_506_);
    return v_r_507_;
}
pub unsafe fn l_UInt64_ofNatTruncate(mut v_n_508_: *mut LeanObject) -> u64 {
    let mut v___x_509_: u64 = 0;
    v___x_509_ = l_UInt64_ofNatClamp(v_n_508_);
    return v___x_509_;
}
pub unsafe fn l_UInt64_ofNatTruncate___boxed(mut v_n_510_: *mut LeanObject) -> *mut LeanObject {
    let mut v_res_511_: u64 = 0;
    let mut v_r_512_: *mut LeanObject = core::ptr::null_mut();
    v_res_511_ = l_UInt64_ofNatTruncate(v_n_510_);
    lean_dec(v_n_510_);
    v_r_512_ = lean_box_uint64(v_res_511_);
    return v_r_512_;
}
pub unsafe fn l_Nat_toUInt64(mut v_n_513_: *mut LeanObject) -> u64 {
    let mut v___x_514_: u64 = 0;
    v___x_514_ = lean_uint64_of_nat(v_n_513_);
    return v___x_514_;
}
pub unsafe fn l_Nat_toUInt64___boxed(mut v_n_515_: *mut LeanObject) -> *mut LeanObject {
    let mut v_res_516_: u64 = 0;
    let mut v_r_517_: *mut LeanObject = core::ptr::null_mut();
    v_res_516_ = l_Nat_toUInt64(v_n_515_);
    lean_dec(v_n_515_);
    v_r_517_ = lean_box_uint64(v_res_516_);
    return v_r_517_;
}
pub unsafe fn l_UInt64_toNat___boxed(mut v_n_519_: *mut LeanObject) -> *mut LeanObject {
    let mut v_n_boxed_520_: u64 = 0;
    let mut v_res_521_: *mut LeanObject = core::ptr::null_mut();
    v_n_boxed_520_ = lean_unbox_uint64(v_n_519_);
    lean_dec_ref(v_n_519_);
    v_res_521_ = lean_uint64_to_nat(v_n_boxed_520_);
    return v_res_521_;
}
pub unsafe fn l_UInt64_toUInt8___boxed(mut v_a_523_: *mut LeanObject) -> *mut LeanObject {
    let mut v_a_boxed_524_: u64 = 0;
    let mut v_res_525_: u8 = 0;
    let mut v_r_526_: *mut LeanObject = core::ptr::null_mut();
    v_a_boxed_524_ = lean_unbox_uint64(v_a_523_);
    lean_dec_ref(v_a_523_);
    v_res_525_ = lean_uint64_to_uint8(v_a_boxed_524_);
    v_r_526_ = lean_box((v_res_525_) as usize);
    return v_r_526_;
}
pub unsafe fn l_UInt64_toUInt16___boxed(mut v_a_528_: *mut LeanObject) -> *mut LeanObject {
    let mut v_a_boxed_529_: u64 = 0;
    let mut v_res_530_: u16 = 0;
    let mut v_r_531_: *mut LeanObject = core::ptr::null_mut();
    v_a_boxed_529_ = lean_unbox_uint64(v_a_528_);
    lean_dec_ref(v_a_528_);
    v_res_530_ = lean_uint64_to_uint16(v_a_boxed_529_);
    v_r_531_ = lean_box((v_res_530_) as usize);
    return v_r_531_;
}
pub unsafe fn l_UInt64_toUInt32___boxed(mut v_a_533_: *mut LeanObject) -> *mut LeanObject {
    let mut v_a_boxed_534_: u64 = 0;
    let mut v_res_535_: u32 = 0;
    let mut v_r_536_: *mut LeanObject = core::ptr::null_mut();
    v_a_boxed_534_ = lean_unbox_uint64(v_a_533_);
    lean_dec_ref(v_a_533_);
    v_res_535_ = lean_uint64_to_uint32(v_a_boxed_534_);
    v_r_536_ = lean_box_uint32(v_res_535_);
    return v_r_536_;
}
pub unsafe fn l_UInt8_toUInt64___boxed(mut v_a_538_: *mut LeanObject) -> *mut LeanObject {
    let mut v_a_boxed_539_: u8 = 0;
    let mut v_res_540_: u64 = 0;
    let mut v_r_541_: *mut LeanObject = core::ptr::null_mut();
    v_a_boxed_539_ = (lean_unbox(v_a_538_) as u8);
    v_res_540_ = lean_uint8_to_uint64(v_a_boxed_539_);
    v_r_541_ = lean_box_uint64(v_res_540_);
    return v_r_541_;
}
pub unsafe fn l_UInt16_toUInt64___boxed(mut v_a_543_: *mut LeanObject) -> *mut LeanObject {
    let mut v_a_boxed_544_: u16 = 0;
    let mut v_res_545_: u64 = 0;
    let mut v_r_546_: *mut LeanObject = core::ptr::null_mut();
    v_a_boxed_544_ = (lean_unbox(v_a_543_) as u16);
    v_res_545_ = lean_uint16_to_uint64(v_a_boxed_544_);
    v_r_546_ = lean_box_uint64(v_res_545_);
    return v_r_546_;
}
pub unsafe fn l_UInt32_toUInt64___boxed(mut v_a_548_: *mut LeanObject) -> *mut LeanObject {
    let mut v_a_boxed_549_: u32 = 0;
    let mut v_res_550_: u64 = 0;
    let mut v_r_551_: *mut LeanObject = core::ptr::null_mut();
    v_a_boxed_549_ = lean_unbox_uint32(v_a_548_);
    lean_dec(v_a_548_);
    v_res_550_ = lean_uint32_to_uint64(v_a_boxed_549_);
    v_r_551_ = lean_box_uint64(v_res_550_);
    return v_r_551_;
}
pub unsafe fn l_UInt64_instOfNat(mut v_n_552_: *mut LeanObject) -> u64 {
    let mut v___x_553_: u64 = 0;
    v___x_553_ = lean_uint64_of_nat(v_n_552_);
    return v___x_553_;
}
pub unsafe fn l_UInt64_instOfNat___boxed(mut v_n_554_: *mut LeanObject) -> *mut LeanObject {
    let mut v_res_555_: u64 = 0;
    let mut v_r_556_: *mut LeanObject = core::ptr::null_mut();
    v_res_555_ = l_UInt64_instOfNat(v_n_554_);
    lean_dec(v_n_554_);
    v_r_556_ = lean_box_uint64(v_res_555_);
    return v_r_556_;
}
pub unsafe fn l_USize_toFin(mut v_x_557_: usize) -> *mut LeanObject {
    let mut v___x_558_: *mut LeanObject = core::ptr::null_mut();
    v___x_558_ = lean_usize_to_nat(v_x_557_);
    return v___x_558_;
}
pub unsafe fn l_USize_toFin___boxed(mut v_x_559_: *mut LeanObject) -> *mut LeanObject {
    let mut v_x_boxed_560_: usize = 0;
    let mut v_res_561_: *mut LeanObject = core::ptr::null_mut();
    v_x_boxed_560_ = lean_unbox_usize(v_x_559_);
    lean_dec(v_x_559_);
    v_res_561_ = l_USize_toFin(v_x_boxed_560_);
    return v_res_561_;
}
pub unsafe fn l_USize_ofNat___boxed(mut v_n_563_: *mut LeanObject) -> *mut LeanObject {
    let mut v_res_564_: usize = 0;
    let mut v_r_565_: *mut LeanObject = core::ptr::null_mut();
    v_res_564_ = lean_usize_of_nat(v_n_563_);
    lean_dec(v_n_563_);
    v_r_565_ = lean_box_usize(v_res_564_);
    return v_r_565_;
}
pub unsafe fn _init_l_USize_ofNatClamp___closed__0() -> *mut LeanObject {
    let mut v___x_566_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_567_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_568_: *mut LeanObject = core::ptr::null_mut();
    v___x_566_ = l_System_Platform_numBits;
    v___x_567_ = lean_unsigned_to_nat(2);
    v___x_568_ = lean_nat_pow(v___x_567_, v___x_566_);
    return v___x_568_;
}
pub unsafe fn _init_l_USize_ofNatClamp___closed__1() -> *mut LeanObject {
    let mut v___x_569_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_570_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_571_: *mut LeanObject = core::ptr::null_mut();
    v___x_569_ = lean_unsigned_to_nat(1);
    v___x_570_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_USize_ofNatClamp___closed__0),
        core::ptr::addr_of_mut!(l_USize_ofNatClamp___closed__0_once),
        _init_l_USize_ofNatClamp___closed__0,
    );
    v___x_571_ = lean_nat_sub(v___x_570_, v___x_569_);
    return v___x_571_;
}
pub unsafe fn _init_l_USize_ofNatClamp___closed__2() -> usize {
    let mut v___x_572_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_573_: usize = 0;
    v___x_572_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_USize_ofNatClamp___closed__1),
        core::ptr::addr_of_mut!(l_USize_ofNatClamp___closed__1_once),
        _init_l_USize_ofNatClamp___closed__1,
    );
    v___x_573_ = lean_usize_of_nat(v___x_572_);
    return v___x_573_;
}
pub unsafe fn l_USize_ofNatClamp(mut v_n_574_: *mut LeanObject) -> usize {
    let mut v___x_575_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_576_: u8 = 0;
    v___x_575_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_USize_ofNatClamp___closed__0),
        core::ptr::addr_of_mut!(l_USize_ofNatClamp___closed__0_once),
        _init_l_USize_ofNatClamp___closed__0,
    );
    v___x_576_ = lean_nat_dec_lt(v_n_574_, v___x_575_);
    if v___x_576_ == 0 {
        let mut v___x_577_: usize = 0;
        v___x_577_ = lean_usize_once(
            core::ptr::addr_of_mut!(l_USize_ofNatClamp___closed__2),
            core::ptr::addr_of_mut!(l_USize_ofNatClamp___closed__2_once),
            _init_l_USize_ofNatClamp___closed__2,
        );
        return v___x_577_;
    } else {
        let mut v___x_578_: usize = 0;
        v___x_578_ = lean_usize_of_nat(v_n_574_);
        return v___x_578_;
    }
}
pub unsafe fn l_USize_ofNatClamp___boxed(mut v_n_579_: *mut LeanObject) -> *mut LeanObject {
    let mut v_res_580_: usize = 0;
    let mut v_r_581_: *mut LeanObject = core::ptr::null_mut();
    v_res_580_ = l_USize_ofNatClamp(v_n_579_);
    lean_dec(v_n_579_);
    v_r_581_ = lean_box_usize(v_res_580_);
    return v_r_581_;
}
pub unsafe fn l_USize_ofNatTruncate(mut v_n_582_: *mut LeanObject) -> usize {
    let mut v___x_583_: usize = 0;
    v___x_583_ = l_USize_ofNatClamp(v_n_582_);
    return v___x_583_;
}
pub unsafe fn l_USize_ofNatTruncate___boxed(mut v_n_584_: *mut LeanObject) -> *mut LeanObject {
    let mut v_res_585_: usize = 0;
    let mut v_r_586_: *mut LeanObject = core::ptr::null_mut();
    v_res_585_ = l_USize_ofNatTruncate(v_n_584_);
    lean_dec(v_n_584_);
    v_r_586_ = lean_box_usize(v_res_585_);
    return v_r_586_;
}
pub unsafe fn l_Nat_toUSize(mut v_n_587_: *mut LeanObject) -> usize {
    let mut v___x_588_: usize = 0;
    v___x_588_ = lean_usize_of_nat(v_n_587_);
    return v___x_588_;
}
pub unsafe fn l_Nat_toUSize___boxed(mut v_n_589_: *mut LeanObject) -> *mut LeanObject {
    let mut v_res_590_: usize = 0;
    let mut v_r_591_: *mut LeanObject = core::ptr::null_mut();
    v_res_590_ = l_Nat_toUSize(v_n_589_);
    lean_dec(v_n_589_);
    v_r_591_ = lean_box_usize(v_res_590_);
    return v_r_591_;
}
pub unsafe fn l_USize_toNat___boxed(mut v_n_593_: *mut LeanObject) -> *mut LeanObject {
    let mut v_n_boxed_594_: usize = 0;
    let mut v_res_595_: *mut LeanObject = core::ptr::null_mut();
    v_n_boxed_594_ = lean_unbox_usize(v_n_593_);
    lean_dec(v_n_593_);
    v_res_595_ = lean_usize_to_nat(v_n_boxed_594_);
    return v_res_595_;
}
pub unsafe fn l_USize_add___boxed(
    mut v_a_598_: *mut LeanObject,
    mut v_b_599_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_boxed_600_: usize = 0;
    let mut v_b_boxed_601_: usize = 0;
    let mut v_res_602_: usize = 0;
    let mut v_r_603_: *mut LeanObject = core::ptr::null_mut();
    v_a_boxed_600_ = lean_unbox_usize(v_a_598_);
    lean_dec(v_a_598_);
    v_b_boxed_601_ = lean_unbox_usize(v_b_599_);
    lean_dec(v_b_599_);
    v_res_602_ = lean_usize_add(v_a_boxed_600_, v_b_boxed_601_);
    v_r_603_ = lean_box_usize(v_res_602_);
    return v_r_603_;
}
pub unsafe fn l_USize_sub___boxed(
    mut v_a_606_: *mut LeanObject,
    mut v_b_607_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_boxed_608_: usize = 0;
    let mut v_b_boxed_609_: usize = 0;
    let mut v_res_610_: usize = 0;
    let mut v_r_611_: *mut LeanObject = core::ptr::null_mut();
    v_a_boxed_608_ = lean_unbox_usize(v_a_606_);
    lean_dec(v_a_606_);
    v_b_boxed_609_ = lean_unbox_usize(v_b_607_);
    lean_dec(v_b_607_);
    v_res_610_ = lean_usize_sub(v_a_boxed_608_, v_b_boxed_609_);
    v_r_611_ = lean_box_usize(v_res_610_);
    return v_r_611_;
}
pub unsafe fn l_USize_instOfNat(mut v_n_612_: *mut LeanObject) -> usize {
    let mut v___x_613_: usize = 0;
    v___x_613_ = lean_usize_of_nat(v_n_612_);
    return v___x_613_;
}
pub unsafe fn l_USize_instOfNat___boxed(mut v_n_614_: *mut LeanObject) -> *mut LeanObject {
    let mut v_res_615_: usize = 0;
    let mut v_r_616_: *mut LeanObject = core::ptr::null_mut();
    v_res_615_ = l_USize_instOfNat(v_n_614_);
    lean_dec(v_n_614_);
    v_r_616_ = lean_box_usize(v_res_615_);
    return v_r_616_;
}
pub unsafe fn _init_l_instLTUSize() -> *mut LeanObject {
    let mut v___x_621_: *mut LeanObject = core::ptr::null_mut();
    v___x_621_ = lean_box(0);
    return v___x_621_;
}
pub unsafe fn _init_l_instLEUSize() -> *mut LeanObject {
    let mut v___x_622_: *mut LeanObject = core::ptr::null_mut();
    v___x_622_ = lean_box(0);
    return v___x_622_;
}
pub unsafe fn l_USize_decLt___aux__1(mut v_a_623_: usize, mut v_b_624_: usize) -> u8 {
    let mut v___x_625_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_626_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_627_: u8 = 0;
    v___x_625_ = lean_usize_to_nat(v_a_623_);
    v___x_626_ = lean_usize_to_nat(v_b_624_);
    v___x_627_ = lean_nat_dec_lt(v___x_625_, v___x_626_);
    lean_dec(v___x_626_);
    lean_dec(v___x_625_);
    return v___x_627_;
}
pub unsafe fn l_USize_decLt___aux__1___boxed(
    mut v_a_628_: *mut LeanObject,
    mut v_b_629_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_boxed_630_: usize = 0;
    let mut v_b_boxed_631_: usize = 0;
    let mut v_res_632_: u8 = 0;
    let mut v_r_633_: *mut LeanObject = core::ptr::null_mut();
    v_a_boxed_630_ = lean_unbox_usize(v_a_628_);
    lean_dec(v_a_628_);
    v_b_boxed_631_ = lean_unbox_usize(v_b_629_);
    lean_dec(v_b_629_);
    v_res_632_ = l_USize_decLt___aux__1(v_a_boxed_630_, v_b_boxed_631_);
    v_r_633_ = lean_box((v_res_632_) as usize);
    return v_r_633_;
}
pub unsafe fn l_USize_decLt___boxed(
    mut v_a_636_: *mut LeanObject,
    mut v_b_637_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_boxed_638_: usize = 0;
    let mut v_b_boxed_639_: usize = 0;
    let mut v_res_640_: u8 = 0;
    let mut v_r_641_: *mut LeanObject = core::ptr::null_mut();
    v_a_boxed_638_ = lean_unbox_usize(v_a_636_);
    lean_dec(v_a_636_);
    v_b_boxed_639_ = lean_unbox_usize(v_b_637_);
    lean_dec(v_b_637_);
    v_res_640_ = lean_usize_dec_lt(v_a_boxed_638_, v_b_boxed_639_);
    v_r_641_ = lean_box((v_res_640_) as usize);
    return v_r_641_;
}
pub unsafe fn l_USize_decLe___aux__1(mut v_a_642_: usize, mut v_b_643_: usize) -> u8 {
    let mut v___x_644_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_645_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_646_: u8 = 0;
    v___x_644_ = lean_usize_to_nat(v_a_642_);
    v___x_645_ = lean_usize_to_nat(v_b_643_);
    v___x_646_ = lean_nat_dec_le(v___x_644_, v___x_645_);
    lean_dec(v___x_645_);
    lean_dec(v___x_644_);
    return v___x_646_;
}
pub unsafe fn l_USize_decLe___aux__1___boxed(
    mut v_a_647_: *mut LeanObject,
    mut v_b_648_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_boxed_649_: usize = 0;
    let mut v_b_boxed_650_: usize = 0;
    let mut v_res_651_: u8 = 0;
    let mut v_r_652_: *mut LeanObject = core::ptr::null_mut();
    v_a_boxed_649_ = lean_unbox_usize(v_a_647_);
    lean_dec(v_a_647_);
    v_b_boxed_650_ = lean_unbox_usize(v_b_648_);
    lean_dec(v_b_648_);
    v_res_651_ = l_USize_decLe___aux__1(v_a_boxed_649_, v_b_boxed_650_);
    v_r_652_ = lean_box((v_res_651_) as usize);
    return v_r_652_;
}
pub unsafe fn l_USize_decLe___boxed(
    mut v_a_655_: *mut LeanObject,
    mut v_b_656_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_boxed_657_: usize = 0;
    let mut v_b_boxed_658_: usize = 0;
    let mut v_res_659_: u8 = 0;
    let mut v_r_660_: *mut LeanObject = core::ptr::null_mut();
    v_a_boxed_657_ = lean_unbox_usize(v_a_655_);
    lean_dec(v_a_655_);
    v_b_boxed_658_ = lean_unbox_usize(v_b_656_);
    lean_dec(v_b_656_);
    v_res_659_ = lean_usize_dec_le(v_a_boxed_657_, v_b_boxed_658_);
    v_r_660_ = lean_box((v_res_659_) as usize);
    return v_r_660_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Init_Data_UInt_BasicAux(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Init_Data_BitVec_BasicAux(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Fin_Basic(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Nat_Div_Basic(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    l_instLTUSize = _init_l_instLTUSize();
    lean_mark_persistent(l_instLTUSize);
    l_instLEUSize = _init_l_instLEUSize();
    lean_mark_persistent(l_instLEUSize);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Init_Data_UInt_BasicAux(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_meta_initialized = true;
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Init_Data_UInt_BasicAux(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Init_Data_BitVec_BasicAux(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Data_Fin_Basic(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Data_Nat_Div_Basic(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_UInt_BasicAux(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Init_Data_UInt_BasicAux(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Init_Data_UInt_BasicAux(builtin);
}
