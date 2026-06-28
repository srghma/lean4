// Lean compiler output
// Module: Init.Grind.Ring.Envelope
// Imports: Init.Grind.Ordered.Ring Init.Data.AC Init.Omega Init.RCases
use crate::r#gen::Init::Data::AC::{initialize_Init_Data_AC, runtime_initialize_Init_Data_AC};
use crate::r#gen::Init::Grind::Ordered::Ring::{
    initialize_Init_Grind_Ordered_Ring, runtime_initialize_Init_Grind_Ordered_Ring,
};
use crate::r#gen::Init::Omega::{initialize_Init_Omega, runtime_initialize_Init_Omega};
use crate::r#gen::Init::Prelude::{
    l_Lean_Name_mkStr1, l_Lean_Name_mkStr4, l_Lean_SourceInfo_fromRef, l_Lean_Syntax_getArg,
    l_Lean_Syntax_isOfKind, l_Lean_Syntax_matchesNull, l_Lean_Syntax_node2,
};
use crate::r#gen::Init::RCases::{initialize_Init_RCases, runtime_initialize_Init_RCases};
use crate::lean_imports_rs::Init::Data::Int::Basic::{
    lean_int_dec_lt, lean_nat_abs, lean_nat_to_int,
};
use crate::lean_imports_rs::Init::Prelude::{lean_nat_dec_eq, lean_nat_sub};
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_alloc_closure, lean_alloc_ctor, lean_apply_1,
    lean_apply_2, lean_apply_4, lean_box, lean_closure_set, lean_ctor_get, lean_ctor_set, lean_dec,
    lean_dec_ref, lean_inc, lean_inc_n, lean_inc_ref, lean_inc_ref_n, lean_io_result_is_error,
    lean_io_result_mk_ok, lean_is_exclusive, lean_obj_once, lean_unsigned_to_nat,
};
static mut l_Lean_Grind_Ring_OfSemiring_intCast___redArg___closed__0_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Grind_Ring_OfSemiring_intCast___redArg___closed__0: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Grind_CommRing_OfCommSemiring_toQUnexpander___closed__0_value: LeanStringObject<
    5,
> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 5,
    m_capacity: 5,
    m_length: 4,
    m_data: [76, 101, 97, 110, 0],
};
static mut l_Lean_Grind_CommRing_OfCommSemiring_toQUnexpander___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Grind_CommRing_OfCommSemiring_toQUnexpander___closed__0_value)
        as *mut LeanObject;
pub static l_Lean_Grind_CommRing_OfCommSemiring_toQUnexpander___closed__1_value: LeanStringObject<
    7,
> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 7,
    m_capacity: 7,
    m_length: 6,
    m_data: [80, 97, 114, 115, 101, 114, 0],
};
static mut l_Lean_Grind_CommRing_OfCommSemiring_toQUnexpander___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Grind_CommRing_OfCommSemiring_toQUnexpander___closed__1_value)
        as *mut LeanObject;
pub static l_Lean_Grind_CommRing_OfCommSemiring_toQUnexpander___closed__2_value: LeanStringObject<
    5,
> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 5,
    m_capacity: 5,
    m_length: 4,
    m_data: [84, 101, 114, 109, 0],
};
static mut l_Lean_Grind_CommRing_OfCommSemiring_toQUnexpander___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Grind_CommRing_OfCommSemiring_toQUnexpander___closed__2_value)
        as *mut LeanObject;
pub static l_Lean_Grind_CommRing_OfCommSemiring_toQUnexpander___closed__3_value: LeanStringObject<
    4,
> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 4,
    m_capacity: 4,
    m_length: 3,
    m_data: [97, 112, 112, 0],
};
static mut l_Lean_Grind_CommRing_OfCommSemiring_toQUnexpander___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Grind_CommRing_OfCommSemiring_toQUnexpander___closed__3_value)
        as *mut LeanObject;
static l_Lean_Grind_CommRing_OfCommSemiring_toQUnexpander___closed__4_value_aux_0: LeanCtorObject<
    3,
> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Grind_CommRing_OfCommSemiring_toQUnexpander___closed__0_value)
            as *mut LeanObject,
        11948124481539785030 as *mut LeanObject,
    ],
};
static l_Lean_Grind_CommRing_OfCommSemiring_toQUnexpander___closed__4_value_aux_1: LeanCtorObject<
    3,
> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l_Lean_Grind_CommRing_OfCommSemiring_toQUnexpander___closed__4_value_aux_0
        ) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Grind_CommRing_OfCommSemiring_toQUnexpander___closed__1_value)
            as *mut LeanObject,
        8018486133748762727 as *mut LeanObject,
    ],
};
static l_Lean_Grind_CommRing_OfCommSemiring_toQUnexpander___closed__4_value_aux_2: LeanCtorObject<
    3,
> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l_Lean_Grind_CommRing_OfCommSemiring_toQUnexpander___closed__4_value_aux_1
        ) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Grind_CommRing_OfCommSemiring_toQUnexpander___closed__2_value)
            as *mut LeanObject,
        16572064140653406795 as *mut LeanObject,
    ],
};
pub static l_Lean_Grind_CommRing_OfCommSemiring_toQUnexpander___closed__4_value: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(
                l_Lean_Grind_CommRing_OfCommSemiring_toQUnexpander___closed__4_value_aux_2
            ) as *mut LeanObject,
            core::ptr::addr_of!(
                l_Lean_Grind_CommRing_OfCommSemiring_toQUnexpander___closed__3_value
            ) as *mut LeanObject,
            12966880221525079621 as *mut LeanObject,
        ],
    };
static mut l_Lean_Grind_CommRing_OfCommSemiring_toQUnexpander___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Grind_CommRing_OfCommSemiring_toQUnexpander___closed__4_value)
        as *mut LeanObject;
pub static l_Lean_Grind_CommRing_OfCommSemiring_toQUnexpander___closed__5_value: LeanStringObject<
    12,
> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 12,
    m_capacity: 12,
    m_length: 11,
    m_data: [99, 111, 101, 78, 111, 116, 97, 116, 105, 111, 110, 0],
};
static mut l_Lean_Grind_CommRing_OfCommSemiring_toQUnexpander___closed__5: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Grind_CommRing_OfCommSemiring_toQUnexpander___closed__5_value)
        as *mut LeanObject;
pub static l_Lean_Grind_CommRing_OfCommSemiring_toQUnexpander___closed__6_value: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            (((0 as usize) << 1) | 1) as *mut LeanObject,
            core::ptr::addr_of!(
                l_Lean_Grind_CommRing_OfCommSemiring_toQUnexpander___closed__5_value
            ) as *mut LeanObject,
            4193428478068483112 as *mut LeanObject,
        ],
    };
static mut l_Lean_Grind_CommRing_OfCommSemiring_toQUnexpander___closed__6: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Grind_CommRing_OfCommSemiring_toQUnexpander___closed__6_value)
        as *mut LeanObject;
pub static l_Lean_Grind_CommRing_OfCommSemiring_toQUnexpander___closed__7_value: LeanStringObject<
    4,
> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 4,
    m_capacity: 4,
    m_length: 1,
    m_data: [226, 134, 145, 0],
};
static mut l_Lean_Grind_CommRing_OfCommSemiring_toQUnexpander___closed__7: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Grind_CommRing_OfCommSemiring_toQUnexpander___closed__7_value)
        as *mut LeanObject;
pub unsafe fn l___private_Init_Grind_Ring_Envelope_0__Lean_Grind_Ring_OfSemiring_r_match__1_splitter___redArg(
    mut v_x_427_: *mut LeanObject,
    mut v_x_428_: *mut LeanObject,
    mut v_h__1_429_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_fst_430_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_431_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_432_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_433_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_434_: *mut LeanObject = core::ptr::null_mut();
    v_fst_430_ = lean_ctor_get(v_x_427_, 0);
    lean_inc(v_fst_430_);
    v_snd_431_ = lean_ctor_get(v_x_427_, 1);
    lean_inc(v_snd_431_);
    lean_dec_ref(v_x_427_);
    v_fst_432_ = lean_ctor_get(v_x_428_, 0);
    lean_inc(v_fst_432_);
    v_snd_433_ = lean_ctor_get(v_x_428_, 1);
    lean_inc(v_snd_433_);
    lean_dec_ref(v_x_428_);
    v___x_434_ = lean_apply_4(v_h__1_429_, v_fst_430_, v_snd_431_, v_fst_432_, v_snd_433_);
    return v___x_434_;
}
pub unsafe fn l___private_Init_Grind_Ring_Envelope_0__Lean_Grind_Ring_OfSemiring_r_match__1_splitter(
    mut v_00_u03b1_435_: *mut LeanObject,
    mut v_motive_436_: *mut LeanObject,
    mut v_x_437_: *mut LeanObject,
    mut v_x_438_: *mut LeanObject,
    mut v_h__1_439_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_fst_440_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_441_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_442_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_443_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_444_: *mut LeanObject = core::ptr::null_mut();
    v_fst_440_ = lean_ctor_get(v_x_437_, 0);
    lean_inc(v_fst_440_);
    v_snd_441_ = lean_ctor_get(v_x_437_, 1);
    lean_inc(v_snd_441_);
    lean_dec_ref(v_x_437_);
    v_fst_442_ = lean_ctor_get(v_x_438_, 0);
    lean_inc(v_fst_442_);
    v_snd_443_ = lean_ctor_get(v_x_438_, 1);
    lean_inc(v_snd_443_);
    lean_dec_ref(v_x_438_);
    v___x_444_ = lean_apply_4(v_h__1_439_, v_fst_440_, v_snd_441_, v_fst_442_, v_snd_443_);
    return v___x_444_;
}
pub unsafe fn l_Lean_Grind_Ring_OfSemiring_Q_mk___redArg(
    mut v_p_445_: *mut LeanObject,
) -> *mut LeanObject {
    lean_inc_ref(v_p_445_);
    return v_p_445_;
}
pub unsafe fn l_Lean_Grind_Ring_OfSemiring_Q_mk___redArg___boxed(
    mut v_p_446_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_447_: *mut LeanObject = core::ptr::null_mut();
    v_res_447_ = l_Lean_Grind_Ring_OfSemiring_Q_mk___redArg(v_p_446_);
    lean_dec_ref(v_p_446_);
    return v_res_447_;
}
pub unsafe fn l_Lean_Grind_Ring_OfSemiring_Q_mk(
    mut v_00_u03b1_448_: *mut LeanObject,
    mut v_inst_449_: *mut LeanObject,
    mut v_p_450_: *mut LeanObject,
) -> *mut LeanObject {
    lean_inc_ref(v_p_450_);
    return v_p_450_;
}
pub unsafe fn l_Lean_Grind_Ring_OfSemiring_Q_mk___boxed(
    mut v_00_u03b1_451_: *mut LeanObject,
    mut v_inst_452_: *mut LeanObject,
    mut v_p_453_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_454_: *mut LeanObject = core::ptr::null_mut();
    v_res_454_ = l_Lean_Grind_Ring_OfSemiring_Q_mk(v_00_u03b1_451_, v_inst_452_, v_p_453_);
    lean_dec_ref(v_p_453_);
    lean_dec_ref(v_inst_452_);
    return v_res_454_;
}
pub unsafe fn l_Lean_Grind_Ring_OfSemiring_Q_liftOn_u2082___redArg(
    mut v_q_u2081_455_: *mut LeanObject,
    mut v_q_u2082_456_: *mut LeanObject,
    mut v_f_457_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_458_: *mut LeanObject = core::ptr::null_mut();
    v___x_458_ = lean_apply_2(v_f_457_, v_q_u2081_455_, v_q_u2082_456_);
    return v___x_458_;
}
pub unsafe fn l_Lean_Grind_Ring_OfSemiring_Q_liftOn_u2082(
    mut v_00_u03b1_459_: *mut LeanObject,
    mut v_inst_460_: *mut LeanObject,
    mut v_00_u03b2_461_: *mut LeanObject,
    mut v_q_u2081_462_: *mut LeanObject,
    mut v_q_u2082_463_: *mut LeanObject,
    mut v_f_464_: *mut LeanObject,
    mut v_h_465_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_466_: *mut LeanObject = core::ptr::null_mut();
    v___x_466_ = lean_apply_2(v_f_464_, v_q_u2081_462_, v_q_u2082_463_);
    return v___x_466_;
}
pub unsafe fn l_Lean_Grind_Ring_OfSemiring_Q_liftOn_u2082___boxed(
    mut v_00_u03b1_467_: *mut LeanObject,
    mut v_inst_468_: *mut LeanObject,
    mut v_00_u03b2_469_: *mut LeanObject,
    mut v_q_u2081_470_: *mut LeanObject,
    mut v_q_u2082_471_: *mut LeanObject,
    mut v_f_472_: *mut LeanObject,
    mut v_h_473_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_474_: *mut LeanObject = core::ptr::null_mut();
    v_res_474_ = l_Lean_Grind_Ring_OfSemiring_Q_liftOn_u2082(
        v_00_u03b1_467_,
        v_inst_468_,
        v_00_u03b2_469_,
        v_q_u2081_470_,
        v_q_u2082_471_,
        v_f_472_,
        v_h_473_,
    );
    lean_dec_ref(v_inst_468_);
    return v_res_474_;
}
pub unsafe fn l_Lean_Grind_Ring_OfSemiring_natCast___redArg(
    mut v_inst_475_: *mut LeanObject,
    mut v_n_476_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_natCast_477_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ofNat_478_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_479_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_480_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_481_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_482_: *mut LeanObject = core::ptr::null_mut();
    v_natCast_477_ = lean_ctor_get(v_inst_475_, 2);
    lean_inc(v_natCast_477_);
    v_ofNat_478_ = lean_ctor_get(v_inst_475_, 3);
    lean_inc(v_ofNat_478_);
    lean_dec_ref(v_inst_475_);
    v___x_479_ = lean_apply_1(v_natCast_477_, v_n_476_);
    v___x_480_ = lean_unsigned_to_nat(0);
    v___x_481_ = lean_apply_1(v_ofNat_478_, v___x_480_);
    v___x_482_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_482_, 0, v___x_479_);
    lean_ctor_set(v___x_482_, 1, v___x_481_);
    return v___x_482_;
}
pub unsafe fn l_Lean_Grind_Ring_OfSemiring_natCast(
    mut v_00_u03b1_483_: *mut LeanObject,
    mut v_inst_484_: *mut LeanObject,
    mut v_n_485_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_486_: *mut LeanObject = core::ptr::null_mut();
    v___x_486_ = l_Lean_Grind_Ring_OfSemiring_natCast___redArg(v_inst_484_, v_n_485_);
    return v___x_486_;
}
pub unsafe fn _init_l_Lean_Grind_Ring_OfSemiring_intCast___redArg___closed__0() -> *mut LeanObject {
    let mut v___x_487_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_488_: *mut LeanObject = core::ptr::null_mut();
    v___x_487_ = lean_unsigned_to_nat(0);
    v___x_488_ = lean_nat_to_int(v___x_487_);
    return v___x_488_;
}
pub unsafe fn l_Lean_Grind_Ring_OfSemiring_intCast___redArg(
    mut v_inst_489_: *mut LeanObject,
    mut v_n_490_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_491_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_492_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_493_: u8 = 0;
    v___x_491_ = lean_unsigned_to_nat(0);
    v___x_492_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Grind_Ring_OfSemiring_intCast___redArg___closed__0),
        core::ptr::addr_of_mut!(l_Lean_Grind_Ring_OfSemiring_intCast___redArg___closed__0_once),
        _init_l_Lean_Grind_Ring_OfSemiring_intCast___redArg___closed__0,
    );
    v___x_493_ = lean_int_dec_lt(v_n_490_, v___x_492_);
    if v___x_493_ == 0 {
        let mut v_natCast_494_: *mut LeanObject = core::ptr::null_mut();
        let mut v_ofNat_495_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_496_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_497_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_498_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_499_: *mut LeanObject = core::ptr::null_mut();
        v_natCast_494_ = lean_ctor_get(v_inst_489_, 2);
        lean_inc(v_natCast_494_);
        v_ofNat_495_ = lean_ctor_get(v_inst_489_, 3);
        lean_inc(v_ofNat_495_);
        lean_dec_ref(v_inst_489_);
        v___x_496_ = lean_nat_abs(v_n_490_);
        v___x_497_ = lean_apply_1(v_natCast_494_, v___x_496_);
        v___x_498_ = lean_apply_1(v_ofNat_495_, v___x_491_);
        v___x_499_ = lean_alloc_ctor(0, 2, (0) as u32);
        lean_ctor_set(v___x_499_, 0, v___x_497_);
        lean_ctor_set(v___x_499_, 1, v___x_498_);
        return v___x_499_;
    } else {
        let mut v_natCast_500_: *mut LeanObject = core::ptr::null_mut();
        let mut v_ofNat_501_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_502_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_503_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_504_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_505_: *mut LeanObject = core::ptr::null_mut();
        v_natCast_500_ = lean_ctor_get(v_inst_489_, 2);
        lean_inc(v_natCast_500_);
        v_ofNat_501_ = lean_ctor_get(v_inst_489_, 3);
        lean_inc(v_ofNat_501_);
        lean_dec_ref(v_inst_489_);
        v___x_502_ = lean_apply_1(v_ofNat_501_, v___x_491_);
        v___x_503_ = lean_nat_abs(v_n_490_);
        v___x_504_ = lean_apply_1(v_natCast_500_, v___x_503_);
        v___x_505_ = lean_alloc_ctor(0, 2, (0) as u32);
        lean_ctor_set(v___x_505_, 0, v___x_502_);
        lean_ctor_set(v___x_505_, 1, v___x_504_);
        return v___x_505_;
    }
}
pub unsafe fn l_Lean_Grind_Ring_OfSemiring_intCast___redArg___boxed(
    mut v_inst_506_: *mut LeanObject,
    mut v_n_507_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_508_: *mut LeanObject = core::ptr::null_mut();
    v_res_508_ = l_Lean_Grind_Ring_OfSemiring_intCast___redArg(v_inst_506_, v_n_507_);
    lean_dec(v_n_507_);
    return v_res_508_;
}
pub unsafe fn l_Lean_Grind_Ring_OfSemiring_intCast(
    mut v_00_u03b1_509_: *mut LeanObject,
    mut v_inst_510_: *mut LeanObject,
    mut v_n_511_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_512_: *mut LeanObject = core::ptr::null_mut();
    v___x_512_ = l_Lean_Grind_Ring_OfSemiring_intCast___redArg(v_inst_510_, v_n_511_);
    return v___x_512_;
}
pub unsafe fn l_Lean_Grind_Ring_OfSemiring_intCast___boxed(
    mut v_00_u03b1_513_: *mut LeanObject,
    mut v_inst_514_: *mut LeanObject,
    mut v_n_515_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_516_: *mut LeanObject = core::ptr::null_mut();
    v_res_516_ = l_Lean_Grind_Ring_OfSemiring_intCast(v_00_u03b1_513_, v_inst_514_, v_n_515_);
    lean_dec(v_n_515_);
    return v_res_516_;
}
pub unsafe fn l_Lean_Grind_Ring_OfSemiring_sub___redArg(
    mut v_inst_517_: *mut LeanObject,
    mut v_q_u2081_518_: *mut LeanObject,
    mut v_q_u2082_519_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toAdd_520_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_521_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_522_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_523_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_524_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_526_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_527_: u8 = 0;
    let mut v___x_528_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_529_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_531_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_532_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_533_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_toAdd_520_ = lean_ctor_get(v_inst_517_, 0);
                lean_inc(v_toAdd_520_);
                lean_dec_ref(v_inst_517_);
                v_fst_521_ = lean_ctor_get(v_q_u2081_518_, 0);
                lean_inc(v_fst_521_);
                v_snd_522_ = lean_ctor_get(v_q_u2081_518_, 1);
                lean_inc(v_snd_522_);
                lean_dec(v_q_u2081_518_);
                v_fst_523_ = lean_ctor_get(v_q_u2082_519_, 0);
                v_snd_524_ = lean_ctor_get(v_q_u2082_519_, 1);
                v_isSharedCheck_533_ = (!lean_is_exclusive(v_q_u2082_519_)) as u8;
                if v_isSharedCheck_533_ == 0 {
                    v___x_526_ = v_q_u2082_519_;
                    v_isShared_527_ = v_isSharedCheck_533_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_snd_524_);
                    lean_inc(v_fst_523_);
                    lean_dec(v_q_u2082_519_);
                    v___x_526_ = lean_box(0);
                    v_isShared_527_ = v_isSharedCheck_533_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                lean_inc(v_toAdd_520_);
                v___x_528_ = lean_apply_2(v_toAdd_520_, v_fst_521_, v_snd_524_);
                v___x_529_ = lean_apply_2(v_toAdd_520_, v_fst_523_, v_snd_522_);
                if v_isShared_527_ == 0 {
                    lean_ctor_set(v___x_526_, 1, v___x_529_);
                    lean_ctor_set(v___x_526_, 0, v___x_528_);
                    v___x_531_ = v___x_526_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_532_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_532_, 0, v___x_528_);
                    lean_ctor_set(v_reuseFailAlloc_532_, 1, v___x_529_);
                    v___x_531_ = v_reuseFailAlloc_532_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_531_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Grind_Ring_OfSemiring_sub(
    mut v_00_u03b1_534_: *mut LeanObject,
    mut v_inst_535_: *mut LeanObject,
    mut v_q_u2081_536_: *mut LeanObject,
    mut v_q_u2082_537_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_538_: *mut LeanObject = core::ptr::null_mut();
    v___x_538_ =
        l_Lean_Grind_Ring_OfSemiring_sub___redArg(v_inst_535_, v_q_u2081_536_, v_q_u2082_537_);
    return v___x_538_;
}
pub unsafe fn l_Lean_Grind_Ring_OfSemiring_add___redArg(
    mut v_inst_539_: *mut LeanObject,
    mut v_q_u2081_540_: *mut LeanObject,
    mut v_q_u2082_541_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toAdd_542_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_543_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_544_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_545_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_546_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_548_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_549_: u8 = 0;
    let mut v___x_550_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_551_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_553_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_554_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_555_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_toAdd_542_ = lean_ctor_get(v_inst_539_, 0);
                lean_inc(v_toAdd_542_);
                lean_dec_ref(v_inst_539_);
                v_fst_543_ = lean_ctor_get(v_q_u2081_540_, 0);
                lean_inc(v_fst_543_);
                v_snd_544_ = lean_ctor_get(v_q_u2081_540_, 1);
                lean_inc(v_snd_544_);
                lean_dec(v_q_u2081_540_);
                v_fst_545_ = lean_ctor_get(v_q_u2082_541_, 0);
                v_snd_546_ = lean_ctor_get(v_q_u2082_541_, 1);
                v_isSharedCheck_555_ = (!lean_is_exclusive(v_q_u2082_541_)) as u8;
                if v_isSharedCheck_555_ == 0 {
                    v___x_548_ = v_q_u2082_541_;
                    v_isShared_549_ = v_isSharedCheck_555_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_snd_546_);
                    lean_inc(v_fst_545_);
                    lean_dec(v_q_u2082_541_);
                    v___x_548_ = lean_box(0);
                    v_isShared_549_ = v_isSharedCheck_555_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                lean_inc(v_toAdd_542_);
                v___x_550_ = lean_apply_2(v_toAdd_542_, v_fst_543_, v_fst_545_);
                v___x_551_ = lean_apply_2(v_toAdd_542_, v_snd_544_, v_snd_546_);
                if v_isShared_549_ == 0 {
                    lean_ctor_set(v___x_548_, 1, v___x_551_);
                    lean_ctor_set(v___x_548_, 0, v___x_550_);
                    v___x_553_ = v___x_548_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_554_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_554_, 0, v___x_550_);
                    lean_ctor_set(v_reuseFailAlloc_554_, 1, v___x_551_);
                    v___x_553_ = v_reuseFailAlloc_554_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_553_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Grind_Ring_OfSemiring_add(
    mut v_00_u03b1_556_: *mut LeanObject,
    mut v_inst_557_: *mut LeanObject,
    mut v_q_u2081_558_: *mut LeanObject,
    mut v_q_u2082_559_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_560_: *mut LeanObject = core::ptr::null_mut();
    v___x_560_ =
        l_Lean_Grind_Ring_OfSemiring_add___redArg(v_inst_557_, v_q_u2081_558_, v_q_u2082_559_);
    return v___x_560_;
}
pub unsafe fn l_Lean_Grind_Ring_OfSemiring_mul___redArg(
    mut v_inst_561_: *mut LeanObject,
    mut v_q_u2081_562_: *mut LeanObject,
    mut v_q_u2082_563_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toAdd_564_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toMul_565_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_566_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_567_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_568_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_569_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_571_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_572_: u8 = 0;
    let mut v___x_573_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_574_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_575_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_576_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_577_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_578_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_580_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_581_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_582_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_toAdd_564_ = lean_ctor_get(v_inst_561_, 0);
                lean_inc(v_toAdd_564_);
                v_toMul_565_ = lean_ctor_get(v_inst_561_, 1);
                lean_inc(v_toMul_565_);
                lean_dec_ref(v_inst_561_);
                v_fst_566_ = lean_ctor_get(v_q_u2081_562_, 0);
                lean_inc(v_fst_566_);
                v_snd_567_ = lean_ctor_get(v_q_u2081_562_, 1);
                lean_inc(v_snd_567_);
                lean_dec(v_q_u2081_562_);
                v_fst_568_ = lean_ctor_get(v_q_u2082_563_, 0);
                v_snd_569_ = lean_ctor_get(v_q_u2082_563_, 1);
                v_isSharedCheck_582_ = (!lean_is_exclusive(v_q_u2082_563_)) as u8;
                if v_isSharedCheck_582_ == 0 {
                    v___x_571_ = v_q_u2082_563_;
                    v_isShared_572_ = v_isSharedCheck_582_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_snd_569_);
                    lean_inc(v_fst_568_);
                    lean_dec(v_q_u2082_563_);
                    v___x_571_ = lean_box(0);
                    v_isShared_572_ = v_isSharedCheck_582_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                lean_inc_n(v_toMul_565_, 3);
                lean_inc(v_fst_568_);
                lean_inc(v_fst_566_);
                v___x_573_ = lean_apply_2(v_toMul_565_, v_fst_566_, v_fst_568_);
                lean_inc(v_snd_569_);
                lean_inc(v_snd_567_);
                v___x_574_ = lean_apply_2(v_toMul_565_, v_snd_567_, v_snd_569_);
                lean_inc(v_toAdd_564_);
                v___x_575_ = lean_apply_2(v_toAdd_564_, v___x_573_, v___x_574_);
                v___x_576_ = lean_apply_2(v_toMul_565_, v_fst_566_, v_snd_569_);
                v___x_577_ = lean_apply_2(v_toMul_565_, v_snd_567_, v_fst_568_);
                v___x_578_ = lean_apply_2(v_toAdd_564_, v___x_576_, v___x_577_);
                if v_isShared_572_ == 0 {
                    lean_ctor_set(v___x_571_, 1, v___x_578_);
                    lean_ctor_set(v___x_571_, 0, v___x_575_);
                    v___x_580_ = v___x_571_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_581_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_581_, 0, v___x_575_);
                    lean_ctor_set(v_reuseFailAlloc_581_, 1, v___x_578_);
                    v___x_580_ = v_reuseFailAlloc_581_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_580_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Grind_Ring_OfSemiring_mul(
    mut v_00_u03b1_583_: *mut LeanObject,
    mut v_inst_584_: *mut LeanObject,
    mut v_q_u2081_585_: *mut LeanObject,
    mut v_q_u2082_586_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_587_: *mut LeanObject = core::ptr::null_mut();
    v___x_587_ =
        l_Lean_Grind_Ring_OfSemiring_mul___redArg(v_inst_584_, v_q_u2081_585_, v_q_u2082_586_);
    return v___x_587_;
}
pub unsafe fn l_Lean_Grind_Ring_OfSemiring_neg___redArg(
    mut v_q_588_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_fst_589_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_590_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_592_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_593_: u8 = 0;
    let mut v___x_595_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_596_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_597_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_fst_589_ = lean_ctor_get(v_q_588_, 0);
                v_snd_590_ = lean_ctor_get(v_q_588_, 1);
                v_isSharedCheck_597_ = (!lean_is_exclusive(v_q_588_)) as u8;
                if v_isSharedCheck_597_ == 0 {
                    v___x_592_ = v_q_588_;
                    v_isShared_593_ = v_isSharedCheck_597_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_snd_590_);
                    lean_inc(v_fst_589_);
                    lean_dec(v_q_588_);
                    v___x_592_ = lean_box(0);
                    v_isShared_593_ = v_isSharedCheck_597_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                if v_isShared_593_ == 0 {
                    lean_ctor_set(v___x_592_, 1, v_fst_589_);
                    lean_ctor_set(v___x_592_, 0, v_snd_590_);
                    v___x_595_ = v___x_592_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_596_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_596_, 0, v_snd_590_);
                    lean_ctor_set(v_reuseFailAlloc_596_, 1, v_fst_589_);
                    v___x_595_ = v_reuseFailAlloc_596_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_595_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Grind_Ring_OfSemiring_neg(
    mut v_00_u03b1_598_: *mut LeanObject,
    mut v_inst_599_: *mut LeanObject,
    mut v_q_600_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_601_: *mut LeanObject = core::ptr::null_mut();
    v___x_601_ = l_Lean_Grind_Ring_OfSemiring_neg___redArg(v_q_600_);
    return v___x_601_;
}
pub unsafe fn l_Lean_Grind_Ring_OfSemiring_neg___boxed(
    mut v_00_u03b1_602_: *mut LeanObject,
    mut v_inst_603_: *mut LeanObject,
    mut v_q_604_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_605_: *mut LeanObject = core::ptr::null_mut();
    v_res_605_ = l_Lean_Grind_Ring_OfSemiring_neg(v_00_u03b1_602_, v_inst_603_, v_q_604_);
    lean_dec_ref(v_inst_603_);
    return v_res_605_;
}
pub unsafe fn l_Lean_Grind_Ring_OfSemiring_npow___redArg(
    mut v_inst_606_: *mut LeanObject,
    mut v_a_607_: *mut LeanObject,
    mut v_n_608_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_zero_609_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isZero_610_: u8 = 0;
    v_zero_609_ = lean_unsigned_to_nat(0);
    v_isZero_610_ = lean_nat_dec_eq(v_n_608_, v_zero_609_);
    if v_isZero_610_ == 1 {
        let mut v___x_611_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_612_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_a_607_);
        v___x_611_ = lean_unsigned_to_nat(1);
        v___x_612_ = l_Lean_Grind_Ring_OfSemiring_natCast___redArg(v_inst_606_, v___x_611_);
        return v___x_612_;
    } else {
        let mut v_one_613_: *mut LeanObject = core::ptr::null_mut();
        let mut v_n_614_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_615_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_616_: *mut LeanObject = core::ptr::null_mut();
        v_one_613_ = lean_unsigned_to_nat(1);
        v_n_614_ = lean_nat_sub(v_n_608_, v_one_613_);
        lean_inc(v_a_607_);
        lean_inc_ref(v_inst_606_);
        v___x_615_ = l_Lean_Grind_Ring_OfSemiring_npow___redArg(v_inst_606_, v_a_607_, v_n_614_);
        lean_dec(v_n_614_);
        v___x_616_ = l_Lean_Grind_Ring_OfSemiring_mul___redArg(v_inst_606_, v___x_615_, v_a_607_);
        return v___x_616_;
    }
}
pub unsafe fn l_Lean_Grind_Ring_OfSemiring_npow___redArg___boxed(
    mut v_inst_617_: *mut LeanObject,
    mut v_a_618_: *mut LeanObject,
    mut v_n_619_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_620_: *mut LeanObject = core::ptr::null_mut();
    v_res_620_ = l_Lean_Grind_Ring_OfSemiring_npow___redArg(v_inst_617_, v_a_618_, v_n_619_);
    lean_dec(v_n_619_);
    return v_res_620_;
}
pub unsafe fn l_Lean_Grind_Ring_OfSemiring_npow(
    mut v_00_u03b1_621_: *mut LeanObject,
    mut v_inst_622_: *mut LeanObject,
    mut v_a_623_: *mut LeanObject,
    mut v_n_624_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_625_: *mut LeanObject = core::ptr::null_mut();
    v___x_625_ = l_Lean_Grind_Ring_OfSemiring_npow___redArg(v_inst_622_, v_a_623_, v_n_624_);
    return v___x_625_;
}
pub unsafe fn l_Lean_Grind_Ring_OfSemiring_npow___boxed(
    mut v_00_u03b1_626_: *mut LeanObject,
    mut v_inst_627_: *mut LeanObject,
    mut v_a_628_: *mut LeanObject,
    mut v_n_629_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_630_: *mut LeanObject = core::ptr::null_mut();
    v_res_630_ =
        l_Lean_Grind_Ring_OfSemiring_npow(v_00_u03b1_626_, v_inst_627_, v_a_628_, v_n_629_);
    lean_dec(v_n_629_);
    return v_res_630_;
}
pub unsafe fn l_Lean_Grind_Ring_OfSemiring_nsmul___redArg(
    mut v_inst_631_: *mut LeanObject,
    mut v_n_632_: *mut LeanObject,
    mut v_a_633_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_634_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_635_: *mut LeanObject = core::ptr::null_mut();
    lean_inc_ref(v_inst_631_);
    v___x_634_ = l_Lean_Grind_Ring_OfSemiring_natCast___redArg(v_inst_631_, v_n_632_);
    v___x_635_ = l_Lean_Grind_Ring_OfSemiring_mul___redArg(v_inst_631_, v___x_634_, v_a_633_);
    return v___x_635_;
}
pub unsafe fn l_Lean_Grind_Ring_OfSemiring_nsmul(
    mut v_00_u03b1_636_: *mut LeanObject,
    mut v_inst_637_: *mut LeanObject,
    mut v_n_638_: *mut LeanObject,
    mut v_a_639_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_640_: *mut LeanObject = core::ptr::null_mut();
    v___x_640_ = l_Lean_Grind_Ring_OfSemiring_nsmul___redArg(v_inst_637_, v_n_638_, v_a_639_);
    return v___x_640_;
}
pub unsafe fn l_Lean_Grind_Ring_OfSemiring_zsmul___redArg(
    mut v_inst_641_: *mut LeanObject,
    mut v_i_642_: *mut LeanObject,
    mut v_a_643_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_644_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_645_: *mut LeanObject = core::ptr::null_mut();
    lean_inc_ref(v_inst_641_);
    v___x_644_ = l_Lean_Grind_Ring_OfSemiring_intCast___redArg(v_inst_641_, v_i_642_);
    v___x_645_ = l_Lean_Grind_Ring_OfSemiring_mul___redArg(v_inst_641_, v___x_644_, v_a_643_);
    return v___x_645_;
}
pub unsafe fn l_Lean_Grind_Ring_OfSemiring_zsmul___redArg___boxed(
    mut v_inst_646_: *mut LeanObject,
    mut v_i_647_: *mut LeanObject,
    mut v_a_648_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_649_: *mut LeanObject = core::ptr::null_mut();
    v_res_649_ = l_Lean_Grind_Ring_OfSemiring_zsmul___redArg(v_inst_646_, v_i_647_, v_a_648_);
    lean_dec(v_i_647_);
    return v_res_649_;
}
pub unsafe fn l_Lean_Grind_Ring_OfSemiring_zsmul(
    mut v_00_u03b1_650_: *mut LeanObject,
    mut v_inst_651_: *mut LeanObject,
    mut v_i_652_: *mut LeanObject,
    mut v_a_653_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_654_: *mut LeanObject = core::ptr::null_mut();
    v___x_654_ = l_Lean_Grind_Ring_OfSemiring_zsmul___redArg(v_inst_651_, v_i_652_, v_a_653_);
    return v___x_654_;
}
pub unsafe fn l_Lean_Grind_Ring_OfSemiring_zsmul___boxed(
    mut v_00_u03b1_655_: *mut LeanObject,
    mut v_inst_656_: *mut LeanObject,
    mut v_i_657_: *mut LeanObject,
    mut v_a_658_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_659_: *mut LeanObject = core::ptr::null_mut();
    v_res_659_ =
        l_Lean_Grind_Ring_OfSemiring_zsmul(v_00_u03b1_655_, v_inst_656_, v_i_657_, v_a_658_);
    lean_dec(v_i_657_);
    return v_res_659_;
}
pub unsafe fn l_Lean_Grind_Ring_OfSemiring_ofSemiring___redArg___lam__0(
    mut v_inst_660_: *mut LeanObject,
    mut v_n_661_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_662_: *mut LeanObject = core::ptr::null_mut();
    v___x_662_ = l_Lean_Grind_Ring_OfSemiring_natCast___redArg(v_inst_660_, v_n_661_);
    return v___x_662_;
}
pub unsafe fn l_Lean_Grind_Ring_OfSemiring_ofSemiring___redArg(
    mut v_inst_663_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_664_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_665_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_666_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_667_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_668_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_669_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_670_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_671_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_672_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_673_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_674_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_675_: *mut LeanObject = core::ptr::null_mut();
    lean_inc_ref_n(v_inst_663_, 9);
    v___f_664_ = lean_alloc_closure(
        l_Lean_Grind_Ring_OfSemiring_ofSemiring___redArg___lam__0 as *mut core::ffi::c_void,
        2,
        1,
    );
    lean_closure_set(v___f_664_, 0, v_inst_663_);
    v___x_665_ = lean_alloc_closure(
        l_Lean_Grind_Ring_OfSemiring_add as *mut core::ffi::c_void,
        4,
        2,
    );
    lean_closure_set(v___x_665_, 0, lean_box(0));
    lean_closure_set(v___x_665_, 1, v_inst_663_);
    v___x_666_ = lean_alloc_closure(
        l_Lean_Grind_Ring_OfSemiring_mul as *mut core::ffi::c_void,
        4,
        2,
    );
    lean_closure_set(v___x_666_, 0, lean_box(0));
    lean_closure_set(v___x_666_, 1, v_inst_663_);
    v___x_667_ = lean_alloc_closure(
        l_Lean_Grind_Ring_OfSemiring_natCast as *mut core::ffi::c_void,
        3,
        2,
    );
    lean_closure_set(v___x_667_, 0, lean_box(0));
    lean_closure_set(v___x_667_, 1, v_inst_663_);
    v___x_668_ = lean_alloc_closure(
        l_Lean_Grind_Ring_OfSemiring_nsmul as *mut core::ffi::c_void,
        4,
        2,
    );
    lean_closure_set(v___x_668_, 0, lean_box(0));
    lean_closure_set(v___x_668_, 1, v_inst_663_);
    v___x_669_ = lean_alloc_closure(
        l_Lean_Grind_Ring_OfSemiring_npow___boxed as *mut core::ffi::c_void,
        4,
        2,
    );
    lean_closure_set(v___x_669_, 0, lean_box(0));
    lean_closure_set(v___x_669_, 1, v_inst_663_);
    v___x_670_ = lean_alloc_ctor(0, 6, (0) as u32);
    lean_ctor_set(v___x_670_, 0, v___x_665_);
    lean_ctor_set(v___x_670_, 1, v___x_666_);
    lean_ctor_set(v___x_670_, 2, v___x_667_);
    lean_ctor_set(v___x_670_, 3, v___f_664_);
    lean_ctor_set(v___x_670_, 4, v___x_668_);
    lean_ctor_set(v___x_670_, 5, v___x_669_);
    v___x_671_ = lean_alloc_closure(
        l_Lean_Grind_Ring_OfSemiring_neg___boxed as *mut core::ffi::c_void,
        3,
        2,
    );
    lean_closure_set(v___x_671_, 0, lean_box(0));
    lean_closure_set(v___x_671_, 1, v_inst_663_);
    v___x_672_ = lean_alloc_closure(
        l_Lean_Grind_Ring_OfSemiring_sub as *mut core::ffi::c_void,
        4,
        2,
    );
    lean_closure_set(v___x_672_, 0, lean_box(0));
    lean_closure_set(v___x_672_, 1, v_inst_663_);
    v___x_673_ = lean_alloc_closure(
        l_Lean_Grind_Ring_OfSemiring_intCast___boxed as *mut core::ffi::c_void,
        3,
        2,
    );
    lean_closure_set(v___x_673_, 0, lean_box(0));
    lean_closure_set(v___x_673_, 1, v_inst_663_);
    v___x_674_ = lean_alloc_closure(
        l_Lean_Grind_Ring_OfSemiring_zsmul___boxed as *mut core::ffi::c_void,
        4,
        2,
    );
    lean_closure_set(v___x_674_, 0, lean_box(0));
    lean_closure_set(v___x_674_, 1, v_inst_663_);
    v___x_675_ = lean_alloc_ctor(0, 5, (0) as u32);
    lean_ctor_set(v___x_675_, 0, v___x_670_);
    lean_ctor_set(v___x_675_, 1, v___x_671_);
    lean_ctor_set(v___x_675_, 2, v___x_672_);
    lean_ctor_set(v___x_675_, 3, v___x_673_);
    lean_ctor_set(v___x_675_, 4, v___x_674_);
    return v___x_675_;
}
pub unsafe fn l_Lean_Grind_Ring_OfSemiring_ofSemiring(
    mut v_00_u03b1_676_: *mut LeanObject,
    mut v_inst_677_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_678_: *mut LeanObject = core::ptr::null_mut();
    v___x_678_ = l_Lean_Grind_Ring_OfSemiring_ofSemiring___redArg(v_inst_677_);
    return v___x_678_;
}
pub unsafe fn l_Lean_Grind_Ring_OfSemiring_toQ___redArg(
    mut v_inst_679_: *mut LeanObject,
    mut v_a_680_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_ofNat_681_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_682_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_683_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_684_: *mut LeanObject = core::ptr::null_mut();
    v_ofNat_681_ = lean_ctor_get(v_inst_679_, 3);
    lean_inc(v_ofNat_681_);
    lean_dec_ref(v_inst_679_);
    v___x_682_ = lean_unsigned_to_nat(0);
    v___x_683_ = lean_apply_1(v_ofNat_681_, v___x_682_);
    v___x_684_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_684_, 0, v_a_680_);
    lean_ctor_set(v___x_684_, 1, v___x_683_);
    return v___x_684_;
}
pub unsafe fn l_Lean_Grind_Ring_OfSemiring_toQ(
    mut v_00_u03b1_685_: *mut LeanObject,
    mut v_inst_686_: *mut LeanObject,
    mut v_a_687_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_688_: *mut LeanObject = core::ptr::null_mut();
    v___x_688_ = l_Lean_Grind_Ring_OfSemiring_toQ___redArg(v_inst_686_, v_a_687_);
    return v___x_688_;
}
pub unsafe fn l_Lean_Grind_Ring_OfSemiring_instLEQOfOrderedAdd(
    mut v_00_u03b1_689_: *mut LeanObject,
    mut v_inst_690_: *mut LeanObject,
    mut v_inst_691_: *mut LeanObject,
    mut v_inst_692_: *mut LeanObject,
    mut v_inst_693_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_694_: *mut LeanObject = core::ptr::null_mut();
    v___x_694_ = lean_box(0);
    return v___x_694_;
}
pub unsafe fn l_Lean_Grind_Ring_OfSemiring_instLEQOfOrderedAdd___boxed(
    mut v_00_u03b1_695_: *mut LeanObject,
    mut v_inst_696_: *mut LeanObject,
    mut v_inst_697_: *mut LeanObject,
    mut v_inst_698_: *mut LeanObject,
    mut v_inst_699_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_700_: *mut LeanObject = core::ptr::null_mut();
    v_res_700_ = l_Lean_Grind_Ring_OfSemiring_instLEQOfOrderedAdd(
        v_00_u03b1_695_,
        v_inst_696_,
        v_inst_697_,
        v_inst_698_,
        v_inst_699_,
    );
    lean_dec_ref(v_inst_696_);
    return v_res_700_;
}
pub unsafe fn l_Lean_Grind_Ring_OfSemiring_instLTQOfOrderedAdd(
    mut v_00_u03b1_701_: *mut LeanObject,
    mut v_inst_702_: *mut LeanObject,
    mut v_inst_703_: *mut LeanObject,
    mut v_inst_704_: *mut LeanObject,
    mut v_inst_705_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_706_: *mut LeanObject = core::ptr::null_mut();
    v___x_706_ = lean_box(0);
    return v___x_706_;
}
pub unsafe fn l_Lean_Grind_Ring_OfSemiring_instLTQOfOrderedAdd___boxed(
    mut v_00_u03b1_707_: *mut LeanObject,
    mut v_inst_708_: *mut LeanObject,
    mut v_inst_709_: *mut LeanObject,
    mut v_inst_710_: *mut LeanObject,
    mut v_inst_711_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_712_: *mut LeanObject = core::ptr::null_mut();
    v_res_712_ = l_Lean_Grind_Ring_OfSemiring_instLTQOfOrderedAdd(
        v_00_u03b1_707_,
        v_inst_708_,
        v_inst_709_,
        v_inst_710_,
        v_inst_711_,
    );
    lean_dec_ref(v_inst_708_);
    return v_res_712_;
}
pub unsafe fn l_Lean_Grind_CommRing_OfCommSemiring_ofCommSemiring___redArg(
    mut v_inst_713_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_714_: *mut LeanObject = core::ptr::null_mut();
    v___x_714_ = l_Lean_Grind_Ring_OfSemiring_ofSemiring___redArg(v_inst_713_);
    return v___x_714_;
}
pub unsafe fn l_Lean_Grind_CommRing_OfCommSemiring_ofCommSemiring(
    mut v_00_u03b1_715_: *mut LeanObject,
    mut v_inst_716_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_717_: *mut LeanObject = core::ptr::null_mut();
    v___x_717_ = l_Lean_Grind_Ring_OfSemiring_ofSemiring___redArg(v_inst_716_);
    return v___x_717_;
}
pub unsafe fn l_Lean_Grind_CommRing_OfCommSemiring_instAddQ___redArg(
    mut v_inst_718_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toSemiring_719_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toAdd_720_: *mut LeanObject = core::ptr::null_mut();
    v_toSemiring_719_ = lean_ctor_get(v_inst_718_, 0);
    v_toAdd_720_ = lean_ctor_get(v_toSemiring_719_, 0);
    lean_inc(v_toAdd_720_);
    return v_toAdd_720_;
}
pub unsafe fn l_Lean_Grind_CommRing_OfCommSemiring_instAddQ___redArg___boxed(
    mut v_inst_721_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_722_: *mut LeanObject = core::ptr::null_mut();
    v_res_722_ = l_Lean_Grind_CommRing_OfCommSemiring_instAddQ___redArg(v_inst_721_);
    lean_dec_ref(v_inst_721_);
    return v_res_722_;
}
pub unsafe fn l_Lean_Grind_CommRing_OfCommSemiring_instAddQ(
    mut v_00_u03b1_723_: *mut LeanObject,
    mut v_inst_724_: *mut LeanObject,
    mut v_inst_725_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_726_: *mut LeanObject = core::ptr::null_mut();
    v___x_726_ = l_Lean_Grind_CommRing_OfCommSemiring_instAddQ___redArg(v_inst_725_);
    return v___x_726_;
}
pub unsafe fn l_Lean_Grind_CommRing_OfCommSemiring_instAddQ___boxed(
    mut v_00_u03b1_727_: *mut LeanObject,
    mut v_inst_728_: *mut LeanObject,
    mut v_inst_729_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_730_: *mut LeanObject = core::ptr::null_mut();
    v_res_730_ =
        l_Lean_Grind_CommRing_OfCommSemiring_instAddQ(v_00_u03b1_727_, v_inst_728_, v_inst_729_);
    lean_dec_ref(v_inst_729_);
    lean_dec_ref(v_inst_728_);
    return v_res_730_;
}
pub unsafe fn l_Lean_Grind_CommRing_OfCommSemiring_instSubQ___redArg(
    mut v_inst_731_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_732_: *mut LeanObject = core::ptr::null_mut();
    v___x_732_ = lean_alloc_closure(
        l_Lean_Grind_Ring_OfSemiring_sub as *mut core::ffi::c_void,
        4,
        2,
    );
    lean_closure_set(v___x_732_, 0, lean_box(0));
    lean_closure_set(v___x_732_, 1, v_inst_731_);
    return v___x_732_;
}
pub unsafe fn l_Lean_Grind_CommRing_OfCommSemiring_instSubQ(
    mut v_00_u03b1_733_: *mut LeanObject,
    mut v_inst_734_: *mut LeanObject,
    mut v_inst_735_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_736_: *mut LeanObject = core::ptr::null_mut();
    v___x_736_ = lean_alloc_closure(
        l_Lean_Grind_Ring_OfSemiring_sub as *mut core::ffi::c_void,
        4,
        2,
    );
    lean_closure_set(v___x_736_, 0, lean_box(0));
    lean_closure_set(v___x_736_, 1, v_inst_734_);
    return v___x_736_;
}
pub unsafe fn l_Lean_Grind_CommRing_OfCommSemiring_instSubQ___boxed(
    mut v_00_u03b1_737_: *mut LeanObject,
    mut v_inst_738_: *mut LeanObject,
    mut v_inst_739_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_740_: *mut LeanObject = core::ptr::null_mut();
    v_res_740_ =
        l_Lean_Grind_CommRing_OfCommSemiring_instSubQ(v_00_u03b1_737_, v_inst_738_, v_inst_739_);
    lean_dec_ref(v_inst_739_);
    return v_res_740_;
}
pub unsafe fn l_Lean_Grind_CommRing_OfCommSemiring_instMulQ___redArg(
    mut v_inst_741_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toSemiring_742_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toMul_743_: *mut LeanObject = core::ptr::null_mut();
    v_toSemiring_742_ = lean_ctor_get(v_inst_741_, 0);
    v_toMul_743_ = lean_ctor_get(v_toSemiring_742_, 1);
    lean_inc(v_toMul_743_);
    return v_toMul_743_;
}
pub unsafe fn l_Lean_Grind_CommRing_OfCommSemiring_instMulQ___redArg___boxed(
    mut v_inst_744_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_745_: *mut LeanObject = core::ptr::null_mut();
    v_res_745_ = l_Lean_Grind_CommRing_OfCommSemiring_instMulQ___redArg(v_inst_744_);
    lean_dec_ref(v_inst_744_);
    return v_res_745_;
}
pub unsafe fn l_Lean_Grind_CommRing_OfCommSemiring_instMulQ(
    mut v_00_u03b1_746_: *mut LeanObject,
    mut v_inst_747_: *mut LeanObject,
    mut v_inst_748_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_749_: *mut LeanObject = core::ptr::null_mut();
    v___x_749_ = l_Lean_Grind_CommRing_OfCommSemiring_instMulQ___redArg(v_inst_748_);
    return v___x_749_;
}
pub unsafe fn l_Lean_Grind_CommRing_OfCommSemiring_instMulQ___boxed(
    mut v_00_u03b1_750_: *mut LeanObject,
    mut v_inst_751_: *mut LeanObject,
    mut v_inst_752_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_753_: *mut LeanObject = core::ptr::null_mut();
    v_res_753_ =
        l_Lean_Grind_CommRing_OfCommSemiring_instMulQ(v_00_u03b1_750_, v_inst_751_, v_inst_752_);
    lean_dec_ref(v_inst_752_);
    lean_dec_ref(v_inst_751_);
    return v_res_753_;
}
pub unsafe fn l_Lean_Grind_CommRing_OfCommSemiring_instNegQ___redArg(
    mut v_inst_754_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_755_: *mut LeanObject = core::ptr::null_mut();
    v___x_755_ = lean_alloc_closure(
        l_Lean_Grind_Ring_OfSemiring_neg___boxed as *mut core::ffi::c_void,
        3,
        2,
    );
    lean_closure_set(v___x_755_, 0, lean_box(0));
    lean_closure_set(v___x_755_, 1, v_inst_754_);
    return v___x_755_;
}
pub unsafe fn l_Lean_Grind_CommRing_OfCommSemiring_instNegQ(
    mut v_00_u03b1_756_: *mut LeanObject,
    mut v_inst_757_: *mut LeanObject,
    mut v_inst_758_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_759_: *mut LeanObject = core::ptr::null_mut();
    v___x_759_ = lean_alloc_closure(
        l_Lean_Grind_Ring_OfSemiring_neg___boxed as *mut core::ffi::c_void,
        3,
        2,
    );
    lean_closure_set(v___x_759_, 0, lean_box(0));
    lean_closure_set(v___x_759_, 1, v_inst_757_);
    return v___x_759_;
}
pub unsafe fn l_Lean_Grind_CommRing_OfCommSemiring_instNegQ___boxed(
    mut v_00_u03b1_760_: *mut LeanObject,
    mut v_inst_761_: *mut LeanObject,
    mut v_inst_762_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_763_: *mut LeanObject = core::ptr::null_mut();
    v_res_763_ =
        l_Lean_Grind_CommRing_OfCommSemiring_instNegQ(v_00_u03b1_760_, v_inst_761_, v_inst_762_);
    lean_dec_ref(v_inst_762_);
    return v_res_763_;
}
pub unsafe fn l_Lean_Grind_CommRing_OfCommSemiring_instOfNatQ___redArg(
    mut v_n_764_: *mut LeanObject,
    mut v_inst_765_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toSemiring_766_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ofNat_767_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_768_: *mut LeanObject = core::ptr::null_mut();
    v_toSemiring_766_ = lean_ctor_get(v_inst_765_, 0);
    lean_inc_ref(v_toSemiring_766_);
    lean_dec_ref(v_inst_765_);
    v_ofNat_767_ = lean_ctor_get(v_toSemiring_766_, 3);
    lean_inc(v_ofNat_767_);
    lean_dec_ref(v_toSemiring_766_);
    v___x_768_ = lean_apply_1(v_ofNat_767_, v_n_764_);
    return v___x_768_;
}
pub unsafe fn l_Lean_Grind_CommRing_OfCommSemiring_instOfNatQ(
    mut v_00_u03b1_769_: *mut LeanObject,
    mut v_inst_770_: *mut LeanObject,
    mut v_n_771_: *mut LeanObject,
    mut v_inst_772_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_773_: *mut LeanObject = core::ptr::null_mut();
    v___x_773_ = l_Lean_Grind_CommRing_OfCommSemiring_instOfNatQ___redArg(v_n_771_, v_inst_772_);
    return v___x_773_;
}
pub unsafe fn l_Lean_Grind_CommRing_OfCommSemiring_instOfNatQ___boxed(
    mut v_00_u03b1_774_: *mut LeanObject,
    mut v_inst_775_: *mut LeanObject,
    mut v_n_776_: *mut LeanObject,
    mut v_inst_777_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_778_: *mut LeanObject = core::ptr::null_mut();
    v_res_778_ = l_Lean_Grind_CommRing_OfCommSemiring_instOfNatQ(
        v_00_u03b1_774_,
        v_inst_775_,
        v_n_776_,
        v_inst_777_,
    );
    lean_dec_ref(v_inst_775_);
    return v_res_778_;
}
pub unsafe fn l_Lean_Grind_CommRing_OfCommSemiring_instNatCastQ___redArg(
    mut v_inst_779_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toSemiring_780_: *mut LeanObject = core::ptr::null_mut();
    let mut v_natCast_781_: *mut LeanObject = core::ptr::null_mut();
    v_toSemiring_780_ = lean_ctor_get(v_inst_779_, 0);
    v_natCast_781_ = lean_ctor_get(v_toSemiring_780_, 2);
    lean_inc(v_natCast_781_);
    return v_natCast_781_;
}
pub unsafe fn l_Lean_Grind_CommRing_OfCommSemiring_instNatCastQ___redArg___boxed(
    mut v_inst_782_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_783_: *mut LeanObject = core::ptr::null_mut();
    v_res_783_ = l_Lean_Grind_CommRing_OfCommSemiring_instNatCastQ___redArg(v_inst_782_);
    lean_dec_ref(v_inst_782_);
    return v_res_783_;
}
pub unsafe fn l_Lean_Grind_CommRing_OfCommSemiring_instNatCastQ(
    mut v_00_u03b1_784_: *mut LeanObject,
    mut v_inst_785_: *mut LeanObject,
    mut v_inst_786_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_787_: *mut LeanObject = core::ptr::null_mut();
    v___x_787_ = l_Lean_Grind_CommRing_OfCommSemiring_instNatCastQ___redArg(v_inst_786_);
    return v___x_787_;
}
pub unsafe fn l_Lean_Grind_CommRing_OfCommSemiring_instNatCastQ___boxed(
    mut v_00_u03b1_788_: *mut LeanObject,
    mut v_inst_789_: *mut LeanObject,
    mut v_inst_790_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_791_: *mut LeanObject = core::ptr::null_mut();
    v_res_791_ = l_Lean_Grind_CommRing_OfCommSemiring_instNatCastQ(
        v_00_u03b1_788_,
        v_inst_789_,
        v_inst_790_,
    );
    lean_dec_ref(v_inst_790_);
    lean_dec_ref(v_inst_789_);
    return v_res_791_;
}
pub unsafe fn l_Lean_Grind_CommRing_OfCommSemiring_instIntCastQ___redArg(
    mut v_inst_792_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_793_: *mut LeanObject = core::ptr::null_mut();
    v___x_793_ = lean_alloc_closure(
        l_Lean_Grind_Ring_OfSemiring_intCast___boxed as *mut core::ffi::c_void,
        3,
        2,
    );
    lean_closure_set(v___x_793_, 0, lean_box(0));
    lean_closure_set(v___x_793_, 1, v_inst_792_);
    return v___x_793_;
}
pub unsafe fn l_Lean_Grind_CommRing_OfCommSemiring_instIntCastQ(
    mut v_00_u03b1_794_: *mut LeanObject,
    mut v_inst_795_: *mut LeanObject,
    mut v_inst_796_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_797_: *mut LeanObject = core::ptr::null_mut();
    v___x_797_ = lean_alloc_closure(
        l_Lean_Grind_Ring_OfSemiring_intCast___boxed as *mut core::ffi::c_void,
        3,
        2,
    );
    lean_closure_set(v___x_797_, 0, lean_box(0));
    lean_closure_set(v___x_797_, 1, v_inst_795_);
    return v___x_797_;
}
pub unsafe fn l_Lean_Grind_CommRing_OfCommSemiring_instIntCastQ___boxed(
    mut v_00_u03b1_798_: *mut LeanObject,
    mut v_inst_799_: *mut LeanObject,
    mut v_inst_800_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_801_: *mut LeanObject = core::ptr::null_mut();
    v_res_801_ = l_Lean_Grind_CommRing_OfCommSemiring_instIntCastQ(
        v_00_u03b1_798_,
        v_inst_799_,
        v_inst_800_,
    );
    lean_dec_ref(v_inst_800_);
    return v_res_801_;
}
pub unsafe fn l_Lean_Grind_CommRing_OfCommSemiring_instHPowQNat___redArg(
    mut v_inst_802_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toSemiring_803_: *mut LeanObject = core::ptr::null_mut();
    let mut v_npow_804_: *mut LeanObject = core::ptr::null_mut();
    v_toSemiring_803_ = lean_ctor_get(v_inst_802_, 0);
    v_npow_804_ = lean_ctor_get(v_toSemiring_803_, 5);
    lean_inc(v_npow_804_);
    return v_npow_804_;
}
pub unsafe fn l_Lean_Grind_CommRing_OfCommSemiring_instHPowQNat___redArg___boxed(
    mut v_inst_805_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_806_: *mut LeanObject = core::ptr::null_mut();
    v_res_806_ = l_Lean_Grind_CommRing_OfCommSemiring_instHPowQNat___redArg(v_inst_805_);
    lean_dec_ref(v_inst_805_);
    return v_res_806_;
}
pub unsafe fn l_Lean_Grind_CommRing_OfCommSemiring_instHPowQNat(
    mut v_00_u03b1_807_: *mut LeanObject,
    mut v_inst_808_: *mut LeanObject,
    mut v_inst_809_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_810_: *mut LeanObject = core::ptr::null_mut();
    v___x_810_ = l_Lean_Grind_CommRing_OfCommSemiring_instHPowQNat___redArg(v_inst_809_);
    return v___x_810_;
}
pub unsafe fn l_Lean_Grind_CommRing_OfCommSemiring_instHPowQNat___boxed(
    mut v_00_u03b1_811_: *mut LeanObject,
    mut v_inst_812_: *mut LeanObject,
    mut v_inst_813_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_814_: *mut LeanObject = core::ptr::null_mut();
    v_res_814_ = l_Lean_Grind_CommRing_OfCommSemiring_instHPowQNat(
        v_00_u03b1_811_,
        v_inst_812_,
        v_inst_813_,
    );
    lean_dec_ref(v_inst_813_);
    lean_dec_ref(v_inst_812_);
    return v_res_814_;
}
pub unsafe fn l_Lean_Grind_CommRing_OfCommSemiring_toQUnexpander(
    mut v_stx_828_: *mut LeanObject,
    mut v_a_829_: *mut LeanObject,
    mut v_a_830_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_831_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_832_: u8 = 0;
    v___x_831_ = l_Lean_Grind_CommRing_OfCommSemiring_toQUnexpander___closed__4;
    lean_inc(v_stx_828_);
    v___x_832_ = l_Lean_Syntax_isOfKind(v_stx_828_, v___x_831_);
    if v___x_832_ == 0 {
        let mut v___x_833_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_834_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_stx_828_);
        v___x_833_ = lean_box(0);
        v___x_834_ = lean_alloc_ctor(1, 2, (0) as u32);
        lean_ctor_set(v___x_834_, 0, v___x_833_);
        lean_ctor_set(v___x_834_, 1, v_a_830_);
        return v___x_834_;
    } else {
        let mut v___x_835_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_836_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_837_: u8 = 0;
        v___x_835_ = lean_unsigned_to_nat(1);
        v___x_836_ = l_Lean_Syntax_getArg(v_stx_828_, v___x_835_);
        lean_dec(v_stx_828_);
        lean_inc(v___x_836_);
        v___x_837_ = l_Lean_Syntax_matchesNull(v___x_836_, v___x_835_);
        if v___x_837_ == 0 {
            let mut v___x_838_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_839_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v___x_836_);
            v___x_838_ = lean_box(0);
            v___x_839_ = lean_alloc_ctor(1, 2, (0) as u32);
            lean_ctor_set(v___x_839_, 0, v___x_838_);
            lean_ctor_set(v___x_839_, 1, v_a_830_);
            return v___x_839_;
        } else {
            let mut v___x_840_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_841_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_842_: u8 = 0;
            let mut v___x_843_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_844_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_845_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_846_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_847_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_848_: *mut LeanObject = core::ptr::null_mut();
            v___x_840_ = lean_unsigned_to_nat(0);
            v___x_841_ = l_Lean_Syntax_getArg(v___x_836_, v___x_840_);
            lean_dec(v___x_836_);
            v___x_842_ = 0;
            v___x_843_ = l_Lean_SourceInfo_fromRef(v_a_829_, v___x_842_);
            v___x_844_ = l_Lean_Grind_CommRing_OfCommSemiring_toQUnexpander___closed__6;
            v___x_845_ = l_Lean_Grind_CommRing_OfCommSemiring_toQUnexpander___closed__7;
            lean_inc(v___x_843_);
            v___x_846_ = lean_alloc_ctor(2, 2, (0) as u32);
            lean_ctor_set(v___x_846_, 0, v___x_843_);
            lean_ctor_set(v___x_846_, 1, v___x_845_);
            v___x_847_ = l_Lean_Syntax_node2(v___x_843_, v___x_844_, v___x_846_, v___x_841_);
            v___x_848_ = lean_alloc_ctor(0, 2, (0) as u32);
            lean_ctor_set(v___x_848_, 0, v___x_847_);
            lean_ctor_set(v___x_848_, 1, v_a_830_);
            return v___x_848_;
        }
    }
}
pub unsafe fn l_Lean_Grind_CommRing_OfCommSemiring_toQUnexpander___boxed(
    mut v_stx_849_: *mut LeanObject,
    mut v_a_850_: *mut LeanObject,
    mut v_a_851_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_852_: *mut LeanObject = core::ptr::null_mut();
    v_res_852_ = l_Lean_Grind_CommRing_OfCommSemiring_toQUnexpander(v_stx_849_, v_a_850_, v_a_851_);
    lean_dec(v_a_850_);
    return v_res_852_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Init_Grind_Ring_Envelope(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Init_Grind_Ordered_Ring(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_AC(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Omega(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_RCases(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Init_Grind_Ring_Envelope(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_meta_initialized = true;
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Init_Grind_Ring_Envelope(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Init_Grind_Ordered_Ring(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Data_AC(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Omega(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_RCases(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Grind_Ring_Envelope(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Init_Grind_Ring_Envelope(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Init_Grind_Ring_Envelope(builtin);
}
