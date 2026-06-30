// Lean compiler output
// Module: Init.Grind.Ring.Envelope
// Imports: Init.Grind.Ordered.Ring Init.Data.AC Init.Omega Init.RCases
use crate::ffi::{lean_int_dec_lt, lean_nat_abs, lean_nat_dec_eq, lean_nat_sub, lean_nat_to_int};
use crate::r#gen::Init::Data::AC::{initialize_Init_Data_AC, runtime_initialize_Init_Data_AC};
use crate::r#gen::Init::Grind::Ordered::Ring::{
    initialize_Init_Grind_Ordered_Ring, runtime_initialize_Init_Grind_Ordered_Ring,
};
use crate::r#gen::Init::Omega::{initialize_Init_Omega, runtime_initialize_Init_Omega};
use crate::r#gen::Init::Prelude::{
    l_Lean_SourceInfo_fromRef, l_Lean_Syntax_getArg, l_Lean_Syntax_isOfKind,
    l_Lean_Syntax_matchesNull, l_Lean_Syntax_node2,
};
use crate::r#gen::Init::RCases::{initialize_Init_RCases, runtime_initialize_Init_RCases};
static mut l_Lean_Grind_Ring_OfSemiring_intCast___redArg___closed__0_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Grind_Ring_OfSemiring_intCast___redArg___closed__0:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Grind_CommRing_OfCommSemiring_toQUnexpander___closed__0_value:
    leanh::LeanStringObject<5> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
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
static mut l_Lean_Grind_CommRing_OfCommSemiring_toQUnexpander___closed__0:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Grind_CommRing_OfCommSemiring_toQUnexpander___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Grind_CommRing_OfCommSemiring_toQUnexpander___closed__1_value:
    leanh::LeanStringObject<7> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
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
static mut l_Lean_Grind_CommRing_OfCommSemiring_toQUnexpander___closed__1:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Grind_CommRing_OfCommSemiring_toQUnexpander___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Grind_CommRing_OfCommSemiring_toQUnexpander___closed__2_value:
    leanh::LeanStringObject<5> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
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
static mut l_Lean_Grind_CommRing_OfCommSemiring_toQUnexpander___closed__2:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Grind_CommRing_OfCommSemiring_toQUnexpander___closed__2_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Grind_CommRing_OfCommSemiring_toQUnexpander___closed__3_value:
    leanh::LeanStringObject<4> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
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
static mut l_Lean_Grind_CommRing_OfCommSemiring_toQUnexpander___closed__3:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Grind_CommRing_OfCommSemiring_toQUnexpander___closed__3_value)
        as *mut leanh::LeanObject;
static l_Lean_Grind_CommRing_OfCommSemiring_toQUnexpander___closed__4_value_aux_0:
    leanh::LeanCtorObject<3> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Grind_CommRing_OfCommSemiring_toQUnexpander___closed__0_value)
            as *mut leanh::LeanObject,
        11948124481539785030 as *mut leanh::LeanObject,
    ],
};
static l_Lean_Grind_CommRing_OfCommSemiring_toQUnexpander___closed__4_value_aux_1:
    leanh::LeanCtorObject<3> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l_Lean_Grind_CommRing_OfCommSemiring_toQUnexpander___closed__4_value_aux_0
        ) as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Grind_CommRing_OfCommSemiring_toQUnexpander___closed__1_value)
            as *mut leanh::LeanObject,
        8018486133748762727 as *mut leanh::LeanObject,
    ],
};
static l_Lean_Grind_CommRing_OfCommSemiring_toQUnexpander___closed__4_value_aux_2:
    leanh::LeanCtorObject<3> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l_Lean_Grind_CommRing_OfCommSemiring_toQUnexpander___closed__4_value_aux_1
        ) as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Grind_CommRing_OfCommSemiring_toQUnexpander___closed__2_value)
            as *mut leanh::LeanObject,
        16572064140653406795 as *mut leanh::LeanObject,
    ],
};
pub static l_Lean_Grind_CommRing_OfCommSemiring_toQUnexpander___closed__4_value:
    leanh::LeanCtorObject<3> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l_Lean_Grind_CommRing_OfCommSemiring_toQUnexpander___closed__4_value_aux_2
        ) as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Grind_CommRing_OfCommSemiring_toQUnexpander___closed__3_value)
            as *mut leanh::LeanObject,
        12966880221525079621 as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Grind_CommRing_OfCommSemiring_toQUnexpander___closed__4:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Grind_CommRing_OfCommSemiring_toQUnexpander___closed__4_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Grind_CommRing_OfCommSemiring_toQUnexpander___closed__5_value:
    leanh::LeanStringObject<12> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
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
static mut l_Lean_Grind_CommRing_OfCommSemiring_toQUnexpander___closed__5:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Grind_CommRing_OfCommSemiring_toQUnexpander___closed__5_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Grind_CommRing_OfCommSemiring_toQUnexpander___closed__6_value:
    leanh::LeanCtorObject<3> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Grind_CommRing_OfCommSemiring_toQUnexpander___closed__5_value)
            as *mut leanh::LeanObject,
        4193428478068483112 as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Grind_CommRing_OfCommSemiring_toQUnexpander___closed__6:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Grind_CommRing_OfCommSemiring_toQUnexpander___closed__6_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Grind_CommRing_OfCommSemiring_toQUnexpander___closed__7_value:
    leanh::LeanStringObject<4> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
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
static mut l_Lean_Grind_CommRing_OfCommSemiring_toQUnexpander___closed__7:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Grind_CommRing_OfCommSemiring_toQUnexpander___closed__7_value)
        as *mut leanh::LeanObject;
pub unsafe fn l___private_Init_Grind_Ring_Envelope_0__Lean_Grind_Ring_OfSemiring_r_match__1_splitter___redArg(
    mut v_x_427_: *mut leanh::LeanObject,
    mut v_x_428_: *mut leanh::LeanObject,
    mut v_h__1_429_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_fst_430_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_431_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_432_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_433_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_434_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_fst_430_ = leanh::lean_ctor_get(v_x_427_, 0);
    leanh::lean_inc(v_fst_430_);
    v_snd_431_ = leanh::lean_ctor_get(v_x_427_, 1);
    leanh::lean_inc(v_snd_431_);
    leanh::lean_dec_ref(v_x_427_);
    v_fst_432_ = leanh::lean_ctor_get(v_x_428_, 0);
    leanh::lean_inc(v_fst_432_);
    v_snd_433_ = leanh::lean_ctor_get(v_x_428_, 1);
    leanh::lean_inc(v_snd_433_);
    leanh::lean_dec_ref(v_x_428_);
    v___x_434_ =
        leanh::lean_apply_4(v_h__1_429_, v_fst_430_, v_snd_431_, v_fst_432_, v_snd_433_);
    return v___x_434_;
}
pub unsafe fn l___private_Init_Grind_Ring_Envelope_0__Lean_Grind_Ring_OfSemiring_r_match__1_splitter(
    mut v_00_u03b1_435_: *mut leanh::LeanObject,
    mut v_motive_436_: *mut leanh::LeanObject,
    mut v_x_437_: *mut leanh::LeanObject,
    mut v_x_438_: *mut leanh::LeanObject,
    mut v_h__1_439_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_fst_440_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_441_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_442_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_443_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_444_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_fst_440_ = leanh::lean_ctor_get(v_x_437_, 0);
    leanh::lean_inc(v_fst_440_);
    v_snd_441_ = leanh::lean_ctor_get(v_x_437_, 1);
    leanh::lean_inc(v_snd_441_);
    leanh::lean_dec_ref(v_x_437_);
    v_fst_442_ = leanh::lean_ctor_get(v_x_438_, 0);
    leanh::lean_inc(v_fst_442_);
    v_snd_443_ = leanh::lean_ctor_get(v_x_438_, 1);
    leanh::lean_inc(v_snd_443_);
    leanh::lean_dec_ref(v_x_438_);
    v___x_444_ =
        leanh::lean_apply_4(v_h__1_439_, v_fst_440_, v_snd_441_, v_fst_442_, v_snd_443_);
    return v___x_444_;
}
pub unsafe fn l_Lean_Grind_Ring_OfSemiring_Q_mk___redArg(
    mut v_p_445_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    leanh::lean_inc_ref(v_p_445_);
    return v_p_445_;
}
pub unsafe fn l_Lean_Grind_Ring_OfSemiring_Q_mk___redArg___boxed(
    mut v_p_446_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_447_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_447_ = l_Lean_Grind_Ring_OfSemiring_Q_mk___redArg(v_p_446_);
    leanh::lean_dec_ref(v_p_446_);
    return v_res_447_;
}
pub unsafe fn l_Lean_Grind_Ring_OfSemiring_Q_mk(
    mut v_00_u03b1_448_: *mut leanh::LeanObject,
    mut v_inst_449_: *mut leanh::LeanObject,
    mut v_p_450_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    leanh::lean_inc_ref(v_p_450_);
    return v_p_450_;
}
pub unsafe fn l_Lean_Grind_Ring_OfSemiring_Q_mk___boxed(
    mut v_00_u03b1_451_: *mut leanh::LeanObject,
    mut v_inst_452_: *mut leanh::LeanObject,
    mut v_p_453_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_454_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_454_ = l_Lean_Grind_Ring_OfSemiring_Q_mk(v_00_u03b1_451_, v_inst_452_, v_p_453_);
    leanh::lean_dec_ref(v_p_453_);
    leanh::lean_dec_ref(v_inst_452_);
    return v_res_454_;
}
pub unsafe fn l_Lean_Grind_Ring_OfSemiring_Q_liftOn_u2082___redArg(
    mut v_q_u2081_455_: *mut leanh::LeanObject,
    mut v_q_u2082_456_: *mut leanh::LeanObject,
    mut v_f_457_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_458_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_458_ = leanh::lean_apply_2(v_f_457_, v_q_u2081_455_, v_q_u2082_456_);
    return v___x_458_;
}
pub unsafe fn l_Lean_Grind_Ring_OfSemiring_Q_liftOn_u2082(
    mut v_00_u03b1_459_: *mut leanh::LeanObject,
    mut v_inst_460_: *mut leanh::LeanObject,
    mut v_00_u03b2_461_: *mut leanh::LeanObject,
    mut v_q_u2081_462_: *mut leanh::LeanObject,
    mut v_q_u2082_463_: *mut leanh::LeanObject,
    mut v_f_464_: *mut leanh::LeanObject,
    mut v_h_465_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_466_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_466_ = leanh::lean_apply_2(v_f_464_, v_q_u2081_462_, v_q_u2082_463_);
    return v___x_466_;
}
pub unsafe fn l_Lean_Grind_Ring_OfSemiring_Q_liftOn_u2082___boxed(
    mut v_00_u03b1_467_: *mut leanh::LeanObject,
    mut v_inst_468_: *mut leanh::LeanObject,
    mut v_00_u03b2_469_: *mut leanh::LeanObject,
    mut v_q_u2081_470_: *mut leanh::LeanObject,
    mut v_q_u2082_471_: *mut leanh::LeanObject,
    mut v_f_472_: *mut leanh::LeanObject,
    mut v_h_473_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_474_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_474_ = l_Lean_Grind_Ring_OfSemiring_Q_liftOn_u2082(
        v_00_u03b1_467_,
        v_inst_468_,
        v_00_u03b2_469_,
        v_q_u2081_470_,
        v_q_u2082_471_,
        v_f_472_,
        v_h_473_,
    );
    leanh::lean_dec_ref(v_inst_468_);
    return v_res_474_;
}
pub unsafe fn l_Lean_Grind_Ring_OfSemiring_natCast___redArg(
    mut v_inst_475_: *mut leanh::LeanObject,
    mut v_n_476_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_natCast_477_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ofNat_478_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_479_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_480_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_481_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_482_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_natCast_477_ = leanh::lean_ctor_get(v_inst_475_, 2);
    leanh::lean_inc(v_natCast_477_);
    v_ofNat_478_ = leanh::lean_ctor_get(v_inst_475_, 3);
    leanh::lean_inc(v_ofNat_478_);
    leanh::lean_dec_ref(v_inst_475_);
    v___x_479_ = leanh::lean_apply_1(v_natCast_477_, v_n_476_);
    v___x_480_ = leanh::lean_unsigned_to_nat(0);
    v___x_481_ = leanh::lean_apply_1(v_ofNat_478_, v___x_480_);
    v___x_482_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_482_, 0, v___x_479_);
    leanh::lean_ctor_set(v___x_482_, 1, v___x_481_);
    return v___x_482_;
}
pub unsafe fn l_Lean_Grind_Ring_OfSemiring_natCast(
    mut v_00_u03b1_483_: *mut leanh::LeanObject,
    mut v_inst_484_: *mut leanh::LeanObject,
    mut v_n_485_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_486_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_486_ = l_Lean_Grind_Ring_OfSemiring_natCast___redArg(v_inst_484_, v_n_485_);
    return v___x_486_;
}
pub unsafe fn _init_l_Lean_Grind_Ring_OfSemiring_intCast___redArg___closed__0()
-> *mut leanh::LeanObject {
    let mut v___x_487_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_488_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_487_ = leanh::lean_unsigned_to_nat(0);
    v___x_488_ = lean_nat_to_int(v___x_487_);
    return v___x_488_;
}
pub unsafe fn l_Lean_Grind_Ring_OfSemiring_intCast___redArg(
    mut v_inst_489_: *mut leanh::LeanObject,
    mut v_n_490_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_491_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_492_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_493_: u8 = 0;
    v___x_491_ = leanh::lean_unsigned_to_nat(0);
    v___x_492_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Grind_Ring_OfSemiring_intCast___redArg___closed__0),
        core::ptr::addr_of_mut!(l_Lean_Grind_Ring_OfSemiring_intCast___redArg___closed__0_once),
        _init_l_Lean_Grind_Ring_OfSemiring_intCast___redArg___closed__0,
    );
    v___x_493_ = lean_int_dec_lt(v_n_490_, v___x_492_);
    if v___x_493_ == 0 {
        let mut v_natCast_494_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_ofNat_495_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_496_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_497_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_498_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_499_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_natCast_494_ = leanh::lean_ctor_get(v_inst_489_, 2);
        leanh::lean_inc(v_natCast_494_);
        v_ofNat_495_ = leanh::lean_ctor_get(v_inst_489_, 3);
        leanh::lean_inc(v_ofNat_495_);
        leanh::lean_dec_ref(v_inst_489_);
        v___x_496_ = lean_nat_abs(v_n_490_);
        v___x_497_ = leanh::lean_apply_1(v_natCast_494_, v___x_496_);
        v___x_498_ = leanh::lean_apply_1(v_ofNat_495_, v___x_491_);
        v___x_499_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
        leanh::lean_ctor_set(v___x_499_, 0, v___x_497_);
        leanh::lean_ctor_set(v___x_499_, 1, v___x_498_);
        return v___x_499_;
    } else {
        let mut v_natCast_500_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_ofNat_501_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_502_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_503_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_504_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_505_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_natCast_500_ = leanh::lean_ctor_get(v_inst_489_, 2);
        leanh::lean_inc(v_natCast_500_);
        v_ofNat_501_ = leanh::lean_ctor_get(v_inst_489_, 3);
        leanh::lean_inc(v_ofNat_501_);
        leanh::lean_dec_ref(v_inst_489_);
        v___x_502_ = leanh::lean_apply_1(v_ofNat_501_, v___x_491_);
        v___x_503_ = lean_nat_abs(v_n_490_);
        v___x_504_ = leanh::lean_apply_1(v_natCast_500_, v___x_503_);
        v___x_505_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
        leanh::lean_ctor_set(v___x_505_, 0, v___x_502_);
        leanh::lean_ctor_set(v___x_505_, 1, v___x_504_);
        return v___x_505_;
    }
}
pub unsafe fn l_Lean_Grind_Ring_OfSemiring_intCast___redArg___boxed(
    mut v_inst_506_: *mut leanh::LeanObject,
    mut v_n_507_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_508_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_508_ = l_Lean_Grind_Ring_OfSemiring_intCast___redArg(v_inst_506_, v_n_507_);
    leanh::lean_dec(v_n_507_);
    return v_res_508_;
}
pub unsafe fn l_Lean_Grind_Ring_OfSemiring_intCast(
    mut v_00_u03b1_509_: *mut leanh::LeanObject,
    mut v_inst_510_: *mut leanh::LeanObject,
    mut v_n_511_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_512_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_512_ = l_Lean_Grind_Ring_OfSemiring_intCast___redArg(v_inst_510_, v_n_511_);
    return v___x_512_;
}
pub unsafe fn l_Lean_Grind_Ring_OfSemiring_intCast___boxed(
    mut v_00_u03b1_513_: *mut leanh::LeanObject,
    mut v_inst_514_: *mut leanh::LeanObject,
    mut v_n_515_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_516_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_516_ = l_Lean_Grind_Ring_OfSemiring_intCast(v_00_u03b1_513_, v_inst_514_, v_n_515_);
    leanh::lean_dec(v_n_515_);
    return v_res_516_;
}
pub unsafe fn l_Lean_Grind_Ring_OfSemiring_sub___redArg(
    mut v_inst_517_: *mut leanh::LeanObject,
    mut v_q_u2081_518_: *mut leanh::LeanObject,
    mut v_q_u2082_519_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_toAdd_520_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_521_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_522_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_523_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_524_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_526_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_527_: u8 = 0;
    let mut v___x_528_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_529_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_531_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_532_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_533_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_toAdd_520_ = leanh::lean_ctor_get(v_inst_517_, 0);
                leanh::lean_inc(v_toAdd_520_);
                leanh::lean_dec_ref(v_inst_517_);
                v_fst_521_ = leanh::lean_ctor_get(v_q_u2081_518_, 0);
                leanh::lean_inc(v_fst_521_);
                v_snd_522_ = leanh::lean_ctor_get(v_q_u2081_518_, 1);
                leanh::lean_inc(v_snd_522_);
                leanh::lean_dec(v_q_u2081_518_);
                v_fst_523_ = leanh::lean_ctor_get(v_q_u2082_519_, 0);
                v_snd_524_ = leanh::lean_ctor_get(v_q_u2082_519_, 1);
                v_isSharedCheck_533_ = (!leanh::lean_is_exclusive(v_q_u2082_519_)) as u8;
                if v_isSharedCheck_533_ == 0 {
                    v___x_526_ = v_q_u2082_519_;
                    v_isShared_527_ = v_isSharedCheck_533_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_snd_524_);
                    leanh::lean_inc(v_fst_523_);
                    leanh::lean_dec(v_q_u2082_519_);
                    v___x_526_ = leanh::lean_box(0);
                    v_isShared_527_ = v_isSharedCheck_533_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                leanh::lean_inc(v_toAdd_520_);
                v___x_528_ = leanh::lean_apply_2(v_toAdd_520_, v_fst_521_, v_snd_524_);
                v___x_529_ = leanh::lean_apply_2(v_toAdd_520_, v_fst_523_, v_snd_522_);
                if v_isShared_527_ == 0 {
                    leanh::lean_ctor_set(v___x_526_, 1, v___x_529_);
                    leanh::lean_ctor_set(v___x_526_, 0, v___x_528_);
                    v___x_531_ = v___x_526_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_532_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_532_, 0, v___x_528_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_532_, 1, v___x_529_);
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
    mut v_00_u03b1_534_: *mut leanh::LeanObject,
    mut v_inst_535_: *mut leanh::LeanObject,
    mut v_q_u2081_536_: *mut leanh::LeanObject,
    mut v_q_u2082_537_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_538_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_538_ =
        l_Lean_Grind_Ring_OfSemiring_sub___redArg(v_inst_535_, v_q_u2081_536_, v_q_u2082_537_);
    return v___x_538_;
}
pub unsafe fn l_Lean_Grind_Ring_OfSemiring_add___redArg(
    mut v_inst_539_: *mut leanh::LeanObject,
    mut v_q_u2081_540_: *mut leanh::LeanObject,
    mut v_q_u2082_541_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_toAdd_542_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_543_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_544_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_545_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_546_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_548_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_549_: u8 = 0;
    let mut v___x_550_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_551_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_553_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_554_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_555_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_toAdd_542_ = leanh::lean_ctor_get(v_inst_539_, 0);
                leanh::lean_inc(v_toAdd_542_);
                leanh::lean_dec_ref(v_inst_539_);
                v_fst_543_ = leanh::lean_ctor_get(v_q_u2081_540_, 0);
                leanh::lean_inc(v_fst_543_);
                v_snd_544_ = leanh::lean_ctor_get(v_q_u2081_540_, 1);
                leanh::lean_inc(v_snd_544_);
                leanh::lean_dec(v_q_u2081_540_);
                v_fst_545_ = leanh::lean_ctor_get(v_q_u2082_541_, 0);
                v_snd_546_ = leanh::lean_ctor_get(v_q_u2082_541_, 1);
                v_isSharedCheck_555_ = (!leanh::lean_is_exclusive(v_q_u2082_541_)) as u8;
                if v_isSharedCheck_555_ == 0 {
                    v___x_548_ = v_q_u2082_541_;
                    v_isShared_549_ = v_isSharedCheck_555_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_snd_546_);
                    leanh::lean_inc(v_fst_545_);
                    leanh::lean_dec(v_q_u2082_541_);
                    v___x_548_ = leanh::lean_box(0);
                    v_isShared_549_ = v_isSharedCheck_555_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                leanh::lean_inc(v_toAdd_542_);
                v___x_550_ = leanh::lean_apply_2(v_toAdd_542_, v_fst_543_, v_fst_545_);
                v___x_551_ = leanh::lean_apply_2(v_toAdd_542_, v_snd_544_, v_snd_546_);
                if v_isShared_549_ == 0 {
                    leanh::lean_ctor_set(v___x_548_, 1, v___x_551_);
                    leanh::lean_ctor_set(v___x_548_, 0, v___x_550_);
                    v___x_553_ = v___x_548_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_554_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_554_, 0, v___x_550_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_554_, 1, v___x_551_);
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
    mut v_00_u03b1_556_: *mut leanh::LeanObject,
    mut v_inst_557_: *mut leanh::LeanObject,
    mut v_q_u2081_558_: *mut leanh::LeanObject,
    mut v_q_u2082_559_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_560_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_560_ =
        l_Lean_Grind_Ring_OfSemiring_add___redArg(v_inst_557_, v_q_u2081_558_, v_q_u2082_559_);
    return v___x_560_;
}
pub unsafe fn l_Lean_Grind_Ring_OfSemiring_mul___redArg(
    mut v_inst_561_: *mut leanh::LeanObject,
    mut v_q_u2081_562_: *mut leanh::LeanObject,
    mut v_q_u2082_563_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_toAdd_564_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toMul_565_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_566_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_567_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_568_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_569_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_571_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_572_: u8 = 0;
    let mut v___x_573_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_574_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_575_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_576_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_577_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_578_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_580_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_581_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_582_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_toAdd_564_ = leanh::lean_ctor_get(v_inst_561_, 0);
                leanh::lean_inc(v_toAdd_564_);
                v_toMul_565_ = leanh::lean_ctor_get(v_inst_561_, 1);
                leanh::lean_inc(v_toMul_565_);
                leanh::lean_dec_ref(v_inst_561_);
                v_fst_566_ = leanh::lean_ctor_get(v_q_u2081_562_, 0);
                leanh::lean_inc(v_fst_566_);
                v_snd_567_ = leanh::lean_ctor_get(v_q_u2081_562_, 1);
                leanh::lean_inc(v_snd_567_);
                leanh::lean_dec(v_q_u2081_562_);
                v_fst_568_ = leanh::lean_ctor_get(v_q_u2082_563_, 0);
                v_snd_569_ = leanh::lean_ctor_get(v_q_u2082_563_, 1);
                v_isSharedCheck_582_ = (!leanh::lean_is_exclusive(v_q_u2082_563_)) as u8;
                if v_isSharedCheck_582_ == 0 {
                    v___x_571_ = v_q_u2082_563_;
                    v_isShared_572_ = v_isSharedCheck_582_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_snd_569_);
                    leanh::lean_inc(v_fst_568_);
                    leanh::lean_dec(v_q_u2082_563_);
                    v___x_571_ = leanh::lean_box(0);
                    v_isShared_572_ = v_isSharedCheck_582_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                leanh::lean_inc_n(v_toMul_565_, 3);
                leanh::lean_inc(v_fst_568_);
                leanh::lean_inc(v_fst_566_);
                v___x_573_ = leanh::lean_apply_2(v_toMul_565_, v_fst_566_, v_fst_568_);
                leanh::lean_inc(v_snd_569_);
                leanh::lean_inc(v_snd_567_);
                v___x_574_ = leanh::lean_apply_2(v_toMul_565_, v_snd_567_, v_snd_569_);
                leanh::lean_inc(v_toAdd_564_);
                v___x_575_ = leanh::lean_apply_2(v_toAdd_564_, v___x_573_, v___x_574_);
                v___x_576_ = leanh::lean_apply_2(v_toMul_565_, v_fst_566_, v_snd_569_);
                v___x_577_ = leanh::lean_apply_2(v_toMul_565_, v_snd_567_, v_fst_568_);
                v___x_578_ = leanh::lean_apply_2(v_toAdd_564_, v___x_576_, v___x_577_);
                if v_isShared_572_ == 0 {
                    leanh::lean_ctor_set(v___x_571_, 1, v___x_578_);
                    leanh::lean_ctor_set(v___x_571_, 0, v___x_575_);
                    v___x_580_ = v___x_571_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_581_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_581_, 0, v___x_575_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_581_, 1, v___x_578_);
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
    mut v_00_u03b1_583_: *mut leanh::LeanObject,
    mut v_inst_584_: *mut leanh::LeanObject,
    mut v_q_u2081_585_: *mut leanh::LeanObject,
    mut v_q_u2082_586_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_587_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_587_ =
        l_Lean_Grind_Ring_OfSemiring_mul___redArg(v_inst_584_, v_q_u2081_585_, v_q_u2082_586_);
    return v___x_587_;
}
pub unsafe fn l_Lean_Grind_Ring_OfSemiring_neg___redArg(
    mut v_q_588_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_fst_589_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_590_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_592_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_593_: u8 = 0;
    let mut v___x_595_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_596_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_597_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_fst_589_ = leanh::lean_ctor_get(v_q_588_, 0);
                v_snd_590_ = leanh::lean_ctor_get(v_q_588_, 1);
                v_isSharedCheck_597_ = (!leanh::lean_is_exclusive(v_q_588_)) as u8;
                if v_isSharedCheck_597_ == 0 {
                    v___x_592_ = v_q_588_;
                    v_isShared_593_ = v_isSharedCheck_597_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_snd_590_);
                    leanh::lean_inc(v_fst_589_);
                    leanh::lean_dec(v_q_588_);
                    v___x_592_ = leanh::lean_box(0);
                    v_isShared_593_ = v_isSharedCheck_597_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                if v_isShared_593_ == 0 {
                    leanh::lean_ctor_set(v___x_592_, 1, v_fst_589_);
                    leanh::lean_ctor_set(v___x_592_, 0, v_snd_590_);
                    v___x_595_ = v___x_592_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_596_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_596_, 0, v_snd_590_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_596_, 1, v_fst_589_);
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
    mut v_00_u03b1_598_: *mut leanh::LeanObject,
    mut v_inst_599_: *mut leanh::LeanObject,
    mut v_q_600_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_601_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_601_ = l_Lean_Grind_Ring_OfSemiring_neg___redArg(v_q_600_);
    return v___x_601_;
}
pub unsafe fn l_Lean_Grind_Ring_OfSemiring_neg___boxed(
    mut v_00_u03b1_602_: *mut leanh::LeanObject,
    mut v_inst_603_: *mut leanh::LeanObject,
    mut v_q_604_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_605_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_605_ = l_Lean_Grind_Ring_OfSemiring_neg(v_00_u03b1_602_, v_inst_603_, v_q_604_);
    leanh::lean_dec_ref(v_inst_603_);
    return v_res_605_;
}
pub unsafe fn l_Lean_Grind_Ring_OfSemiring_npow___redArg(
    mut v_inst_606_: *mut leanh::LeanObject,
    mut v_a_607_: *mut leanh::LeanObject,
    mut v_n_608_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_zero_609_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isZero_610_: u8 = 0;
    v_zero_609_ = leanh::lean_unsigned_to_nat(0);
    v_isZero_610_ = lean_nat_dec_eq(v_n_608_, v_zero_609_);
    if v_isZero_610_ == 1 {
        let mut v___x_611_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_612_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_a_607_);
        v___x_611_ = leanh::lean_unsigned_to_nat(1);
        v___x_612_ = l_Lean_Grind_Ring_OfSemiring_natCast___redArg(v_inst_606_, v___x_611_);
        return v___x_612_;
    } else {
        let mut v_one_613_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_n_614_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_615_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_616_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_one_613_ = leanh::lean_unsigned_to_nat(1);
        v_n_614_ = lean_nat_sub(v_n_608_, v_one_613_);
        leanh::lean_inc(v_a_607_);
        leanh::lean_inc_ref(v_inst_606_);
        v___x_615_ = l_Lean_Grind_Ring_OfSemiring_npow___redArg(v_inst_606_, v_a_607_, v_n_614_);
        leanh::lean_dec(v_n_614_);
        v___x_616_ = l_Lean_Grind_Ring_OfSemiring_mul___redArg(v_inst_606_, v___x_615_, v_a_607_);
        return v___x_616_;
    }
}
pub unsafe fn l_Lean_Grind_Ring_OfSemiring_npow___redArg___boxed(
    mut v_inst_617_: *mut leanh::LeanObject,
    mut v_a_618_: *mut leanh::LeanObject,
    mut v_n_619_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_620_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_620_ = l_Lean_Grind_Ring_OfSemiring_npow___redArg(v_inst_617_, v_a_618_, v_n_619_);
    leanh::lean_dec(v_n_619_);
    return v_res_620_;
}
pub unsafe fn l_Lean_Grind_Ring_OfSemiring_npow(
    mut v_00_u03b1_621_: *mut leanh::LeanObject,
    mut v_inst_622_: *mut leanh::LeanObject,
    mut v_a_623_: *mut leanh::LeanObject,
    mut v_n_624_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_625_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_625_ = l_Lean_Grind_Ring_OfSemiring_npow___redArg(v_inst_622_, v_a_623_, v_n_624_);
    return v___x_625_;
}
pub unsafe fn l_Lean_Grind_Ring_OfSemiring_npow___boxed(
    mut v_00_u03b1_626_: *mut leanh::LeanObject,
    mut v_inst_627_: *mut leanh::LeanObject,
    mut v_a_628_: *mut leanh::LeanObject,
    mut v_n_629_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_630_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_630_ =
        l_Lean_Grind_Ring_OfSemiring_npow(v_00_u03b1_626_, v_inst_627_, v_a_628_, v_n_629_);
    leanh::lean_dec(v_n_629_);
    return v_res_630_;
}
pub unsafe fn l_Lean_Grind_Ring_OfSemiring_nsmul___redArg(
    mut v_inst_631_: *mut leanh::LeanObject,
    mut v_n_632_: *mut leanh::LeanObject,
    mut v_a_633_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_634_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_635_: *mut leanh::LeanObject = core::ptr::null_mut();
    leanh::lean_inc_ref(v_inst_631_);
    v___x_634_ = l_Lean_Grind_Ring_OfSemiring_natCast___redArg(v_inst_631_, v_n_632_);
    v___x_635_ = l_Lean_Grind_Ring_OfSemiring_mul___redArg(v_inst_631_, v___x_634_, v_a_633_);
    return v___x_635_;
}
pub unsafe fn l_Lean_Grind_Ring_OfSemiring_nsmul(
    mut v_00_u03b1_636_: *mut leanh::LeanObject,
    mut v_inst_637_: *mut leanh::LeanObject,
    mut v_n_638_: *mut leanh::LeanObject,
    mut v_a_639_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_640_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_640_ = l_Lean_Grind_Ring_OfSemiring_nsmul___redArg(v_inst_637_, v_n_638_, v_a_639_);
    return v___x_640_;
}
pub unsafe fn l_Lean_Grind_Ring_OfSemiring_zsmul___redArg(
    mut v_inst_641_: *mut leanh::LeanObject,
    mut v_i_642_: *mut leanh::LeanObject,
    mut v_a_643_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_644_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_645_: *mut leanh::LeanObject = core::ptr::null_mut();
    leanh::lean_inc_ref(v_inst_641_);
    v___x_644_ = l_Lean_Grind_Ring_OfSemiring_intCast___redArg(v_inst_641_, v_i_642_);
    v___x_645_ = l_Lean_Grind_Ring_OfSemiring_mul___redArg(v_inst_641_, v___x_644_, v_a_643_);
    return v___x_645_;
}
pub unsafe fn l_Lean_Grind_Ring_OfSemiring_zsmul___redArg___boxed(
    mut v_inst_646_: *mut leanh::LeanObject,
    mut v_i_647_: *mut leanh::LeanObject,
    mut v_a_648_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_649_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_649_ = l_Lean_Grind_Ring_OfSemiring_zsmul___redArg(v_inst_646_, v_i_647_, v_a_648_);
    leanh::lean_dec(v_i_647_);
    return v_res_649_;
}
pub unsafe fn l_Lean_Grind_Ring_OfSemiring_zsmul(
    mut v_00_u03b1_650_: *mut leanh::LeanObject,
    mut v_inst_651_: *mut leanh::LeanObject,
    mut v_i_652_: *mut leanh::LeanObject,
    mut v_a_653_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_654_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_654_ = l_Lean_Grind_Ring_OfSemiring_zsmul___redArg(v_inst_651_, v_i_652_, v_a_653_);
    return v___x_654_;
}
pub unsafe fn l_Lean_Grind_Ring_OfSemiring_zsmul___boxed(
    mut v_00_u03b1_655_: *mut leanh::LeanObject,
    mut v_inst_656_: *mut leanh::LeanObject,
    mut v_i_657_: *mut leanh::LeanObject,
    mut v_a_658_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_659_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_659_ =
        l_Lean_Grind_Ring_OfSemiring_zsmul(v_00_u03b1_655_, v_inst_656_, v_i_657_, v_a_658_);
    leanh::lean_dec(v_i_657_);
    return v_res_659_;
}
pub unsafe fn l_Lean_Grind_Ring_OfSemiring_ofSemiring___redArg___lam__0(
    mut v_inst_660_: *mut leanh::LeanObject,
    mut v_n_661_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_662_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_662_ = l_Lean_Grind_Ring_OfSemiring_natCast___redArg(v_inst_660_, v_n_661_);
    return v___x_662_;
}
pub unsafe fn l_Lean_Grind_Ring_OfSemiring_ofSemiring___redArg(
    mut v_inst_663_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_664_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_665_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_666_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_667_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_668_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_669_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_670_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_671_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_672_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_673_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_674_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_675_: *mut leanh::LeanObject = core::ptr::null_mut();
    leanh::lean_inc_ref_n(v_inst_663_, 9);
    v___f_664_ = leanh::lean_alloc_closure(
        l_Lean_Grind_Ring_OfSemiring_ofSemiring___redArg___lam__0 as *mut core::ffi::c_void,
        2,
        1,
    );
    leanh::lean_closure_set(v___f_664_, 0, v_inst_663_);
    v___x_665_ = leanh::lean_alloc_closure(
        l_Lean_Grind_Ring_OfSemiring_add as *mut core::ffi::c_void,
        4,
        2,
    );
    leanh::lean_closure_set(v___x_665_, 0, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_665_, 1, v_inst_663_);
    v___x_666_ = leanh::lean_alloc_closure(
        l_Lean_Grind_Ring_OfSemiring_mul as *mut core::ffi::c_void,
        4,
        2,
    );
    leanh::lean_closure_set(v___x_666_, 0, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_666_, 1, v_inst_663_);
    v___x_667_ = leanh::lean_alloc_closure(
        l_Lean_Grind_Ring_OfSemiring_natCast as *mut core::ffi::c_void,
        3,
        2,
    );
    leanh::lean_closure_set(v___x_667_, 0, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_667_, 1, v_inst_663_);
    v___x_668_ = leanh::lean_alloc_closure(
        l_Lean_Grind_Ring_OfSemiring_nsmul as *mut core::ffi::c_void,
        4,
        2,
    );
    leanh::lean_closure_set(v___x_668_, 0, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_668_, 1, v_inst_663_);
    v___x_669_ = leanh::lean_alloc_closure(
        l_Lean_Grind_Ring_OfSemiring_npow___boxed as *mut core::ffi::c_void,
        4,
        2,
    );
    leanh::lean_closure_set(v___x_669_, 0, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_669_, 1, v_inst_663_);
    v___x_670_ = leanh::lean_alloc_ctor(0, 6, (0) as u32);
    leanh::lean_ctor_set(v___x_670_, 0, v___x_665_);
    leanh::lean_ctor_set(v___x_670_, 1, v___x_666_);
    leanh::lean_ctor_set(v___x_670_, 2, v___x_667_);
    leanh::lean_ctor_set(v___x_670_, 3, v___f_664_);
    leanh::lean_ctor_set(v___x_670_, 4, v___x_668_);
    leanh::lean_ctor_set(v___x_670_, 5, v___x_669_);
    v___x_671_ = leanh::lean_alloc_closure(
        l_Lean_Grind_Ring_OfSemiring_neg___boxed as *mut core::ffi::c_void,
        3,
        2,
    );
    leanh::lean_closure_set(v___x_671_, 0, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_671_, 1, v_inst_663_);
    v___x_672_ = leanh::lean_alloc_closure(
        l_Lean_Grind_Ring_OfSemiring_sub as *mut core::ffi::c_void,
        4,
        2,
    );
    leanh::lean_closure_set(v___x_672_, 0, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_672_, 1, v_inst_663_);
    v___x_673_ = leanh::lean_alloc_closure(
        l_Lean_Grind_Ring_OfSemiring_intCast___boxed as *mut core::ffi::c_void,
        3,
        2,
    );
    leanh::lean_closure_set(v___x_673_, 0, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_673_, 1, v_inst_663_);
    v___x_674_ = leanh::lean_alloc_closure(
        l_Lean_Grind_Ring_OfSemiring_zsmul___boxed as *mut core::ffi::c_void,
        4,
        2,
    );
    leanh::lean_closure_set(v___x_674_, 0, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_674_, 1, v_inst_663_);
    v___x_675_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
    leanh::lean_ctor_set(v___x_675_, 0, v___x_670_);
    leanh::lean_ctor_set(v___x_675_, 1, v___x_671_);
    leanh::lean_ctor_set(v___x_675_, 2, v___x_672_);
    leanh::lean_ctor_set(v___x_675_, 3, v___x_673_);
    leanh::lean_ctor_set(v___x_675_, 4, v___x_674_);
    return v___x_675_;
}
pub unsafe fn l_Lean_Grind_Ring_OfSemiring_ofSemiring(
    mut v_00_u03b1_676_: *mut leanh::LeanObject,
    mut v_inst_677_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_678_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_678_ = l_Lean_Grind_Ring_OfSemiring_ofSemiring___redArg(v_inst_677_);
    return v___x_678_;
}
pub unsafe fn l_Lean_Grind_Ring_OfSemiring_toQ___redArg(
    mut v_inst_679_: *mut leanh::LeanObject,
    mut v_a_680_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_ofNat_681_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_682_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_683_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_684_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_ofNat_681_ = leanh::lean_ctor_get(v_inst_679_, 3);
    leanh::lean_inc(v_ofNat_681_);
    leanh::lean_dec_ref(v_inst_679_);
    v___x_682_ = leanh::lean_unsigned_to_nat(0);
    v___x_683_ = leanh::lean_apply_1(v_ofNat_681_, v___x_682_);
    v___x_684_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_684_, 0, v_a_680_);
    leanh::lean_ctor_set(v___x_684_, 1, v___x_683_);
    return v___x_684_;
}
pub unsafe fn l_Lean_Grind_Ring_OfSemiring_toQ(
    mut v_00_u03b1_685_: *mut leanh::LeanObject,
    mut v_inst_686_: *mut leanh::LeanObject,
    mut v_a_687_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_688_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_688_ = l_Lean_Grind_Ring_OfSemiring_toQ___redArg(v_inst_686_, v_a_687_);
    return v___x_688_;
}
pub unsafe fn l_Lean_Grind_Ring_OfSemiring_instLEQOfOrderedAdd(
    mut v_00_u03b1_689_: *mut leanh::LeanObject,
    mut v_inst_690_: *mut leanh::LeanObject,
    mut v_inst_691_: *mut leanh::LeanObject,
    mut v_inst_692_: *mut leanh::LeanObject,
    mut v_inst_693_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_694_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_694_ = leanh::lean_box(0);
    return v___x_694_;
}
pub unsafe fn l_Lean_Grind_Ring_OfSemiring_instLEQOfOrderedAdd___boxed(
    mut v_00_u03b1_695_: *mut leanh::LeanObject,
    mut v_inst_696_: *mut leanh::LeanObject,
    mut v_inst_697_: *mut leanh::LeanObject,
    mut v_inst_698_: *mut leanh::LeanObject,
    mut v_inst_699_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_700_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_700_ = l_Lean_Grind_Ring_OfSemiring_instLEQOfOrderedAdd(
        v_00_u03b1_695_,
        v_inst_696_,
        v_inst_697_,
        v_inst_698_,
        v_inst_699_,
    );
    leanh::lean_dec_ref(v_inst_696_);
    return v_res_700_;
}
pub unsafe fn l_Lean_Grind_Ring_OfSemiring_instLTQOfOrderedAdd(
    mut v_00_u03b1_701_: *mut leanh::LeanObject,
    mut v_inst_702_: *mut leanh::LeanObject,
    mut v_inst_703_: *mut leanh::LeanObject,
    mut v_inst_704_: *mut leanh::LeanObject,
    mut v_inst_705_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_706_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_706_ = leanh::lean_box(0);
    return v___x_706_;
}
pub unsafe fn l_Lean_Grind_Ring_OfSemiring_instLTQOfOrderedAdd___boxed(
    mut v_00_u03b1_707_: *mut leanh::LeanObject,
    mut v_inst_708_: *mut leanh::LeanObject,
    mut v_inst_709_: *mut leanh::LeanObject,
    mut v_inst_710_: *mut leanh::LeanObject,
    mut v_inst_711_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_712_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_712_ = l_Lean_Grind_Ring_OfSemiring_instLTQOfOrderedAdd(
        v_00_u03b1_707_,
        v_inst_708_,
        v_inst_709_,
        v_inst_710_,
        v_inst_711_,
    );
    leanh::lean_dec_ref(v_inst_708_);
    return v_res_712_;
}
pub unsafe fn l_Lean_Grind_CommRing_OfCommSemiring_ofCommSemiring___redArg(
    mut v_inst_713_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_714_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_714_ = l_Lean_Grind_Ring_OfSemiring_ofSemiring___redArg(v_inst_713_);
    return v___x_714_;
}
pub unsafe fn l_Lean_Grind_CommRing_OfCommSemiring_ofCommSemiring(
    mut v_00_u03b1_715_: *mut leanh::LeanObject,
    mut v_inst_716_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_717_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_717_ = l_Lean_Grind_Ring_OfSemiring_ofSemiring___redArg(v_inst_716_);
    return v___x_717_;
}
pub unsafe fn l_Lean_Grind_CommRing_OfCommSemiring_instAddQ___redArg(
    mut v_inst_718_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_toSemiring_719_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toAdd_720_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_toSemiring_719_ = leanh::lean_ctor_get(v_inst_718_, 0);
    v_toAdd_720_ = leanh::lean_ctor_get(v_toSemiring_719_, 0);
    leanh::lean_inc(v_toAdd_720_);
    return v_toAdd_720_;
}
pub unsafe fn l_Lean_Grind_CommRing_OfCommSemiring_instAddQ___redArg___boxed(
    mut v_inst_721_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_722_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_722_ = l_Lean_Grind_CommRing_OfCommSemiring_instAddQ___redArg(v_inst_721_);
    leanh::lean_dec_ref(v_inst_721_);
    return v_res_722_;
}
pub unsafe fn l_Lean_Grind_CommRing_OfCommSemiring_instAddQ(
    mut v_00_u03b1_723_: *mut leanh::LeanObject,
    mut v_inst_724_: *mut leanh::LeanObject,
    mut v_inst_725_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_726_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_726_ = l_Lean_Grind_CommRing_OfCommSemiring_instAddQ___redArg(v_inst_725_);
    return v___x_726_;
}
pub unsafe fn l_Lean_Grind_CommRing_OfCommSemiring_instAddQ___boxed(
    mut v_00_u03b1_727_: *mut leanh::LeanObject,
    mut v_inst_728_: *mut leanh::LeanObject,
    mut v_inst_729_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_730_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_730_ =
        l_Lean_Grind_CommRing_OfCommSemiring_instAddQ(v_00_u03b1_727_, v_inst_728_, v_inst_729_);
    leanh::lean_dec_ref(v_inst_729_);
    leanh::lean_dec_ref(v_inst_728_);
    return v_res_730_;
}
pub unsafe fn l_Lean_Grind_CommRing_OfCommSemiring_instSubQ___redArg(
    mut v_inst_731_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_732_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_732_ = leanh::lean_alloc_closure(
        l_Lean_Grind_Ring_OfSemiring_sub as *mut core::ffi::c_void,
        4,
        2,
    );
    leanh::lean_closure_set(v___x_732_, 0, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_732_, 1, v_inst_731_);
    return v___x_732_;
}
pub unsafe fn l_Lean_Grind_CommRing_OfCommSemiring_instSubQ(
    mut v_00_u03b1_733_: *mut leanh::LeanObject,
    mut v_inst_734_: *mut leanh::LeanObject,
    mut v_inst_735_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_736_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_736_ = leanh::lean_alloc_closure(
        l_Lean_Grind_Ring_OfSemiring_sub as *mut core::ffi::c_void,
        4,
        2,
    );
    leanh::lean_closure_set(v___x_736_, 0, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_736_, 1, v_inst_734_);
    return v___x_736_;
}
pub unsafe fn l_Lean_Grind_CommRing_OfCommSemiring_instSubQ___boxed(
    mut v_00_u03b1_737_: *mut leanh::LeanObject,
    mut v_inst_738_: *mut leanh::LeanObject,
    mut v_inst_739_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_740_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_740_ =
        l_Lean_Grind_CommRing_OfCommSemiring_instSubQ(v_00_u03b1_737_, v_inst_738_, v_inst_739_);
    leanh::lean_dec_ref(v_inst_739_);
    return v_res_740_;
}
pub unsafe fn l_Lean_Grind_CommRing_OfCommSemiring_instMulQ___redArg(
    mut v_inst_741_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_toSemiring_742_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toMul_743_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_toSemiring_742_ = leanh::lean_ctor_get(v_inst_741_, 0);
    v_toMul_743_ = leanh::lean_ctor_get(v_toSemiring_742_, 1);
    leanh::lean_inc(v_toMul_743_);
    return v_toMul_743_;
}
pub unsafe fn l_Lean_Grind_CommRing_OfCommSemiring_instMulQ___redArg___boxed(
    mut v_inst_744_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_745_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_745_ = l_Lean_Grind_CommRing_OfCommSemiring_instMulQ___redArg(v_inst_744_);
    leanh::lean_dec_ref(v_inst_744_);
    return v_res_745_;
}
pub unsafe fn l_Lean_Grind_CommRing_OfCommSemiring_instMulQ(
    mut v_00_u03b1_746_: *mut leanh::LeanObject,
    mut v_inst_747_: *mut leanh::LeanObject,
    mut v_inst_748_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_749_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_749_ = l_Lean_Grind_CommRing_OfCommSemiring_instMulQ___redArg(v_inst_748_);
    return v___x_749_;
}
pub unsafe fn l_Lean_Grind_CommRing_OfCommSemiring_instMulQ___boxed(
    mut v_00_u03b1_750_: *mut leanh::LeanObject,
    mut v_inst_751_: *mut leanh::LeanObject,
    mut v_inst_752_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_753_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_753_ =
        l_Lean_Grind_CommRing_OfCommSemiring_instMulQ(v_00_u03b1_750_, v_inst_751_, v_inst_752_);
    leanh::lean_dec_ref(v_inst_752_);
    leanh::lean_dec_ref(v_inst_751_);
    return v_res_753_;
}
pub unsafe fn l_Lean_Grind_CommRing_OfCommSemiring_instNegQ___redArg(
    mut v_inst_754_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_755_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_755_ = leanh::lean_alloc_closure(
        l_Lean_Grind_Ring_OfSemiring_neg___boxed as *mut core::ffi::c_void,
        3,
        2,
    );
    leanh::lean_closure_set(v___x_755_, 0, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_755_, 1, v_inst_754_);
    return v___x_755_;
}
pub unsafe fn l_Lean_Grind_CommRing_OfCommSemiring_instNegQ(
    mut v_00_u03b1_756_: *mut leanh::LeanObject,
    mut v_inst_757_: *mut leanh::LeanObject,
    mut v_inst_758_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_759_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_759_ = leanh::lean_alloc_closure(
        l_Lean_Grind_Ring_OfSemiring_neg___boxed as *mut core::ffi::c_void,
        3,
        2,
    );
    leanh::lean_closure_set(v___x_759_, 0, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_759_, 1, v_inst_757_);
    return v___x_759_;
}
pub unsafe fn l_Lean_Grind_CommRing_OfCommSemiring_instNegQ___boxed(
    mut v_00_u03b1_760_: *mut leanh::LeanObject,
    mut v_inst_761_: *mut leanh::LeanObject,
    mut v_inst_762_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_763_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_763_ =
        l_Lean_Grind_CommRing_OfCommSemiring_instNegQ(v_00_u03b1_760_, v_inst_761_, v_inst_762_);
    leanh::lean_dec_ref(v_inst_762_);
    return v_res_763_;
}
pub unsafe fn l_Lean_Grind_CommRing_OfCommSemiring_instOfNatQ___redArg(
    mut v_n_764_: *mut leanh::LeanObject,
    mut v_inst_765_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_toSemiring_766_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ofNat_767_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_768_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_toSemiring_766_ = leanh::lean_ctor_get(v_inst_765_, 0);
    leanh::lean_inc_ref(v_toSemiring_766_);
    leanh::lean_dec_ref(v_inst_765_);
    v_ofNat_767_ = leanh::lean_ctor_get(v_toSemiring_766_, 3);
    leanh::lean_inc(v_ofNat_767_);
    leanh::lean_dec_ref(v_toSemiring_766_);
    v___x_768_ = leanh::lean_apply_1(v_ofNat_767_, v_n_764_);
    return v___x_768_;
}
pub unsafe fn l_Lean_Grind_CommRing_OfCommSemiring_instOfNatQ(
    mut v_00_u03b1_769_: *mut leanh::LeanObject,
    mut v_inst_770_: *mut leanh::LeanObject,
    mut v_n_771_: *mut leanh::LeanObject,
    mut v_inst_772_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_773_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_773_ = l_Lean_Grind_CommRing_OfCommSemiring_instOfNatQ___redArg(v_n_771_, v_inst_772_);
    return v___x_773_;
}
pub unsafe fn l_Lean_Grind_CommRing_OfCommSemiring_instOfNatQ___boxed(
    mut v_00_u03b1_774_: *mut leanh::LeanObject,
    mut v_inst_775_: *mut leanh::LeanObject,
    mut v_n_776_: *mut leanh::LeanObject,
    mut v_inst_777_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_778_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_778_ = l_Lean_Grind_CommRing_OfCommSemiring_instOfNatQ(
        v_00_u03b1_774_,
        v_inst_775_,
        v_n_776_,
        v_inst_777_,
    );
    leanh::lean_dec_ref(v_inst_775_);
    return v_res_778_;
}
pub unsafe fn l_Lean_Grind_CommRing_OfCommSemiring_instNatCastQ___redArg(
    mut v_inst_779_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_toSemiring_780_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_natCast_781_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_toSemiring_780_ = leanh::lean_ctor_get(v_inst_779_, 0);
    v_natCast_781_ = leanh::lean_ctor_get(v_toSemiring_780_, 2);
    leanh::lean_inc(v_natCast_781_);
    return v_natCast_781_;
}
pub unsafe fn l_Lean_Grind_CommRing_OfCommSemiring_instNatCastQ___redArg___boxed(
    mut v_inst_782_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_783_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_783_ = l_Lean_Grind_CommRing_OfCommSemiring_instNatCastQ___redArg(v_inst_782_);
    leanh::lean_dec_ref(v_inst_782_);
    return v_res_783_;
}
pub unsafe fn l_Lean_Grind_CommRing_OfCommSemiring_instNatCastQ(
    mut v_00_u03b1_784_: *mut leanh::LeanObject,
    mut v_inst_785_: *mut leanh::LeanObject,
    mut v_inst_786_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_787_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_787_ = l_Lean_Grind_CommRing_OfCommSemiring_instNatCastQ___redArg(v_inst_786_);
    return v___x_787_;
}
pub unsafe fn l_Lean_Grind_CommRing_OfCommSemiring_instNatCastQ___boxed(
    mut v_00_u03b1_788_: *mut leanh::LeanObject,
    mut v_inst_789_: *mut leanh::LeanObject,
    mut v_inst_790_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_791_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_791_ = l_Lean_Grind_CommRing_OfCommSemiring_instNatCastQ(
        v_00_u03b1_788_,
        v_inst_789_,
        v_inst_790_,
    );
    leanh::lean_dec_ref(v_inst_790_);
    leanh::lean_dec_ref(v_inst_789_);
    return v_res_791_;
}
pub unsafe fn l_Lean_Grind_CommRing_OfCommSemiring_instIntCastQ___redArg(
    mut v_inst_792_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_793_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_793_ = leanh::lean_alloc_closure(
        l_Lean_Grind_Ring_OfSemiring_intCast___boxed as *mut core::ffi::c_void,
        3,
        2,
    );
    leanh::lean_closure_set(v___x_793_, 0, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_793_, 1, v_inst_792_);
    return v___x_793_;
}
pub unsafe fn l_Lean_Grind_CommRing_OfCommSemiring_instIntCastQ(
    mut v_00_u03b1_794_: *mut leanh::LeanObject,
    mut v_inst_795_: *mut leanh::LeanObject,
    mut v_inst_796_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_797_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_797_ = leanh::lean_alloc_closure(
        l_Lean_Grind_Ring_OfSemiring_intCast___boxed as *mut core::ffi::c_void,
        3,
        2,
    );
    leanh::lean_closure_set(v___x_797_, 0, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_797_, 1, v_inst_795_);
    return v___x_797_;
}
pub unsafe fn l_Lean_Grind_CommRing_OfCommSemiring_instIntCastQ___boxed(
    mut v_00_u03b1_798_: *mut leanh::LeanObject,
    mut v_inst_799_: *mut leanh::LeanObject,
    mut v_inst_800_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_801_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_801_ = l_Lean_Grind_CommRing_OfCommSemiring_instIntCastQ(
        v_00_u03b1_798_,
        v_inst_799_,
        v_inst_800_,
    );
    leanh::lean_dec_ref(v_inst_800_);
    return v_res_801_;
}
pub unsafe fn l_Lean_Grind_CommRing_OfCommSemiring_instHPowQNat___redArg(
    mut v_inst_802_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_toSemiring_803_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_npow_804_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_toSemiring_803_ = leanh::lean_ctor_get(v_inst_802_, 0);
    v_npow_804_ = leanh::lean_ctor_get(v_toSemiring_803_, 5);
    leanh::lean_inc(v_npow_804_);
    return v_npow_804_;
}
pub unsafe fn l_Lean_Grind_CommRing_OfCommSemiring_instHPowQNat___redArg___boxed(
    mut v_inst_805_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_806_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_806_ = l_Lean_Grind_CommRing_OfCommSemiring_instHPowQNat___redArg(v_inst_805_);
    leanh::lean_dec_ref(v_inst_805_);
    return v_res_806_;
}
pub unsafe fn l_Lean_Grind_CommRing_OfCommSemiring_instHPowQNat(
    mut v_00_u03b1_807_: *mut leanh::LeanObject,
    mut v_inst_808_: *mut leanh::LeanObject,
    mut v_inst_809_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_810_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_810_ = l_Lean_Grind_CommRing_OfCommSemiring_instHPowQNat___redArg(v_inst_809_);
    return v___x_810_;
}
pub unsafe fn l_Lean_Grind_CommRing_OfCommSemiring_instHPowQNat___boxed(
    mut v_00_u03b1_811_: *mut leanh::LeanObject,
    mut v_inst_812_: *mut leanh::LeanObject,
    mut v_inst_813_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_814_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_814_ = l_Lean_Grind_CommRing_OfCommSemiring_instHPowQNat(
        v_00_u03b1_811_,
        v_inst_812_,
        v_inst_813_,
    );
    leanh::lean_dec_ref(v_inst_813_);
    leanh::lean_dec_ref(v_inst_812_);
    return v_res_814_;
}
pub unsafe fn l_Lean_Grind_CommRing_OfCommSemiring_toQUnexpander(
    mut v_stx_828_: *mut leanh::LeanObject,
    mut v_a_829_: *mut leanh::LeanObject,
    mut v_a_830_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_831_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_832_: u8 = 0;
    v___x_831_ = l_Lean_Grind_CommRing_OfCommSemiring_toQUnexpander___closed__4;
    leanh::lean_inc(v_stx_828_);
    v___x_832_ = l_Lean_Syntax_isOfKind(v_stx_828_, v___x_831_);
    if v___x_832_ == 0 {
        let mut v___x_833_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_834_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_stx_828_);
        v___x_833_ = leanh::lean_box(0);
        v___x_834_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
        leanh::lean_ctor_set(v___x_834_, 0, v___x_833_);
        leanh::lean_ctor_set(v___x_834_, 1, v_a_830_);
        return v___x_834_;
    } else {
        let mut v___x_835_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_836_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_837_: u8 = 0;
        v___x_835_ = leanh::lean_unsigned_to_nat(1);
        v___x_836_ = l_Lean_Syntax_getArg(v_stx_828_, v___x_835_);
        leanh::lean_dec(v_stx_828_);
        leanh::lean_inc(v___x_836_);
        v___x_837_ = l_Lean_Syntax_matchesNull(v___x_836_, v___x_835_);
        if v___x_837_ == 0 {
            let mut v___x_838_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_839_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v___x_836_);
            v___x_838_ = leanh::lean_box(0);
            v___x_839_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
            leanh::lean_ctor_set(v___x_839_, 0, v___x_838_);
            leanh::lean_ctor_set(v___x_839_, 1, v_a_830_);
            return v___x_839_;
        } else {
            let mut v___x_840_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_841_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_842_: u8 = 0;
            let mut v___x_843_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_844_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_845_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_846_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_847_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_848_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_840_ = leanh::lean_unsigned_to_nat(0);
            v___x_841_ = l_Lean_Syntax_getArg(v___x_836_, v___x_840_);
            leanh::lean_dec(v___x_836_);
            v___x_842_ = 0;
            v___x_843_ = l_Lean_SourceInfo_fromRef(v_a_829_, v___x_842_);
            v___x_844_ = l_Lean_Grind_CommRing_OfCommSemiring_toQUnexpander___closed__6;
            v___x_845_ = l_Lean_Grind_CommRing_OfCommSemiring_toQUnexpander___closed__7;
            leanh::lean_inc(v___x_843_);
            v___x_846_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
            leanh::lean_ctor_set(v___x_846_, 0, v___x_843_);
            leanh::lean_ctor_set(v___x_846_, 1, v___x_845_);
            v___x_847_ = l_Lean_Syntax_node2(v___x_843_, v___x_844_, v___x_846_, v___x_841_);
            v___x_848_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
            leanh::lean_ctor_set(v___x_848_, 0, v___x_847_);
            leanh::lean_ctor_set(v___x_848_, 1, v_a_830_);
            return v___x_848_;
        }
    }
}
pub unsafe fn l_Lean_Grind_CommRing_OfCommSemiring_toQUnexpander___boxed(
    mut v_stx_849_: *mut leanh::LeanObject,
    mut v_a_850_: *mut leanh::LeanObject,
    mut v_a_851_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_852_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_852_ = l_Lean_Grind_CommRing_OfCommSemiring_toQUnexpander(v_stx_849_, v_a_850_, v_a_851_);
    leanh::lean_dec(v_a_850_);
    return v_res_852_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Init_Grind_Ring_Envelope(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Init_Grind_Ordered_Ring(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_AC(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Omega(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_RCases(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Init_Grind_Ring_Envelope(
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
pub unsafe fn initialize_Init_Grind_Ring_Envelope(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Init_Grind_Ordered_Ring(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_Data_AC(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_Omega(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_RCases(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Grind_Ring_Envelope(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = meta_initialize_Init_Grind_Ring_Envelope(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return initialize_Init_Grind_Ring_Envelope(builtin);
}