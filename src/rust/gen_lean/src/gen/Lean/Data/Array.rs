// Lean compiler output
// Module: Lean.Data.Array
// Imports: Init.Data.Stream Init.Data.Range.Polymorphic.Nat Init.Data.Range.Polymorphic.Iterators
use crate::ffi::{
    lean_array_fget, lean_array_fget_borrowed, lean_array_get, lean_array_get_size,
    lean_array_push, lean_array_set, lean_array_size, lean_array_uget_borrowed, lean_mk_array,
    lean_mk_empty_array_with_capacity, lean_nat_add, lean_nat_dec_lt, lean_usize_add,
    lean_usize_dec_lt,
};
use crate::r#gen::Init::Data::Array::Subarray::l_Array_toSubarray___redArg;
use crate::r#gen::Init::Data::Range::Polymorphic::Iterators::{
    initialize_Init_Data_Range_Polymorphic_Iterators,
    runtime_initialize_Init_Data_Range_Polymorphic_Iterators,
};
use crate::r#gen::Init::Data::Range::Polymorphic::Nat::{
    initialize_Init_Data_Range_Polymorphic_Nat, runtime_initialize_Init_Data_Range_Polymorphic_Nat,
};
use crate::r#gen::Init::Data::Stream::{
    initialize_Init_Data_Stream, runtime_initialize_Init_Data_Stream,
};
use crate::r#gen::Init::WFExtrinsicFix::l_WellFounded_opaqueFix_u2083___redArg;
pub static l_Array_mask___redArg___closed__0_value: leanh::LeanArrayObject<0> =
    leanh::LeanArrayObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<usize>() * 2
                + core::mem::size_of::<*mut leanh::LeanObject>() * 0)
                as u16,
            other: 0,
            tag: 246,
        },
        m_size: 0,
        m_capacity: 0,
        m_data: [],
    };
static mut l_Array_mask___redArg___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Array_mask___redArg___closed__0_value) as *mut leanh::LeanObject;
pub static l_Array_zipMasked___redArg___closed__0_value: leanh::LeanCtorObject<2> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 0,
        },
        m_objs: [
            (((0 as usize) << 1) | 1) as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Array_mask___redArg___closed__0_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Array_zipMasked___redArg___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Array_zipMasked___redArg___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Array_zipMasked___redArg___closed__1_value: leanh::LeanCtorObject<2> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 0,
        },
        m_objs: [
            (((0 as usize) << 1) | 1) as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Array_zipMasked___redArg___closed__0_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Array_zipMasked___redArg___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Array_zipMasked___redArg___closed__1_value)
        as *mut leanh::LeanObject;
pub unsafe fn l_Array_filterPairsM___redArg___lam__0(
    mut v_toPure_531_: *mut leanh::LeanObject,
    mut v_____do__lift_532_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_533_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_533_ = leanh::lean_apply_2(
        v_toPure_531_,
        leanh::lean_box(0),
        v_____do__lift_532_,
    );
    return v___x_533_;
}
pub unsafe fn l_Array_filterPairsM___redArg___lam__2(
    mut v_toPure_534_: *mut leanh::LeanObject,
    mut v_____do__lift_535_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_536_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_536_ = leanh::lean_apply_2(
        v_toPure_534_,
        leanh::lean_box(0),
        v_____do__lift_535_,
    );
    return v___x_536_;
}
pub unsafe fn l_Array_filterPairsM___redArg___lam__1(
    mut v_toPure_537_: *mut leanh::LeanObject,
    mut v_____s_538_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_539_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_539_ = leanh::lean_apply_2(v_toPure_537_, leanh::lean_box(0), v_____s_538_);
    return v___x_539_;
}
pub unsafe fn l_Array_filterPairsM___redArg___lam__3(
    mut v_toPure_540_: *mut leanh::LeanObject,
    mut v_next_541_: *mut leanh::LeanObject,
    mut v_G_542_: *mut leanh::LeanObject,
    mut v_____do__lift_543_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_____do__lift_543_) == 0 {
        let mut v_a_544_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_545_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_G_542_);
        v_a_544_ = leanh::lean_ctor_get(v_____do__lift_543_, 0);
        leanh::lean_inc(v_a_544_);
        leanh::lean_dec_ref_known(v_____do__lift_543_, 1);
        v___x_545_ = leanh::lean_apply_2(v_toPure_540_, leanh::lean_box(0), v_a_544_);
        return v___x_545_;
    } else {
        let mut v_a_546_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_547_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_548_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_549_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_toPure_540_);
        v_a_546_ = leanh::lean_ctor_get(v_____do__lift_543_, 0);
        leanh::lean_inc(v_a_546_);
        leanh::lean_dec_ref_known(v_____do__lift_543_, 1);
        v___x_547_ = leanh::lean_unsigned_to_nat(1);
        v___x_548_ = lean_nat_add(v_next_541_, v___x_547_);
        v___x_549_ = leanh::lean_apply_4(
            v_G_542_,
            v___x_548_,
            v_a_546_,
            leanh::lean_box(0),
            leanh::lean_box(0),
        );
        return v___x_549_;
    }
}
pub unsafe fn l_Array_filterPairsM___redArg___lam__3___boxed(
    mut v_toPure_550_: *mut leanh::LeanObject,
    mut v_next_551_: *mut leanh::LeanObject,
    mut v_G_552_: *mut leanh::LeanObject,
    mut v_____do__lift_553_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_554_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_554_ = l_Array_filterPairsM___redArg___lam__3(
        v_toPure_550_,
        v_next_551_,
        v_G_552_,
        v_____do__lift_553_,
    );
    leanh::lean_dec(v_next_551_);
    return v_res_554_;
}
pub unsafe fn l_Array_filterPairsM___redArg___lam__4(
    mut v___x_555_: *mut leanh::LeanObject,
    mut v_toPure_556_: *mut leanh::LeanObject,
    mut v_toBind_557_: *mut leanh::LeanObject,
    mut v___f_558_: *mut leanh::LeanObject,
    mut v___x_559_: u8,
    mut v_fst_560_: *mut leanh::LeanObject,
    mut v_a_561_: *mut leanh::LeanObject,
    mut v_next_562_: *mut leanh::LeanObject,
    mut v_acc_563_: *mut leanh::LeanObject,
    mut v_h_564_: *mut leanh::LeanObject,
    mut v_G_565_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_566_: u8 = 0;
    let mut v___x_567_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_568_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_570_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_571_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_572_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_573_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_574_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_575_: u8 = 0;
    let mut v___x_576_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_577_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_578_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_579_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_580_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_581_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_566_ = lean_nat_dec_lt(v_next_562_, v___x_555_);
                if v___x_566_ == 0 {
                    leanh::lean_dec(v_G_565_);
                    leanh::lean_dec(v_next_562_);
                    leanh::lean_dec(v___f_558_);
                    leanh::lean_dec(v_toBind_557_);
                    v___x_567_ = leanh::lean_apply_2(
                        v_toPure_556_,
                        leanh::lean_box(0),
                        v_acc_563_,
                    );
                    return v___x_567_;
                } else {
                    leanh::lean_inc(v_next_562_);
                    leanh::lean_inc(v_toPure_556_);
                    v___f_568_ = leanh::lean_alloc_closure(
                        l_Array_filterPairsM___redArg___lam__3___boxed as *mut core::ffi::c_void,
                        4,
                        3,
                    );
                    leanh::lean_closure_set(v___f_568_, 0, v_toPure_556_);
                    leanh::lean_closure_set(v___f_568_, 1, v_next_562_);
                    leanh::lean_closure_set(v___f_568_, 2, v_G_565_);
                    v___x_573_ = leanh::lean_box((v___x_559_) as usize);
                    v___x_574_ = lean_array_get(v___x_573_, v_fst_560_, v_next_562_);
                    leanh::lean_dec(v___x_573_);
                    v___x_575_ = (leanh::lean_unbox(v___x_574_) as u8);
                    leanh::lean_dec(v___x_574_);
                    if v___x_575_ == 0 {
                        v___x_576_ = lean_array_fget_borrowed(v_a_561_, v_next_562_);
                        leanh::lean_dec(v_next_562_);
                        leanh::lean_inc(v___x_576_);
                        v___x_577_ = lean_array_push(v_acc_563_, v___x_576_);
                        v___x_578_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        leanh::lean_ctor_set(v___x_578_, 0, v___x_577_);
                        v___x_579_ = leanh::lean_apply_2(
                            v_toPure_556_,
                            leanh::lean_box(0),
                            v___x_578_,
                        );
                        v___y_570_ = v___x_579_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_dec(v_next_562_);
                        v___x_580_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        leanh::lean_ctor_set(v___x_580_, 0, v_acc_563_);
                        v___x_581_ = leanh::lean_apply_2(
                            v_toPure_556_,
                            leanh::lean_box(0),
                            v___x_580_,
                        );
                        v___y_570_ = v___x_581_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                leanh::lean_inc(v_toBind_557_);
                v___x_571_ = leanh::lean_apply_4(
                    v_toBind_557_,
                    leanh::lean_box(0),
                    leanh::lean_box(0),
                    v___y_570_,
                    v___f_558_,
                );
                v___x_572_ = leanh::lean_apply_4(
                    v_toBind_557_,
                    leanh::lean_box(0),
                    leanh::lean_box(0),
                    v___x_571_,
                    v___f_568_,
                );
                return v___x_572_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Array_filterPairsM___redArg___lam__4___boxed(
    mut v___x_582_: *mut leanh::LeanObject,
    mut v_toPure_583_: *mut leanh::LeanObject,
    mut v_toBind_584_: *mut leanh::LeanObject,
    mut v___f_585_: *mut leanh::LeanObject,
    mut v___x_586_: *mut leanh::LeanObject,
    mut v_fst_587_: *mut leanh::LeanObject,
    mut v_a_588_: *mut leanh::LeanObject,
    mut v_next_589_: *mut leanh::LeanObject,
    mut v_acc_590_: *mut leanh::LeanObject,
    mut v_h_591_: *mut leanh::LeanObject,
    mut v_G_592_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1057__boxed_593_: u8 = 0;
    let mut v_res_594_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1057__boxed_593_ = (leanh::lean_unbox(v___x_586_) as u8);
    v_res_594_ = l_Array_filterPairsM___redArg___lam__4(
        v___x_582_,
        v_toPure_583_,
        v_toBind_584_,
        v___f_585_,
        v___x_1057__boxed_593_,
        v_fst_587_,
        v_a_588_,
        v_next_589_,
        v_acc_590_,
        v_h_591_,
        v_G_592_,
    );
    leanh::lean_dec_ref(v_a_588_);
    leanh::lean_dec(v_fst_587_);
    leanh::lean_dec(v___x_582_);
    return v_res_594_;
}
pub unsafe fn l_Array_filterPairsM___redArg___lam__5(
    mut v___x_595_: *mut leanh::LeanObject,
    mut v_toPure_596_: *mut leanh::LeanObject,
    mut v_toBind_597_: *mut leanh::LeanObject,
    mut v___f_598_: *mut leanh::LeanObject,
    mut v___x_599_: u8,
    mut v_a_600_: *mut leanh::LeanObject,
    mut v___f_601_: *mut leanh::LeanObject,
    mut v_____s_602_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_fst_603_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_604_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_605_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_606_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_607_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_x27_608_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_609_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_610_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_fst_603_ = leanh::lean_ctor_get(v_____s_602_, 0);
    leanh::lean_inc(v_fst_603_);
    v_snd_604_ = leanh::lean_ctor_get(v_____s_602_, 1);
    leanh::lean_inc(v_snd_604_);
    leanh::lean_dec_ref(v_____s_602_);
    v___x_605_ = leanh::lean_unsigned_to_nat(0);
    v___x_606_ = leanh::lean_box((v___x_599_) as usize);
    leanh::lean_inc(v_toBind_597_);
    v___f_607_ = leanh::lean_alloc_closure(
        l_Array_filterPairsM___redArg___lam__4___boxed as *mut core::ffi::c_void,
        11,
        7,
    );
    leanh::lean_closure_set(v___f_607_, 0, v___x_595_);
    leanh::lean_closure_set(v___f_607_, 1, v_toPure_596_);
    leanh::lean_closure_set(v___f_607_, 2, v_toBind_597_);
    leanh::lean_closure_set(v___f_607_, 3, v___f_598_);
    leanh::lean_closure_set(v___f_607_, 4, v___x_606_);
    leanh::lean_closure_set(v___f_607_, 5, v_fst_603_);
    leanh::lean_closure_set(v___f_607_, 6, v_a_600_);
    v_a_x27_608_ = lean_mk_empty_array_with_capacity(v_snd_604_);
    leanh::lean_dec(v_snd_604_);
    v___x_609_ = l_WellFounded_opaqueFix_u2083___redArg(
        v___f_607_,
        v___x_605_,
        v_a_x27_608_,
        leanh::lean_box(0),
    );
    v___x_610_ = leanh::lean_apply_4(
        v_toBind_597_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v___x_609_,
        v___f_601_,
    );
    return v___x_610_;
}
pub unsafe fn l_Array_filterPairsM___redArg___lam__5___boxed(
    mut v___x_611_: *mut leanh::LeanObject,
    mut v_toPure_612_: *mut leanh::LeanObject,
    mut v_toBind_613_: *mut leanh::LeanObject,
    mut v___f_614_: *mut leanh::LeanObject,
    mut v___x_615_: *mut leanh::LeanObject,
    mut v_a_616_: *mut leanh::LeanObject,
    mut v___f_617_: *mut leanh::LeanObject,
    mut v_____s_618_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1098__boxed_619_: u8 = 0;
    let mut v_res_620_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1098__boxed_619_ = (leanh::lean_unbox(v___x_615_) as u8);
    v_res_620_ = l_Array_filterPairsM___redArg___lam__5(
        v___x_611_,
        v_toPure_612_,
        v_toBind_613_,
        v___f_614_,
        v___x_1098__boxed_619_,
        v_a_616_,
        v___f_617_,
        v_____s_618_,
    );
    return v_res_620_;
}
pub unsafe fn l_Array_filterPairsM___redArg___lam__6(
    mut v_toPure_621_: *mut leanh::LeanObject,
    mut v_____s_622_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_fst_623_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_624_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_626_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_627_: u8 = 0;
    let mut v___x_629_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_630_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_631_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_632_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_633_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_fst_623_ = leanh::lean_ctor_get(v_____s_622_, 0);
                v_snd_624_ = leanh::lean_ctor_get(v_____s_622_, 1);
                v_isSharedCheck_633_ = (!leanh::lean_is_exclusive(v_____s_622_)) as u8;
                if v_isSharedCheck_633_ == 0 {
                    v___x_626_ = v_____s_622_;
                    v_isShared_627_ = v_isSharedCheck_633_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_snd_624_);
                    leanh::lean_inc(v_fst_623_);
                    leanh::lean_dec(v_____s_622_);
                    v___x_626_ = leanh::lean_box(0);
                    v_isShared_627_ = v_isSharedCheck_633_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                if v_isShared_627_ == 0 {
                    v___x_629_ = v___x_626_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_632_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_632_, 0, v_fst_623_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_632_, 1, v_snd_624_);
                    v___x_629_ = v_reuseFailAlloc_632_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_630_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_630_, 0, v___x_629_);
                v___x_631_ = leanh::lean_apply_2(
                    v_toPure_621_,
                    leanh::lean_box(0),
                    v___x_630_,
                );
                return v___x_631_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Array_filterPairsM___redArg___lam__7(
    mut v_toPure_634_: *mut leanh::LeanObject,
    mut v_next_635_: *mut leanh::LeanObject,
    mut v_G_636_: *mut leanh::LeanObject,
    mut v_____do__lift_637_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_____do__lift_637_) == 0 {
        let mut v_a_638_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_639_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_G_636_);
        v_a_638_ = leanh::lean_ctor_get(v_____do__lift_637_, 0);
        leanh::lean_inc(v_a_638_);
        leanh::lean_dec_ref_known(v_____do__lift_637_, 1);
        v___x_639_ = leanh::lean_apply_2(v_toPure_634_, leanh::lean_box(0), v_a_638_);
        return v___x_639_;
    } else {
        let mut v_a_640_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_641_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_642_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_643_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_toPure_634_);
        v_a_640_ = leanh::lean_ctor_get(v_____do__lift_637_, 0);
        leanh::lean_inc(v_a_640_);
        leanh::lean_dec_ref_known(v_____do__lift_637_, 1);
        v___x_641_ = leanh::lean_unsigned_to_nat(1);
        v___x_642_ = lean_nat_add(v_next_635_, v___x_641_);
        v___x_643_ = leanh::lean_apply_4(
            v_G_636_,
            v___x_642_,
            v_a_640_,
            leanh::lean_box(0),
            leanh::lean_box(0),
        );
        return v___x_643_;
    }
}
pub unsafe fn l_Array_filterPairsM___redArg___lam__7___boxed(
    mut v_toPure_644_: *mut leanh::LeanObject,
    mut v_next_645_: *mut leanh::LeanObject,
    mut v_G_646_: *mut leanh::LeanObject,
    mut v_____do__lift_647_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_648_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_648_ = l_Array_filterPairsM___redArg___lam__7(
        v_toPure_644_,
        v_next_645_,
        v_G_646_,
        v_____do__lift_647_,
    );
    leanh::lean_dec(v_next_645_);
    return v_res_648_;
}
pub unsafe fn l_Array_filterPairsM___redArg___lam__8(
    mut v_toPure_649_: *mut leanh::LeanObject,
    mut v_next_650_: *mut leanh::LeanObject,
    mut v___x_651_: *mut leanh::LeanObject,
    mut v_G_652_: *mut leanh::LeanObject,
    mut v_____do__lift_653_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_____do__lift_653_) == 0 {
        let mut v_a_654_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_655_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_G_652_);
        v_a_654_ = leanh::lean_ctor_get(v_____do__lift_653_, 0);
        leanh::lean_inc(v_a_654_);
        leanh::lean_dec_ref_known(v_____do__lift_653_, 1);
        v___x_655_ = leanh::lean_apply_2(v_toPure_649_, leanh::lean_box(0), v_a_654_);
        return v___x_655_;
    } else {
        let mut v_a_656_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_657_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_658_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_toPure_649_);
        v_a_656_ = leanh::lean_ctor_get(v_____do__lift_653_, 0);
        leanh::lean_inc(v_a_656_);
        leanh::lean_dec_ref_known(v_____do__lift_653_, 1);
        v___x_657_ = lean_nat_add(v_next_650_, v___x_651_);
        v___x_658_ = leanh::lean_apply_4(
            v_G_652_,
            v___x_657_,
            v_a_656_,
            leanh::lean_box(0),
            leanh::lean_box(0),
        );
        return v___x_658_;
    }
}
pub unsafe fn l_Array_filterPairsM___redArg___lam__8___boxed(
    mut v_toPure_659_: *mut leanh::LeanObject,
    mut v_next_660_: *mut leanh::LeanObject,
    mut v___x_661_: *mut leanh::LeanObject,
    mut v_G_662_: *mut leanh::LeanObject,
    mut v_____do__lift_663_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_664_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_664_ = l_Array_filterPairsM___redArg___lam__8(
        v_toPure_659_,
        v_next_660_,
        v___x_661_,
        v_G_662_,
        v_____do__lift_663_,
    );
    leanh::lean_dec(v___x_661_);
    leanh::lean_dec(v_next_660_);
    return v_res_664_;
}
pub unsafe fn l_Array_filterPairsM___redArg___lam__9(
    mut v___x_665_: *mut leanh::LeanObject,
    mut v_next_666_: *mut leanh::LeanObject,
    mut v___x_667_: u8,
    mut v_toPure_668_: *mut leanh::LeanObject,
    mut v_snd_669_: *mut leanh::LeanObject,
    mut v_fst_670_: *mut leanh::LeanObject,
    mut v_next_671_: *mut leanh::LeanObject,
    mut v_____x_672_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_fst_673_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_674_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_676_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_677_: u8 = 0;
    let mut v_removed_679_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_numRemoved_680_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_681_: u8 = 0;
    let mut v___x_682_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_683_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_684_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_686_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_687_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_688_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_689_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_691_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_692_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_693_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_694_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_695_: u8 = 0;
    let mut v___x_696_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_697_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_698_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_699_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_fst_673_ = leanh::lean_ctor_get(v_____x_672_, 0);
                v_snd_674_ = leanh::lean_ctor_get(v_____x_672_, 1);
                v_isSharedCheck_699_ = (!leanh::lean_is_exclusive(v_____x_672_)) as u8;
                if v_isSharedCheck_699_ == 0 {
                    v___x_676_ = v_____x_672_;
                    v_isShared_677_ = v_isSharedCheck_699_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_snd_674_);
                    leanh::lean_inc(v_fst_673_);
                    leanh::lean_dec(v_____x_672_);
                    v___x_676_ = leanh::lean_box(0);
                    v_isShared_677_ = v_isSharedCheck_699_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_695_ = (leanh::lean_unbox(v_fst_673_) as u8);
                leanh::lean_dec(v_fst_673_);
                if v___x_695_ == 0 {
                    v___x_696_ = lean_nat_add(v_snd_669_, v___x_665_);
                    leanh::lean_dec(v_snd_669_);
                    v___x_697_ = leanh::lean_box((v___x_667_) as usize);
                    v___x_698_ = lean_array_set(v_fst_670_, v_next_671_, v___x_697_);
                    v_removed_679_ = v___x_698_;
                    v_numRemoved_680_ = v___x_696_;
                    state = 2;
                    continue;
                } else {
                    v_removed_679_ = v_fst_670_;
                    v_numRemoved_680_ = v_snd_669_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_681_ = (leanh::lean_unbox(v_snd_674_) as u8);
                leanh::lean_dec(v_snd_674_);
                if v___x_681_ == 0 {
                    v___x_682_ = lean_nat_add(v_numRemoved_680_, v___x_665_);
                    leanh::lean_dec(v_numRemoved_680_);
                    v___x_683_ = leanh::lean_box((v___x_667_) as usize);
                    v___x_684_ = lean_array_set(v_removed_679_, v_next_666_, v___x_683_);
                    if v_isShared_677_ == 0 {
                        leanh::lean_ctor_set(v___x_676_, 1, v___x_682_);
                        leanh::lean_ctor_set(v___x_676_, 0, v___x_684_);
                        v___x_686_ = v___x_676_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_689_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_689_, 0, v___x_684_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_689_, 1, v___x_682_);
                        v___x_686_ = v_reuseFailAlloc_689_;
                        state = 3;
                        continue;
                    }
                } else {
                    if v_isShared_677_ == 0 {
                        leanh::lean_ctor_set(v___x_676_, 1, v_numRemoved_680_);
                        leanh::lean_ctor_set(v___x_676_, 0, v_removed_679_);
                        v___x_691_ = v___x_676_;
                        state = 4;
                        continue;
                    } else {
                        v_reuseFailAlloc_694_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_694_, 0, v_removed_679_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_694_, 1, v_numRemoved_680_);
                        v___x_691_ = v_reuseFailAlloc_694_;
                        state = 4;
                        continue;
                    }
                }
            }
            3 => {
                v___x_687_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_687_, 0, v___x_686_);
                v___x_688_ = leanh::lean_apply_2(
                    v_toPure_668_,
                    leanh::lean_box(0),
                    v___x_687_,
                );
                return v___x_688_;
            }
            4 => {
                v___x_692_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_692_, 0, v___x_691_);
                v___x_693_ = leanh::lean_apply_2(
                    v_toPure_668_,
                    leanh::lean_box(0),
                    v___x_692_,
                );
                return v___x_693_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Array_filterPairsM___redArg___lam__9___boxed(
    mut v___x_700_: *mut leanh::LeanObject,
    mut v_next_701_: *mut leanh::LeanObject,
    mut v___x_702_: *mut leanh::LeanObject,
    mut v_toPure_703_: *mut leanh::LeanObject,
    mut v_snd_704_: *mut leanh::LeanObject,
    mut v_fst_705_: *mut leanh::LeanObject,
    mut v_next_706_: *mut leanh::LeanObject,
    mut v_____x_707_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1173__boxed_708_: u8 = 0;
    let mut v_res_709_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1173__boxed_708_ = (leanh::lean_unbox(v___x_702_) as u8);
    v_res_709_ = l_Array_filterPairsM___redArg___lam__9(
        v___x_700_,
        v_next_701_,
        v___x_1173__boxed_708_,
        v_toPure_703_,
        v_snd_704_,
        v_fst_705_,
        v_next_706_,
        v_____x_707_,
    );
    leanh::lean_dec(v_next_706_);
    leanh::lean_dec(v_next_701_);
    leanh::lean_dec(v___x_700_);
    return v_res_709_;
}
pub unsafe fn l_Array_filterPairsM___redArg___lam__10(
    mut v___x_710_: *mut leanh::LeanObject,
    mut v_toPure_711_: *mut leanh::LeanObject,
    mut v___x_712_: *mut leanh::LeanObject,
    mut v_toBind_713_: *mut leanh::LeanObject,
    mut v___f_714_: *mut leanh::LeanObject,
    mut v_next_715_: *mut leanh::LeanObject,
    mut v_a_716_: *mut leanh::LeanObject,
    mut v_f_717_: *mut leanh::LeanObject,
    mut v___x_718_: u8,
    mut v_next_719_: *mut leanh::LeanObject,
    mut v_acc_720_: *mut leanh::LeanObject,
    mut v_h_721_: *mut leanh::LeanObject,
    mut v_G_722_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_723_: u8 = 0;
    let mut v___x_724_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_725_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_726_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_728_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_729_: u8 = 0;
    let mut v___f_730_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_732_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_733_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_734_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_735_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_736_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_738_: u8 = 0;
    let mut v___x_739_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_740_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_741_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_742_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_744_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_745_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_746_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_747_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_748_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_749_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_750_: u8 = 0;
    let mut v___x_751_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_752_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_753_: u8 = 0;
    let mut v___x_754_: u8 = 0;
    let mut v_isSharedCheck_755_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_723_ = lean_nat_dec_lt(v_next_719_, v___x_710_);
                if v___x_723_ == 0 {
                    leanh::lean_dec(v_G_722_);
                    leanh::lean_dec(v_next_719_);
                    leanh::lean_dec(v_f_717_);
                    leanh::lean_dec(v_next_715_);
                    leanh::lean_dec(v___f_714_);
                    leanh::lean_dec(v_toBind_713_);
                    leanh::lean_dec(v___x_712_);
                    v___x_724_ = leanh::lean_apply_2(
                        v_toPure_711_,
                        leanh::lean_box(0),
                        v_acc_720_,
                    );
                    return v___x_724_;
                } else {
                    v_fst_725_ = leanh::lean_ctor_get(v_acc_720_, 0);
                    v_snd_726_ = leanh::lean_ctor_get(v_acc_720_, 1);
                    v_isSharedCheck_755_ = (!leanh::lean_is_exclusive(v_acc_720_)) as u8;
                    if v_isSharedCheck_755_ == 0 {
                        v___x_728_ = v_acc_720_;
                        v_isShared_729_ = v_isSharedCheck_755_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_snd_726_);
                        leanh::lean_inc(v_fst_725_);
                        leanh::lean_dec(v_acc_720_);
                        v___x_728_ = leanh::lean_box(0);
                        v_isShared_729_ = v_isSharedCheck_755_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                leanh::lean_inc(v___x_712_);
                leanh::lean_inc_n(v_next_719_, 2);
                leanh::lean_inc_n(v_toPure_711_, 2);
                v___f_730_ = leanh::lean_alloc_closure(
                    l_Array_filterPairsM___redArg___lam__8___boxed as *mut core::ffi::c_void,
                    5,
                    4,
                );
                leanh::lean_closure_set(v___f_730_, 0, v_toPure_711_);
                leanh::lean_closure_set(v___f_730_, 1, v_next_719_);
                leanh::lean_closure_set(v___f_730_, 2, v___x_712_);
                leanh::lean_closure_set(v___f_730_, 3, v_G_722_);
                v___x_735_ = leanh::lean_box((v___x_723_) as usize);
                leanh::lean_inc(v_next_715_);
                leanh::lean_inc(v_fst_725_);
                leanh::lean_inc(v_snd_726_);
                v___f_736_ = leanh::lean_alloc_closure(
                    l_Array_filterPairsM___redArg___lam__9___boxed as *mut core::ffi::c_void,
                    8,
                    7,
                );
                leanh::lean_closure_set(v___f_736_, 0, v___x_712_);
                leanh::lean_closure_set(v___f_736_, 1, v_next_719_);
                leanh::lean_closure_set(v___f_736_, 2, v___x_735_);
                leanh::lean_closure_set(v___f_736_, 3, v_toPure_711_);
                leanh::lean_closure_set(v___f_736_, 4, v_snd_726_);
                leanh::lean_closure_set(v___f_736_, 5, v_fst_725_);
                leanh::lean_closure_set(v___f_736_, 6, v_next_715_);
                v___x_748_ = leanh::lean_box((v___x_718_) as usize);
                v___x_749_ = lean_array_get(v___x_748_, v_fst_725_, v_next_715_);
                leanh::lean_dec(v___x_748_);
                v___x_750_ = (leanh::lean_unbox(v___x_749_) as u8);
                if v___x_750_ == 0 {
                    leanh::lean_dec(v___x_749_);
                    v___x_751_ = leanh::lean_box((v___x_718_) as usize);
                    v___x_752_ = lean_array_get(v___x_751_, v_fst_725_, v_next_719_);
                    leanh::lean_dec(v___x_751_);
                    v___x_753_ = (leanh::lean_unbox(v___x_752_) as u8);
                    leanh::lean_dec(v___x_752_);
                    v___y_738_ = v___x_753_;
                    state = 3;
                    continue;
                } else {
                    v___x_754_ = (leanh::lean_unbox(v___x_749_) as u8);
                    leanh::lean_dec(v___x_749_);
                    v___y_738_ = v___x_754_;
                    state = 3;
                    continue;
                }
            }
            2 => {
                leanh::lean_inc(v_toBind_713_);
                v___x_733_ = leanh::lean_apply_4(
                    v_toBind_713_,
                    leanh::lean_box(0),
                    leanh::lean_box(0),
                    v___y_732_,
                    v___f_714_,
                );
                v___x_734_ = leanh::lean_apply_4(
                    v_toBind_713_,
                    leanh::lean_box(0),
                    leanh::lean_box(0),
                    v___x_733_,
                    v___f_730_,
                );
                return v___x_734_;
            }
            3 => {
                if v___y_738_ == 0 {
                    leanh::lean_del_object(v___x_728_);
                    leanh::lean_dec(v_snd_726_);
                    leanh::lean_dec(v_fst_725_);
                    leanh::lean_dec(v_toPure_711_);
                    v___x_739_ = lean_array_fget_borrowed(v_a_716_, v_next_715_);
                    leanh::lean_dec(v_next_715_);
                    v___x_740_ = lean_array_fget_borrowed(v_a_716_, v_next_719_);
                    leanh::lean_dec(v_next_719_);
                    leanh::lean_inc(v___x_740_);
                    leanh::lean_inc(v___x_739_);
                    v___x_741_ = leanh::lean_apply_2(v_f_717_, v___x_739_, v___x_740_);
                    leanh::lean_inc(v_toBind_713_);
                    v___x_742_ = leanh::lean_apply_4(
                        v_toBind_713_,
                        leanh::lean_box(0),
                        leanh::lean_box(0),
                        v___x_741_,
                        v___f_736_,
                    );
                    v___y_732_ = v___x_742_;
                    state = 2;
                    continue;
                } else {
                    leanh::lean_dec_ref(v___f_736_);
                    leanh::lean_dec(v_next_719_);
                    leanh::lean_dec(v_f_717_);
                    leanh::lean_dec(v_next_715_);
                    if v_isShared_729_ == 0 {
                        v___x_744_ = v___x_728_;
                        state = 4;
                        continue;
                    } else {
                        v_reuseFailAlloc_747_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_747_, 0, v_fst_725_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_747_, 1, v_snd_726_);
                        v___x_744_ = v_reuseFailAlloc_747_;
                        state = 4;
                        continue;
                    }
                }
            }
            4 => {
                v___x_745_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_745_, 0, v___x_744_);
                v___x_746_ = leanh::lean_apply_2(
                    v_toPure_711_,
                    leanh::lean_box(0),
                    v___x_745_,
                );
                v___y_732_ = v___x_746_;
                state = 2;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Array_filterPairsM___redArg___lam__10___boxed(
    mut v___x_756_: *mut leanh::LeanObject,
    mut v_toPure_757_: *mut leanh::LeanObject,
    mut v___x_758_: *mut leanh::LeanObject,
    mut v_toBind_759_: *mut leanh::LeanObject,
    mut v___f_760_: *mut leanh::LeanObject,
    mut v_next_761_: *mut leanh::LeanObject,
    mut v_a_762_: *mut leanh::LeanObject,
    mut v_f_763_: *mut leanh::LeanObject,
    mut v___x_764_: *mut leanh::LeanObject,
    mut v_next_765_: *mut leanh::LeanObject,
    mut v_acc_766_: *mut leanh::LeanObject,
    mut v_h_767_: *mut leanh::LeanObject,
    mut v_G_768_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1234__boxed_769_: u8 = 0;
    let mut v_res_770_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1234__boxed_769_ = (leanh::lean_unbox(v___x_764_) as u8);
    v_res_770_ = l_Array_filterPairsM___redArg___lam__10(
        v___x_756_,
        v_toPure_757_,
        v___x_758_,
        v_toBind_759_,
        v___f_760_,
        v_next_761_,
        v_a_762_,
        v_f_763_,
        v___x_1234__boxed_769_,
        v_next_765_,
        v_acc_766_,
        v_h_767_,
        v_G_768_,
    );
    leanh::lean_dec_ref(v_a_762_);
    leanh::lean_dec(v___x_756_);
    return v_res_770_;
}
pub unsafe fn l_Array_filterPairsM___redArg___lam__11(
    mut v___x_771_: *mut leanh::LeanObject,
    mut v_toPure_772_: *mut leanh::LeanObject,
    mut v_toBind_773_: *mut leanh::LeanObject,
    mut v___f_774_: *mut leanh::LeanObject,
    mut v_a_775_: *mut leanh::LeanObject,
    mut v_f_776_: *mut leanh::LeanObject,
    mut v___x_777_: u8,
    mut v___f_778_: *mut leanh::LeanObject,
    mut v___f_779_: *mut leanh::LeanObject,
    mut v_next_780_: *mut leanh::LeanObject,
    mut v_acc_781_: *mut leanh::LeanObject,
    mut v_h_782_: *mut leanh::LeanObject,
    mut v_G_783_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_784_: u8 = 0;
    let mut v___x_785_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_786_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_787_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_789_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_790_: u8 = 0;
    let mut v___f_791_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_792_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_793_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_794_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_795_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_797_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_798_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_799_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_800_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_801_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_802_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_803_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_784_ = lean_nat_dec_lt(v_next_780_, v___x_771_);
                if v___x_784_ == 0 {
                    leanh::lean_dec(v_G_783_);
                    leanh::lean_dec(v_next_780_);
                    leanh::lean_dec(v___f_779_);
                    leanh::lean_dec(v___f_778_);
                    leanh::lean_dec(v_f_776_);
                    leanh::lean_dec_ref(v_a_775_);
                    leanh::lean_dec(v___f_774_);
                    leanh::lean_dec(v_toBind_773_);
                    leanh::lean_dec(v___x_771_);
                    v___x_785_ = leanh::lean_apply_2(
                        v_toPure_772_,
                        leanh::lean_box(0),
                        v_acc_781_,
                    );
                    return v___x_785_;
                } else {
                    v_fst_786_ = leanh::lean_ctor_get(v_acc_781_, 0);
                    v_snd_787_ = leanh::lean_ctor_get(v_acc_781_, 1);
                    v_isSharedCheck_803_ = (!leanh::lean_is_exclusive(v_acc_781_)) as u8;
                    if v_isSharedCheck_803_ == 0 {
                        v___x_789_ = v_acc_781_;
                        v_isShared_790_ = v_isSharedCheck_803_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_snd_787_);
                        leanh::lean_inc(v_fst_786_);
                        leanh::lean_dec(v_acc_781_);
                        v___x_789_ = leanh::lean_box(0);
                        v_isShared_790_ = v_isSharedCheck_803_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                leanh::lean_inc_n(v_next_780_, 2);
                leanh::lean_inc(v_toPure_772_);
                v___f_791_ = leanh::lean_alloc_closure(
                    l_Array_filterPairsM___redArg___lam__7___boxed as *mut core::ffi::c_void,
                    4,
                    3,
                );
                leanh::lean_closure_set(v___f_791_, 0, v_toPure_772_);
                leanh::lean_closure_set(v___f_791_, 1, v_next_780_);
                leanh::lean_closure_set(v___f_791_, 2, v_G_783_);
                v___x_792_ = leanh::lean_unsigned_to_nat(1);
                v___x_793_ = leanh::lean_box((v___x_777_) as usize);
                leanh::lean_inc(v_toBind_773_);
                v___f_794_ = leanh::lean_alloc_closure(
                    l_Array_filterPairsM___redArg___lam__10___boxed as *mut core::ffi::c_void,
                    13,
                    9,
                );
                leanh::lean_closure_set(v___f_794_, 0, v___x_771_);
                leanh::lean_closure_set(v___f_794_, 1, v_toPure_772_);
                leanh::lean_closure_set(v___f_794_, 2, v___x_792_);
                leanh::lean_closure_set(v___f_794_, 3, v_toBind_773_);
                leanh::lean_closure_set(v___f_794_, 4, v___f_774_);
                leanh::lean_closure_set(v___f_794_, 5, v_next_780_);
                leanh::lean_closure_set(v___f_794_, 6, v_a_775_);
                leanh::lean_closure_set(v___f_794_, 7, v_f_776_);
                leanh::lean_closure_set(v___f_794_, 8, v___x_793_);
                v___x_795_ = lean_nat_add(v_next_780_, v___x_792_);
                leanh::lean_dec(v_next_780_);
                if v_isShared_790_ == 0 {
                    v___x_797_ = v___x_789_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_802_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_802_, 0, v_fst_786_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_802_, 1, v_snd_787_);
                    v___x_797_ = v_reuseFailAlloc_802_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_798_ = l_WellFounded_opaqueFix_u2083___redArg(
                    v___f_794_,
                    v___x_795_,
                    v___x_797_,
                    leanh::lean_box(0),
                );
                leanh::lean_inc_n(v_toBind_773_, 2);
                v___x_799_ = leanh::lean_apply_4(
                    v_toBind_773_,
                    leanh::lean_box(0),
                    leanh::lean_box(0),
                    v___x_798_,
                    v___f_778_,
                );
                v___x_800_ = leanh::lean_apply_4(
                    v_toBind_773_,
                    leanh::lean_box(0),
                    leanh::lean_box(0),
                    v___x_799_,
                    v___f_779_,
                );
                v___x_801_ = leanh::lean_apply_4(
                    v_toBind_773_,
                    leanh::lean_box(0),
                    leanh::lean_box(0),
                    v___x_800_,
                    v___f_791_,
                );
                return v___x_801_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Array_filterPairsM___redArg___lam__11___boxed(
    mut v___x_804_: *mut leanh::LeanObject,
    mut v_toPure_805_: *mut leanh::LeanObject,
    mut v_toBind_806_: *mut leanh::LeanObject,
    mut v___f_807_: *mut leanh::LeanObject,
    mut v_a_808_: *mut leanh::LeanObject,
    mut v_f_809_: *mut leanh::LeanObject,
    mut v___x_810_: *mut leanh::LeanObject,
    mut v___f_811_: *mut leanh::LeanObject,
    mut v___f_812_: *mut leanh::LeanObject,
    mut v_next_813_: *mut leanh::LeanObject,
    mut v_acc_814_: *mut leanh::LeanObject,
    mut v_h_815_: *mut leanh::LeanObject,
    mut v_G_816_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1307__boxed_817_: u8 = 0;
    let mut v_res_818_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1307__boxed_817_ = (leanh::lean_unbox(v___x_810_) as u8);
    v_res_818_ = l_Array_filterPairsM___redArg___lam__11(
        v___x_804_,
        v_toPure_805_,
        v_toBind_806_,
        v___f_807_,
        v_a_808_,
        v_f_809_,
        v___x_1307__boxed_817_,
        v___f_811_,
        v___f_812_,
        v_next_813_,
        v_acc_814_,
        v_h_815_,
        v_G_816_,
    );
    return v_res_818_;
}
pub unsafe fn l_Array_filterPairsM___redArg(
    mut v_inst_819_: *mut leanh::LeanObject,
    mut v_a_820_: *mut leanh::LeanObject,
    mut v_f_821_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_toApplicative_822_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_823_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_825_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_826_: u8 = 0;
    let mut v_toPure_827_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_828_: u8 = 0;
    let mut v___x_829_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_830_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_removed_831_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_832_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_833_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_834_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_835_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_836_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_837_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_838_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_839_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_840_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_842_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_843_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_844_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_845_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_846_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_toApplicative_822_ = leanh::lean_ctor_get(v_inst_819_, 0);
                v_toBind_823_ = leanh::lean_ctor_get(v_inst_819_, 1);
                v_isSharedCheck_846_ = (!leanh::lean_is_exclusive(v_inst_819_)) as u8;
                if v_isSharedCheck_846_ == 0 {
                    v___x_825_ = v_inst_819_;
                    v_isShared_826_ = v_isSharedCheck_846_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_toBind_823_);
                    leanh::lean_inc(v_toApplicative_822_);
                    leanh::lean_dec(v_inst_819_);
                    v___x_825_ = leanh::lean_box(0);
                    v_isShared_826_ = v_isSharedCheck_846_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_toPure_827_ = leanh::lean_ctor_get(v_toApplicative_822_, 1);
                leanh::lean_inc_n(v_toPure_827_, 6);
                leanh::lean_dec_ref(v_toApplicative_822_);
                v___x_828_ = 0;
                v___x_829_ = lean_array_get_size(v_a_820_);
                v___x_830_ = leanh::lean_box((v___x_828_) as usize);
                v_removed_831_ = lean_mk_array(v___x_829_, v___x_830_);
                v___f_832_ = leanh::lean_alloc_closure(
                    l_Array_filterPairsM___redArg___lam__0 as *mut core::ffi::c_void,
                    2,
                    1,
                );
                leanh::lean_closure_set(v___f_832_, 0, v_toPure_827_);
                v___f_833_ = leanh::lean_alloc_closure(
                    l_Array_filterPairsM___redArg___lam__2 as *mut core::ffi::c_void,
                    2,
                    1,
                );
                leanh::lean_closure_set(v___f_833_, 0, v_toPure_827_);
                v___f_834_ = leanh::lean_alloc_closure(
                    l_Array_filterPairsM___redArg___lam__1 as *mut core::ffi::c_void,
                    2,
                    1,
                );
                leanh::lean_closure_set(v___f_834_, 0, v_toPure_827_);
                v___x_835_ = leanh::lean_box((v___x_828_) as usize);
                leanh::lean_inc_ref(v_a_820_);
                leanh::lean_inc_n(v_toBind_823_, 2);
                v___f_836_ = leanh::lean_alloc_closure(
                    l_Array_filterPairsM___redArg___lam__5___boxed as *mut core::ffi::c_void,
                    8,
                    7,
                );
                leanh::lean_closure_set(v___f_836_, 0, v___x_829_);
                leanh::lean_closure_set(v___f_836_, 1, v_toPure_827_);
                leanh::lean_closure_set(v___f_836_, 2, v_toBind_823_);
                leanh::lean_closure_set(v___f_836_, 3, v___f_833_);
                leanh::lean_closure_set(v___f_836_, 4, v___x_835_);
                leanh::lean_closure_set(v___f_836_, 5, v_a_820_);
                leanh::lean_closure_set(v___f_836_, 6, v___f_834_);
                v___f_837_ = leanh::lean_alloc_closure(
                    l_Array_filterPairsM___redArg___lam__6 as *mut core::ffi::c_void,
                    2,
                    1,
                );
                leanh::lean_closure_set(v___f_837_, 0, v_toPure_827_);
                v___x_838_ = leanh::lean_box((v___x_828_) as usize);
                leanh::lean_inc_ref(v___f_832_);
                v___f_839_ = leanh::lean_alloc_closure(
                    l_Array_filterPairsM___redArg___lam__11___boxed as *mut core::ffi::c_void,
                    13,
                    9,
                );
                leanh::lean_closure_set(v___f_839_, 0, v___x_829_);
                leanh::lean_closure_set(v___f_839_, 1, v_toPure_827_);
                leanh::lean_closure_set(v___f_839_, 2, v_toBind_823_);
                leanh::lean_closure_set(v___f_839_, 3, v___f_832_);
                leanh::lean_closure_set(v___f_839_, 4, v_a_820_);
                leanh::lean_closure_set(v___f_839_, 5, v_f_821_);
                leanh::lean_closure_set(v___f_839_, 6, v___x_838_);
                leanh::lean_closure_set(v___f_839_, 7, v___f_837_);
                leanh::lean_closure_set(v___f_839_, 8, v___f_832_);
                v___x_840_ = leanh::lean_unsigned_to_nat(0);
                if v_isShared_826_ == 0 {
                    leanh::lean_ctor_set(v___x_825_, 1, v___x_840_);
                    leanh::lean_ctor_set(v___x_825_, 0, v_removed_831_);
                    v___x_842_ = v___x_825_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_845_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_845_, 0, v_removed_831_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_845_, 1, v___x_840_);
                    v___x_842_ = v_reuseFailAlloc_845_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_843_ = l_WellFounded_opaqueFix_u2083___redArg(
                    v___f_839_,
                    v___x_840_,
                    v___x_842_,
                    leanh::lean_box(0),
                );
                v___x_844_ = leanh::lean_apply_4(
                    v_toBind_823_,
                    leanh::lean_box(0),
                    leanh::lean_box(0),
                    v___x_843_,
                    v___f_836_,
                );
                return v___x_844_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Array_filterPairsM(
    mut v_m_847_: *mut leanh::LeanObject,
    mut v_inst_848_: *mut leanh::LeanObject,
    mut v_00_u03b1_849_: *mut leanh::LeanObject,
    mut v_a_850_: *mut leanh::LeanObject,
    mut v_f_851_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_852_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_852_ = l_Array_filterPairsM___redArg(v_inst_848_, v_a_850_, v_f_851_);
    return v___x_852_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Array_mask_spec__0___redArg(
    mut v_as_853_: *mut leanh::LeanObject,
    mut v_sz_854_: usize,
    mut v_i_855_: usize,
    mut v_b_856_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_a_858_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_859_: usize = 0;
    let mut v___x_860_: usize = 0;
    let mut v___x_862_: u8 = 0;
    let mut v_snd_863_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_864_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_866_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_867_: u8 = 0;
    let mut v_array_868_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_start_869_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_stop_870_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_871_: u8 = 0;
    let mut v___x_873_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_874_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_876_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_877_: u8 = 0;
    let mut v_a_878_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_879_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_880_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_881_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_883_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_884_: u8 = 0;
    let mut v___x_886_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_887_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_888_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_890_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_891_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_892_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_893_: u8 = 0;
    let mut v_unused_894_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_895_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_896_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_897_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_862_ = lean_usize_dec_lt(v_i_855_, v_sz_854_);
                if v___x_862_ == 0 {
                    return v_b_856_;
                } else {
                    v_snd_863_ = leanh::lean_ctor_get(v_b_856_, 1);
                    v_fst_864_ = leanh::lean_ctor_get(v_b_856_, 0);
                    v_isSharedCheck_897_ = (!leanh::lean_is_exclusive(v_b_856_)) as u8;
                    if v_isSharedCheck_897_ == 0 {
                        v___x_866_ = v_b_856_;
                        v_isShared_867_ = v_isSharedCheck_897_;
                        state = 2;
                        continue;
                    } else {
                        leanh::lean_inc(v_snd_863_);
                        leanh::lean_inc(v_fst_864_);
                        leanh::lean_dec(v_b_856_);
                        v___x_866_ = leanh::lean_box(0);
                        v_isShared_867_ = v_isSharedCheck_897_;
                        state = 2;
                        continue;
                    }
                }
            }
            1 => {
                v___x_859_ = 1usize;
                v___x_860_ = lean_usize_add(v_i_855_, v___x_859_);
                v_i_855_ = v___x_860_;
                v_b_856_ = v_a_858_;
                state = 0;
                continue;
            }
            2 => {
                v_array_868_ = leanh::lean_ctor_get(v_snd_863_, 0);
                v_start_869_ = leanh::lean_ctor_get(v_snd_863_, 1);
                v_stop_870_ = leanh::lean_ctor_get(v_snd_863_, 2);
                v___x_871_ = lean_nat_dec_lt(v_start_869_, v_stop_870_);
                if v___x_871_ == 0 {
                    if v_isShared_867_ == 0 {
                        v___x_873_ = v___x_866_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_874_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_874_, 0, v_fst_864_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_874_, 1, v_snd_863_);
                        v___x_873_ = v_reuseFailAlloc_874_;
                        state = 3;
                        continue;
                    }
                } else {
                    leanh::lean_inc(v_stop_870_);
                    leanh::lean_inc(v_start_869_);
                    leanh::lean_inc_ref(v_array_868_);
                    v_isSharedCheck_893_ = (!leanh::lean_is_exclusive(v_snd_863_)) as u8;
                    if v_isSharedCheck_893_ == 0 {
                        v_unused_894_ = leanh::lean_ctor_get(v_snd_863_, 2);
                        leanh::lean_dec(v_unused_894_);
                        v_unused_895_ = leanh::lean_ctor_get(v_snd_863_, 1);
                        leanh::lean_dec(v_unused_895_);
                        v_unused_896_ = leanh::lean_ctor_get(v_snd_863_, 0);
                        leanh::lean_dec(v_unused_896_);
                        v___x_876_ = v_snd_863_;
                        v_isShared_877_ = v_isSharedCheck_893_;
                        state = 4;
                        continue;
                    } else {
                        leanh::lean_dec(v_snd_863_);
                        v___x_876_ = leanh::lean_box(0);
                        v_isShared_877_ = v_isSharedCheck_893_;
                        state = 4;
                        continue;
                    }
                }
            }
            3 => {
                return v___x_873_;
            }
            4 => {
                v_a_878_ = lean_array_uget_borrowed(v_as_853_, v_i_855_);
                v___x_879_ = lean_array_fget(v_array_868_, v_start_869_);
                v___x_880_ = leanh::lean_unsigned_to_nat(1);
                v___x_881_ = lean_nat_add(v_start_869_, v___x_880_);
                leanh::lean_dec(v_start_869_);
                if v_isShared_877_ == 0 {
                    leanh::lean_ctor_set(v___x_876_, 1, v___x_881_);
                    v___x_883_ = v___x_876_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_892_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_892_, 0, v_array_868_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_892_, 1, v___x_881_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_892_, 2, v_stop_870_);
                    v___x_883_ = v_reuseFailAlloc_892_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v___x_884_ = (leanh::lean_unbox(v_a_878_) as u8);
                if v___x_884_ == 0 {
                    leanh::lean_dec(v___x_879_);
                    if v_isShared_867_ == 0 {
                        leanh::lean_ctor_set(v___x_866_, 1, v___x_883_);
                        v___x_886_ = v___x_866_;
                        state = 6;
                        continue;
                    } else {
                        v_reuseFailAlloc_887_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_887_, 0, v_fst_864_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_887_, 1, v___x_883_);
                        v___x_886_ = v_reuseFailAlloc_887_;
                        state = 6;
                        continue;
                    }
                } else {
                    v___x_888_ = lean_array_push(v_fst_864_, v___x_879_);
                    if v_isShared_867_ == 0 {
                        leanh::lean_ctor_set(v___x_866_, 1, v___x_883_);
                        leanh::lean_ctor_set(v___x_866_, 0, v___x_888_);
                        v___x_890_ = v___x_866_;
                        state = 7;
                        continue;
                    } else {
                        v_reuseFailAlloc_891_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_891_, 0, v___x_888_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_891_, 1, v___x_883_);
                        v___x_890_ = v_reuseFailAlloc_891_;
                        state = 7;
                        continue;
                    }
                }
            }
            6 => {
                v_a_858_ = v___x_886_;
                state = 1;
                continue;
            }
            7 => {
                v_a_858_ = v___x_890_;
                state = 1;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Array_mask_spec__0___redArg___boxed(
    mut v_as_898_: *mut leanh::LeanObject,
    mut v_sz_899_: *mut leanh::LeanObject,
    mut v_i_900_: *mut leanh::LeanObject,
    mut v_b_901_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_sz_boxed_902_: usize = 0;
    let mut v_i_boxed_903_: usize = 0;
    let mut v_res_904_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_902_ = leanh::lean_unbox_usize(v_sz_899_);
    leanh::lean_dec(v_sz_899_);
    v_i_boxed_903_ = leanh::lean_unbox_usize(v_i_900_);
    leanh::lean_dec(v_i_900_);
    v_res_904_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Array_mask_spec__0___redArg(v_as_898_, v_sz_boxed_902_, v_i_boxed_903_, v_b_901_);
    leanh::lean_dec_ref(v_as_898_);
    return v_res_904_;
}
pub unsafe fn l_Array_mask___redArg(
    mut v_mask_907_: *mut leanh::LeanObject,
    mut v_xs_908_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_909_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ys_910_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_911_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_912_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_913_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_914_: usize = 0;
    let mut v___x_915_: usize = 0;
    let mut v___x_916_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_917_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_909_ = leanh::lean_unsigned_to_nat(0);
    v_ys_910_ = l_Array_mask___redArg___closed__0;
    v___x_911_ = lean_array_get_size(v_xs_908_);
    v___x_912_ = l_Array_toSubarray___redArg(v_xs_908_, v___x_909_, v___x_911_);
    v___x_913_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_913_, 0, v_ys_910_);
    leanh::lean_ctor_set(v___x_913_, 1, v___x_912_);
    v_sz_914_ = lean_array_size(v_mask_907_);
    v___x_915_ = 0usize;
    v___x_916_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Array_mask_spec__0___redArg(v_mask_907_, v_sz_914_, v___x_915_, v___x_913_);
    v_fst_917_ = leanh::lean_ctor_get(v___x_916_, 0);
    leanh::lean_inc(v_fst_917_);
    leanh::lean_dec_ref(v___x_916_);
    return v_fst_917_;
}
pub unsafe fn l_Array_mask___redArg___boxed(
    mut v_mask_918_: *mut leanh::LeanObject,
    mut v_xs_919_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_920_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_920_ = l_Array_mask___redArg(v_mask_918_, v_xs_919_);
    leanh::lean_dec_ref(v_mask_918_);
    return v_res_920_;
}
pub unsafe fn l_Array_mask(
    mut v_00_u03b1_921_: *mut leanh::LeanObject,
    mut v_mask_922_: *mut leanh::LeanObject,
    mut v_xs_923_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_924_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_924_ = l_Array_mask___redArg(v_mask_922_, v_xs_923_);
    return v___x_924_;
}
pub unsafe fn l_Array_mask___boxed(
    mut v_00_u03b1_925_: *mut leanh::LeanObject,
    mut v_mask_926_: *mut leanh::LeanObject,
    mut v_xs_927_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_928_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_928_ = l_Array_mask(v_00_u03b1_925_, v_mask_926_, v_xs_927_);
    leanh::lean_dec_ref(v_mask_926_);
    return v_res_928_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Array_mask_spec__0(
    mut v_00_u03b1_929_: *mut leanh::LeanObject,
    mut v_as_930_: *mut leanh::LeanObject,
    mut v_sz_931_: usize,
    mut v_i_932_: usize,
    mut v_b_933_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_934_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_934_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Array_mask_spec__0___redArg(v_as_930_, v_sz_931_, v_i_932_, v_b_933_);
    return v___x_934_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Array_mask_spec__0___boxed(
    mut v_00_u03b1_935_: *mut leanh::LeanObject,
    mut v_as_936_: *mut leanh::LeanObject,
    mut v_sz_937_: *mut leanh::LeanObject,
    mut v_i_938_: *mut leanh::LeanObject,
    mut v_b_939_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_sz_boxed_940_: usize = 0;
    let mut v_i_boxed_941_: usize = 0;
    let mut v_res_942_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_940_ = leanh::lean_unbox_usize(v_sz_937_);
    leanh::lean_dec(v_sz_937_);
    v_i_boxed_941_ = leanh::lean_unbox_usize(v_i_938_);
    leanh::lean_dec(v_i_938_);
    v_res_942_ =
        l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Array_mask_spec__0(
            v_00_u03b1_935_,
            v_as_936_,
            v_sz_boxed_940_,
            v_i_boxed_941_,
            v_b_939_,
        );
    leanh::lean_dec_ref(v_as_936_);
    return v_res_942_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Array_zipMasked_spec__0___redArg(
    mut v_xs_943_: *mut leanh::LeanObject,
    mut v_ys_944_: *mut leanh::LeanObject,
    mut v_as_945_: *mut leanh::LeanObject,
    mut v_sz_946_: usize,
    mut v_i_947_: usize,
    mut v_b_948_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_a_950_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_951_: usize = 0;
    let mut v___x_952_: usize = 0;
    let mut v___x_954_: u8 = 0;
    let mut v_snd_955_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_956_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_958_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_959_: u8 = 0;
    let mut v_fst_960_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_961_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_963_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_964_: u8 = 0;
    let mut v_a_965_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_966_: u8 = 0;
    let mut v___x_967_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_968_: u8 = 0;
    let mut v___x_970_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_972_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_973_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_974_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_975_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_976_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_977_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_978_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_980_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_982_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_983_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_984_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_985_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_986_: u8 = 0;
    let mut v___x_988_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_990_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_991_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_992_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_993_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_994_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_995_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_996_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_998_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1000_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1001_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1002_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1003_: u8 = 0;
    let mut v_isSharedCheck_1004_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_954_ = lean_usize_dec_lt(v_i_947_, v_sz_946_);
                if v___x_954_ == 0 {
                    return v_b_948_;
                } else {
                    v_snd_955_ = leanh::lean_ctor_get(v_b_948_, 1);
                    v_fst_956_ = leanh::lean_ctor_get(v_b_948_, 0);
                    v_isSharedCheck_1004_ = (!leanh::lean_is_exclusive(v_b_948_)) as u8;
                    if v_isSharedCheck_1004_ == 0 {
                        v___x_958_ = v_b_948_;
                        v_isShared_959_ = v_isSharedCheck_1004_;
                        state = 2;
                        continue;
                    } else {
                        leanh::lean_inc(v_snd_955_);
                        leanh::lean_inc(v_fst_956_);
                        leanh::lean_dec(v_b_948_);
                        v___x_958_ = leanh::lean_box(0);
                        v_isShared_959_ = v_isSharedCheck_1004_;
                        state = 2;
                        continue;
                    }
                }
            }
            1 => {
                v___x_951_ = 1usize;
                v___x_952_ = lean_usize_add(v_i_947_, v___x_951_);
                v_i_947_ = v___x_952_;
                v_b_948_ = v_a_950_;
                state = 0;
                continue;
            }
            2 => {
                v_fst_960_ = leanh::lean_ctor_get(v_snd_955_, 0);
                v_snd_961_ = leanh::lean_ctor_get(v_snd_955_, 1);
                v_isSharedCheck_1003_ = (!leanh::lean_is_exclusive(v_snd_955_)) as u8;
                if v_isSharedCheck_1003_ == 0 {
                    v___x_963_ = v_snd_955_;
                    v_isShared_964_ = v_isSharedCheck_1003_;
                    state = 3;
                    continue;
                } else {
                    leanh::lean_inc(v_snd_961_);
                    leanh::lean_inc(v_fst_960_);
                    leanh::lean_dec(v_snd_955_);
                    v___x_963_ = leanh::lean_box(0);
                    v_isShared_964_ = v_isSharedCheck_1003_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v_a_965_ = lean_array_uget_borrowed(v_as_945_, v_i_947_);
                v___x_966_ = (leanh::lean_unbox(v_a_965_) as u8);
                if v___x_966_ == 0 {
                    v___x_967_ = lean_array_get_size(v_xs_943_);
                    v___x_968_ = lean_nat_dec_lt(v_fst_956_, v___x_967_);
                    if v___x_968_ == 0 {
                        if v_isShared_964_ == 0 {
                            v___x_970_ = v___x_963_;
                            state = 4;
                            continue;
                        } else {
                            v_reuseFailAlloc_974_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                            leanh::lean_ctor_set(v_reuseFailAlloc_974_, 0, v_fst_960_);
                            leanh::lean_ctor_set(v_reuseFailAlloc_974_, 1, v_snd_961_);
                            v___x_970_ = v_reuseFailAlloc_974_;
                            state = 4;
                            continue;
                        }
                    } else {
                        v___x_975_ = lean_array_fget_borrowed(v_xs_943_, v_fst_956_);
                        leanh::lean_inc(v___x_975_);
                        v___x_976_ = lean_array_push(v_snd_961_, v___x_975_);
                        v___x_977_ = leanh::lean_unsigned_to_nat(1);
                        v___x_978_ = lean_nat_add(v_fst_956_, v___x_977_);
                        leanh::lean_dec(v_fst_956_);
                        if v_isShared_964_ == 0 {
                            leanh::lean_ctor_set(v___x_963_, 1, v___x_976_);
                            v___x_980_ = v___x_963_;
                            state = 6;
                            continue;
                        } else {
                            v_reuseFailAlloc_984_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                            leanh::lean_ctor_set(v_reuseFailAlloc_984_, 0, v_fst_960_);
                            leanh::lean_ctor_set(v_reuseFailAlloc_984_, 1, v___x_976_);
                            v___x_980_ = v_reuseFailAlloc_984_;
                            state = 6;
                            continue;
                        }
                    }
                } else {
                    v___x_985_ = lean_array_get_size(v_ys_944_);
                    v___x_986_ = lean_nat_dec_lt(v_fst_960_, v___x_985_);
                    if v___x_986_ == 0 {
                        if v_isShared_964_ == 0 {
                            v___x_988_ = v___x_963_;
                            state = 8;
                            continue;
                        } else {
                            v_reuseFailAlloc_992_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                            leanh::lean_ctor_set(v_reuseFailAlloc_992_, 0, v_fst_960_);
                            leanh::lean_ctor_set(v_reuseFailAlloc_992_, 1, v_snd_961_);
                            v___x_988_ = v_reuseFailAlloc_992_;
                            state = 8;
                            continue;
                        }
                    } else {
                        v___x_993_ = lean_array_fget_borrowed(v_ys_944_, v_fst_960_);
                        leanh::lean_inc(v___x_993_);
                        v___x_994_ = lean_array_push(v_snd_961_, v___x_993_);
                        v___x_995_ = leanh::lean_unsigned_to_nat(1);
                        v___x_996_ = lean_nat_add(v_fst_960_, v___x_995_);
                        leanh::lean_dec(v_fst_960_);
                        if v_isShared_964_ == 0 {
                            leanh::lean_ctor_set(v___x_963_, 1, v___x_994_);
                            leanh::lean_ctor_set(v___x_963_, 0, v___x_996_);
                            v___x_998_ = v___x_963_;
                            state = 10;
                            continue;
                        } else {
                            v_reuseFailAlloc_1002_ =
                                leanh::lean_alloc_ctor(0, 2, (0) as u32);
                            leanh::lean_ctor_set(v_reuseFailAlloc_1002_, 0, v___x_996_);
                            leanh::lean_ctor_set(v_reuseFailAlloc_1002_, 1, v___x_994_);
                            v___x_998_ = v_reuseFailAlloc_1002_;
                            state = 10;
                            continue;
                        }
                    }
                }
            }
            4 => {
                if v_isShared_959_ == 0 {
                    leanh::lean_ctor_set(v___x_958_, 1, v___x_970_);
                    v___x_972_ = v___x_958_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_973_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_973_, 0, v_fst_956_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_973_, 1, v___x_970_);
                    v___x_972_ = v_reuseFailAlloc_973_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v_a_950_ = v___x_972_;
                state = 1;
                continue;
            }
            6 => {
                if v_isShared_959_ == 0 {
                    leanh::lean_ctor_set(v___x_958_, 1, v___x_980_);
                    leanh::lean_ctor_set(v___x_958_, 0, v___x_978_);
                    v___x_982_ = v___x_958_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_983_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_983_, 0, v___x_978_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_983_, 1, v___x_980_);
                    v___x_982_ = v_reuseFailAlloc_983_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                v_a_950_ = v___x_982_;
                state = 1;
                continue;
            }
            8 => {
                if v_isShared_959_ == 0 {
                    leanh::lean_ctor_set(v___x_958_, 1, v___x_988_);
                    v___x_990_ = v___x_958_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_991_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_991_, 0, v_fst_956_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_991_, 1, v___x_988_);
                    v___x_990_ = v_reuseFailAlloc_991_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                v_a_950_ = v___x_990_;
                state = 1;
                continue;
            }
            10 => {
                if v_isShared_959_ == 0 {
                    leanh::lean_ctor_set(v___x_958_, 1, v___x_998_);
                    v___x_1000_ = v___x_958_;
                    state = 11;
                    continue;
                } else {
                    v_reuseFailAlloc_1001_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1001_, 0, v_fst_956_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1001_, 1, v___x_998_);
                    v___x_1000_ = v_reuseFailAlloc_1001_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                v_a_950_ = v___x_1000_;
                state = 1;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Array_zipMasked_spec__0___redArg___boxed(
    mut v_xs_1005_: *mut leanh::LeanObject,
    mut v_ys_1006_: *mut leanh::LeanObject,
    mut v_as_1007_: *mut leanh::LeanObject,
    mut v_sz_1008_: *mut leanh::LeanObject,
    mut v_i_1009_: *mut leanh::LeanObject,
    mut v_b_1010_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_sz_boxed_1011_: usize = 0;
    let mut v_i_boxed_1012_: usize = 0;
    let mut v_res_1013_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_1011_ = leanh::lean_unbox_usize(v_sz_1008_);
    leanh::lean_dec(v_sz_1008_);
    v_i_boxed_1012_ = leanh::lean_unbox_usize(v_i_1009_);
    leanh::lean_dec(v_i_1009_);
    v_res_1013_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Array_zipMasked_spec__0___redArg(v_xs_1005_, v_ys_1006_, v_as_1007_, v_sz_boxed_1011_, v_i_boxed_1012_, v_b_1010_);
    leanh::lean_dec_ref(v_as_1007_);
    leanh::lean_dec_ref(v_ys_1006_);
    leanh::lean_dec_ref(v_xs_1005_);
    return v_res_1013_;
}
pub unsafe fn l_Array_zipMasked___redArg(
    mut v_mask_1020_: *mut leanh::LeanObject,
    mut v_xs_1021_: *mut leanh::LeanObject,
    mut v_ys_1022_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1023_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_1024_: usize = 0;
    let mut v___x_1025_: usize = 0;
    let mut v___x_1026_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1027_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1028_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1023_ = l_Array_zipMasked___redArg___closed__1;
    v_sz_1024_ = lean_array_size(v_mask_1020_);
    v___x_1025_ = 0usize;
    v___x_1026_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Array_zipMasked_spec__0___redArg(v_xs_1021_, v_ys_1022_, v_mask_1020_, v_sz_1024_, v___x_1025_, v___x_1023_);
    v_snd_1027_ = leanh::lean_ctor_get(v___x_1026_, 1);
    leanh::lean_inc(v_snd_1027_);
    leanh::lean_dec_ref(v___x_1026_);
    v_snd_1028_ = leanh::lean_ctor_get(v_snd_1027_, 1);
    leanh::lean_inc(v_snd_1028_);
    leanh::lean_dec(v_snd_1027_);
    return v_snd_1028_;
}
pub unsafe fn l_Array_zipMasked___redArg___boxed(
    mut v_mask_1029_: *mut leanh::LeanObject,
    mut v_xs_1030_: *mut leanh::LeanObject,
    mut v_ys_1031_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1032_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1032_ = l_Array_zipMasked___redArg(v_mask_1029_, v_xs_1030_, v_ys_1031_);
    leanh::lean_dec_ref(v_ys_1031_);
    leanh::lean_dec_ref(v_xs_1030_);
    leanh::lean_dec_ref(v_mask_1029_);
    return v_res_1032_;
}
pub unsafe fn l_Array_zipMasked(
    mut v_00_u03b1_1033_: *mut leanh::LeanObject,
    mut v_mask_1034_: *mut leanh::LeanObject,
    mut v_xs_1035_: *mut leanh::LeanObject,
    mut v_ys_1036_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1037_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1037_ = l_Array_zipMasked___redArg(v_mask_1034_, v_xs_1035_, v_ys_1036_);
    return v___x_1037_;
}
pub unsafe fn l_Array_zipMasked___boxed(
    mut v_00_u03b1_1038_: *mut leanh::LeanObject,
    mut v_mask_1039_: *mut leanh::LeanObject,
    mut v_xs_1040_: *mut leanh::LeanObject,
    mut v_ys_1041_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1042_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1042_ = l_Array_zipMasked(v_00_u03b1_1038_, v_mask_1039_, v_xs_1040_, v_ys_1041_);
    leanh::lean_dec_ref(v_ys_1041_);
    leanh::lean_dec_ref(v_xs_1040_);
    leanh::lean_dec_ref(v_mask_1039_);
    return v_res_1042_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Array_zipMasked_spec__0(
    mut v_00_u03b1_1043_: *mut leanh::LeanObject,
    mut v_xs_1044_: *mut leanh::LeanObject,
    mut v_ys_1045_: *mut leanh::LeanObject,
    mut v_as_1046_: *mut leanh::LeanObject,
    mut v_sz_1047_: usize,
    mut v_i_1048_: usize,
    mut v_b_1049_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1050_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1050_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Array_zipMasked_spec__0___redArg(v_xs_1044_, v_ys_1045_, v_as_1046_, v_sz_1047_, v_i_1048_, v_b_1049_);
    return v___x_1050_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Array_zipMasked_spec__0___boxed(
    mut v_00_u03b1_1051_: *mut leanh::LeanObject,
    mut v_xs_1052_: *mut leanh::LeanObject,
    mut v_ys_1053_: *mut leanh::LeanObject,
    mut v_as_1054_: *mut leanh::LeanObject,
    mut v_sz_1055_: *mut leanh::LeanObject,
    mut v_i_1056_: *mut leanh::LeanObject,
    mut v_b_1057_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_sz_boxed_1058_: usize = 0;
    let mut v_i_boxed_1059_: usize = 0;
    let mut v_res_1060_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_1058_ = leanh::lean_unbox_usize(v_sz_1055_);
    leanh::lean_dec(v_sz_1055_);
    v_i_boxed_1059_ = leanh::lean_unbox_usize(v_i_1056_);
    leanh::lean_dec(v_i_1056_);
    v_res_1060_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Array_zipMasked_spec__0(v_00_u03b1_1051_, v_xs_1052_, v_ys_1053_, v_as_1054_, v_sz_boxed_1058_, v_i_boxed_1059_, v_b_1057_);
    leanh::lean_dec_ref(v_as_1054_);
    leanh::lean_dec_ref(v_ys_1053_);
    leanh::lean_dec_ref(v_xs_1052_);
    return v_res_1060_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Data_Array(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Init_Data_Stream(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Range_Polymorphic_Nat(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Range_Polymorphic_Iterators(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Data_Array(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_meta_initialized = true;
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lean_Data_Array(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Init_Data_Stream(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Range_Polymorphic_Nat(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Range_Polymorphic_Iterators(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Data_Array(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_Data_Array(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return initialize_Lean_Data_Array(builtin);
}