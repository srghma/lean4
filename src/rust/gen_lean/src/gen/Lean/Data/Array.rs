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
pub static l_Array_mask___redArg___closed__0_value: crate::leanh::LeanArrayObject<0> =
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
static mut l_Array_mask___redArg___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Array_mask___redArg___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_Array_zipMasked___redArg___closed__0_value: crate::leanh::LeanCtorObject<2> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 0,
        },
        m_objs: [
            (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Array_mask___redArg___closed__0_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Array_zipMasked___redArg___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Array_zipMasked___redArg___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Array_zipMasked___redArg___closed__1_value: crate::leanh::LeanCtorObject<2> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 0,
        },
        m_objs: [
            (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Array_zipMasked___redArg___closed__0_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Array_zipMasked___redArg___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Array_zipMasked___redArg___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub unsafe fn l_Array_filterPairsM___redArg___lam__0(
    mut v_toPure_531_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_532_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_533_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_533_ = crate::leanh::lean_apply_2(
        v_toPure_531_,
        crate::leanh::lean_box(0),
        v_____do__lift_532_,
    );
    return v___x_533_;
}
pub unsafe fn l_Array_filterPairsM___redArg___lam__2(
    mut v_toPure_534_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_535_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_536_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_536_ = crate::leanh::lean_apply_2(
        v_toPure_534_,
        crate::leanh::lean_box(0),
        v_____do__lift_535_,
    );
    return v___x_536_;
}
pub unsafe fn l_Array_filterPairsM___redArg___lam__1(
    mut v_toPure_537_: *mut crate::leanh::LeanObject,
    mut v_____s_538_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_539_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_539_ = crate::leanh::lean_apply_2(v_toPure_537_, crate::leanh::lean_box(0), v_____s_538_);
    return v___x_539_;
}
pub unsafe fn l_Array_filterPairsM___redArg___lam__3(
    mut v_toPure_540_: *mut crate::leanh::LeanObject,
    mut v_next_541_: *mut crate::leanh::LeanObject,
    mut v_G_542_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_543_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_____do__lift_543_) == 0 {
        let mut v_a_544_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_545_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_G_542_);
        v_a_544_ = crate::leanh::lean_ctor_get(v_____do__lift_543_, 0);
        crate::leanh::lean_inc(v_a_544_);
        crate::leanh::lean_dec_ref_known(v_____do__lift_543_, 1);
        v___x_545_ = crate::leanh::lean_apply_2(v_toPure_540_, crate::leanh::lean_box(0), v_a_544_);
        return v___x_545_;
    } else {
        let mut v_a_546_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_547_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_548_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_549_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_toPure_540_);
        v_a_546_ = crate::leanh::lean_ctor_get(v_____do__lift_543_, 0);
        crate::leanh::lean_inc(v_a_546_);
        crate::leanh::lean_dec_ref_known(v_____do__lift_543_, 1);
        v___x_547_ = crate::leanh::lean_unsigned_to_nat(1);
        v___x_548_ = lean_nat_add(v_next_541_, v___x_547_);
        v___x_549_ = crate::leanh::lean_apply_4(
            v_G_542_,
            v___x_548_,
            v_a_546_,
            crate::leanh::lean_box(0),
            crate::leanh::lean_box(0),
        );
        return v___x_549_;
    }
}
pub unsafe fn l_Array_filterPairsM___redArg___lam__3___boxed(
    mut v_toPure_550_: *mut crate::leanh::LeanObject,
    mut v_next_551_: *mut crate::leanh::LeanObject,
    mut v_G_552_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_553_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_554_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_554_ = l_Array_filterPairsM___redArg___lam__3(
        v_toPure_550_,
        v_next_551_,
        v_G_552_,
        v_____do__lift_553_,
    );
    crate::leanh::lean_dec(v_next_551_);
    return v_res_554_;
}
pub unsafe fn l_Array_filterPairsM___redArg___lam__4(
    mut v___x_555_: *mut crate::leanh::LeanObject,
    mut v_toPure_556_: *mut crate::leanh::LeanObject,
    mut v_toBind_557_: *mut crate::leanh::LeanObject,
    mut v___f_558_: *mut crate::leanh::LeanObject,
    mut v___x_559_: u8,
    mut v_fst_560_: *mut crate::leanh::LeanObject,
    mut v_a_561_: *mut crate::leanh::LeanObject,
    mut v_next_562_: *mut crate::leanh::LeanObject,
    mut v_acc_563_: *mut crate::leanh::LeanObject,
    mut v_h_564_: *mut crate::leanh::LeanObject,
    mut v_G_565_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_566_: u8 = 0;
    let mut v___x_567_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_568_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_570_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_571_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_572_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_573_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_574_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_575_: u8 = 0;
    let mut v___x_576_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_577_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_578_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_579_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_580_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_581_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_566_ = lean_nat_dec_lt(v_next_562_, v___x_555_);
                if v___x_566_ == 0 {
                    crate::leanh::lean_dec(v_G_565_);
                    crate::leanh::lean_dec(v_next_562_);
                    crate::leanh::lean_dec(v___f_558_);
                    crate::leanh::lean_dec(v_toBind_557_);
                    v___x_567_ = crate::leanh::lean_apply_2(
                        v_toPure_556_,
                        crate::leanh::lean_box(0),
                        v_acc_563_,
                    );
                    return v___x_567_;
                } else {
                    crate::leanh::lean_inc(v_next_562_);
                    crate::leanh::lean_inc(v_toPure_556_);
                    v___f_568_ = crate::leanh::lean_alloc_closure(
                        l_Array_filterPairsM___redArg___lam__3___boxed as *mut core::ffi::c_void,
                        4,
                        3,
                    );
                    crate::leanh::lean_closure_set(v___f_568_, 0, v_toPure_556_);
                    crate::leanh::lean_closure_set(v___f_568_, 1, v_next_562_);
                    crate::leanh::lean_closure_set(v___f_568_, 2, v_G_565_);
                    v___x_573_ = crate::leanh::lean_box((v___x_559_) as usize);
                    v___x_574_ = lean_array_get(v___x_573_, v_fst_560_, v_next_562_);
                    crate::leanh::lean_dec(v___x_573_);
                    v___x_575_ = (crate::leanh::lean_unbox(v___x_574_) as u8);
                    crate::leanh::lean_dec(v___x_574_);
                    if v___x_575_ == 0 {
                        v___x_576_ = lean_array_fget_borrowed(v_a_561_, v_next_562_);
                        crate::leanh::lean_dec(v_next_562_);
                        crate::leanh::lean_inc(v___x_576_);
                        v___x_577_ = lean_array_push(v_acc_563_, v___x_576_);
                        v___x_578_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_578_, 0, v___x_577_);
                        v___x_579_ = crate::leanh::lean_apply_2(
                            v_toPure_556_,
                            crate::leanh::lean_box(0),
                            v___x_578_,
                        );
                        v___y_570_ = v___x_579_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v_next_562_);
                        v___x_580_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_580_, 0, v_acc_563_);
                        v___x_581_ = crate::leanh::lean_apply_2(
                            v_toPure_556_,
                            crate::leanh::lean_box(0),
                            v___x_580_,
                        );
                        v___y_570_ = v___x_581_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                crate::leanh::lean_inc(v_toBind_557_);
                v___x_571_ = crate::leanh::lean_apply_4(
                    v_toBind_557_,
                    crate::leanh::lean_box(0),
                    crate::leanh::lean_box(0),
                    v___y_570_,
                    v___f_558_,
                );
                v___x_572_ = crate::leanh::lean_apply_4(
                    v_toBind_557_,
                    crate::leanh::lean_box(0),
                    crate::leanh::lean_box(0),
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
    mut v___x_582_: *mut crate::leanh::LeanObject,
    mut v_toPure_583_: *mut crate::leanh::LeanObject,
    mut v_toBind_584_: *mut crate::leanh::LeanObject,
    mut v___f_585_: *mut crate::leanh::LeanObject,
    mut v___x_586_: *mut crate::leanh::LeanObject,
    mut v_fst_587_: *mut crate::leanh::LeanObject,
    mut v_a_588_: *mut crate::leanh::LeanObject,
    mut v_next_589_: *mut crate::leanh::LeanObject,
    mut v_acc_590_: *mut crate::leanh::LeanObject,
    mut v_h_591_: *mut crate::leanh::LeanObject,
    mut v_G_592_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1057__boxed_593_: u8 = 0;
    let mut v_res_594_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1057__boxed_593_ = (crate::leanh::lean_unbox(v___x_586_) as u8);
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
    crate::leanh::lean_dec_ref(v_a_588_);
    crate::leanh::lean_dec(v_fst_587_);
    crate::leanh::lean_dec(v___x_582_);
    return v_res_594_;
}
pub unsafe fn l_Array_filterPairsM___redArg___lam__5(
    mut v___x_595_: *mut crate::leanh::LeanObject,
    mut v_toPure_596_: *mut crate::leanh::LeanObject,
    mut v_toBind_597_: *mut crate::leanh::LeanObject,
    mut v___f_598_: *mut crate::leanh::LeanObject,
    mut v___x_599_: u8,
    mut v_a_600_: *mut crate::leanh::LeanObject,
    mut v___f_601_: *mut crate::leanh::LeanObject,
    mut v_____s_602_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_fst_603_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_604_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_605_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_606_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_607_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_x27_608_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_609_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_610_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_fst_603_ = crate::leanh::lean_ctor_get(v_____s_602_, 0);
    crate::leanh::lean_inc(v_fst_603_);
    v_snd_604_ = crate::leanh::lean_ctor_get(v_____s_602_, 1);
    crate::leanh::lean_inc(v_snd_604_);
    crate::leanh::lean_dec_ref(v_____s_602_);
    v___x_605_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_606_ = crate::leanh::lean_box((v___x_599_) as usize);
    crate::leanh::lean_inc(v_toBind_597_);
    v___f_607_ = crate::leanh::lean_alloc_closure(
        l_Array_filterPairsM___redArg___lam__4___boxed as *mut core::ffi::c_void,
        11,
        7,
    );
    crate::leanh::lean_closure_set(v___f_607_, 0, v___x_595_);
    crate::leanh::lean_closure_set(v___f_607_, 1, v_toPure_596_);
    crate::leanh::lean_closure_set(v___f_607_, 2, v_toBind_597_);
    crate::leanh::lean_closure_set(v___f_607_, 3, v___f_598_);
    crate::leanh::lean_closure_set(v___f_607_, 4, v___x_606_);
    crate::leanh::lean_closure_set(v___f_607_, 5, v_fst_603_);
    crate::leanh::lean_closure_set(v___f_607_, 6, v_a_600_);
    v_a_x27_608_ = lean_mk_empty_array_with_capacity(v_snd_604_);
    crate::leanh::lean_dec(v_snd_604_);
    v___x_609_ = l_WellFounded_opaqueFix_u2083___redArg(
        v___f_607_,
        v___x_605_,
        v_a_x27_608_,
        crate::leanh::lean_box(0),
    );
    v___x_610_ = crate::leanh::lean_apply_4(
        v_toBind_597_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___x_609_,
        v___f_601_,
    );
    return v___x_610_;
}
pub unsafe fn l_Array_filterPairsM___redArg___lam__5___boxed(
    mut v___x_611_: *mut crate::leanh::LeanObject,
    mut v_toPure_612_: *mut crate::leanh::LeanObject,
    mut v_toBind_613_: *mut crate::leanh::LeanObject,
    mut v___f_614_: *mut crate::leanh::LeanObject,
    mut v___x_615_: *mut crate::leanh::LeanObject,
    mut v_a_616_: *mut crate::leanh::LeanObject,
    mut v___f_617_: *mut crate::leanh::LeanObject,
    mut v_____s_618_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1098__boxed_619_: u8 = 0;
    let mut v_res_620_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1098__boxed_619_ = (crate::leanh::lean_unbox(v___x_615_) as u8);
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
    mut v_toPure_621_: *mut crate::leanh::LeanObject,
    mut v_____s_622_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_fst_623_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_624_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_626_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_627_: u8 = 0;
    let mut v___x_629_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_630_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_631_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_632_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_633_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_fst_623_ = crate::leanh::lean_ctor_get(v_____s_622_, 0);
                v_snd_624_ = crate::leanh::lean_ctor_get(v_____s_622_, 1);
                v_isSharedCheck_633_ = (!crate::leanh::lean_is_exclusive(v_____s_622_)) as u8;
                if v_isSharedCheck_633_ == 0 {
                    v___x_626_ = v_____s_622_;
                    v_isShared_627_ = v_isSharedCheck_633_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_snd_624_);
                    crate::leanh::lean_inc(v_fst_623_);
                    crate::leanh::lean_dec(v_____s_622_);
                    v___x_626_ = crate::leanh::lean_box(0);
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
                    v_reuseFailAlloc_632_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_632_, 0, v_fst_623_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_632_, 1, v_snd_624_);
                    v___x_629_ = v_reuseFailAlloc_632_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_630_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_630_, 0, v___x_629_);
                v___x_631_ = crate::leanh::lean_apply_2(
                    v_toPure_621_,
                    crate::leanh::lean_box(0),
                    v___x_630_,
                );
                return v___x_631_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Array_filterPairsM___redArg___lam__7(
    mut v_toPure_634_: *mut crate::leanh::LeanObject,
    mut v_next_635_: *mut crate::leanh::LeanObject,
    mut v_G_636_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_637_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_____do__lift_637_) == 0 {
        let mut v_a_638_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_639_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_G_636_);
        v_a_638_ = crate::leanh::lean_ctor_get(v_____do__lift_637_, 0);
        crate::leanh::lean_inc(v_a_638_);
        crate::leanh::lean_dec_ref_known(v_____do__lift_637_, 1);
        v___x_639_ = crate::leanh::lean_apply_2(v_toPure_634_, crate::leanh::lean_box(0), v_a_638_);
        return v___x_639_;
    } else {
        let mut v_a_640_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_641_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_642_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_643_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_toPure_634_);
        v_a_640_ = crate::leanh::lean_ctor_get(v_____do__lift_637_, 0);
        crate::leanh::lean_inc(v_a_640_);
        crate::leanh::lean_dec_ref_known(v_____do__lift_637_, 1);
        v___x_641_ = crate::leanh::lean_unsigned_to_nat(1);
        v___x_642_ = lean_nat_add(v_next_635_, v___x_641_);
        v___x_643_ = crate::leanh::lean_apply_4(
            v_G_636_,
            v___x_642_,
            v_a_640_,
            crate::leanh::lean_box(0),
            crate::leanh::lean_box(0),
        );
        return v___x_643_;
    }
}
pub unsafe fn l_Array_filterPairsM___redArg___lam__7___boxed(
    mut v_toPure_644_: *mut crate::leanh::LeanObject,
    mut v_next_645_: *mut crate::leanh::LeanObject,
    mut v_G_646_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_647_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_648_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_648_ = l_Array_filterPairsM___redArg___lam__7(
        v_toPure_644_,
        v_next_645_,
        v_G_646_,
        v_____do__lift_647_,
    );
    crate::leanh::lean_dec(v_next_645_);
    return v_res_648_;
}
pub unsafe fn l_Array_filterPairsM___redArg___lam__8(
    mut v_toPure_649_: *mut crate::leanh::LeanObject,
    mut v_next_650_: *mut crate::leanh::LeanObject,
    mut v___x_651_: *mut crate::leanh::LeanObject,
    mut v_G_652_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_653_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_____do__lift_653_) == 0 {
        let mut v_a_654_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_655_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_G_652_);
        v_a_654_ = crate::leanh::lean_ctor_get(v_____do__lift_653_, 0);
        crate::leanh::lean_inc(v_a_654_);
        crate::leanh::lean_dec_ref_known(v_____do__lift_653_, 1);
        v___x_655_ = crate::leanh::lean_apply_2(v_toPure_649_, crate::leanh::lean_box(0), v_a_654_);
        return v___x_655_;
    } else {
        let mut v_a_656_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_657_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_658_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_toPure_649_);
        v_a_656_ = crate::leanh::lean_ctor_get(v_____do__lift_653_, 0);
        crate::leanh::lean_inc(v_a_656_);
        crate::leanh::lean_dec_ref_known(v_____do__lift_653_, 1);
        v___x_657_ = lean_nat_add(v_next_650_, v___x_651_);
        v___x_658_ = crate::leanh::lean_apply_4(
            v_G_652_,
            v___x_657_,
            v_a_656_,
            crate::leanh::lean_box(0),
            crate::leanh::lean_box(0),
        );
        return v___x_658_;
    }
}
pub unsafe fn l_Array_filterPairsM___redArg___lam__8___boxed(
    mut v_toPure_659_: *mut crate::leanh::LeanObject,
    mut v_next_660_: *mut crate::leanh::LeanObject,
    mut v___x_661_: *mut crate::leanh::LeanObject,
    mut v_G_662_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_663_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_664_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_664_ = l_Array_filterPairsM___redArg___lam__8(
        v_toPure_659_,
        v_next_660_,
        v___x_661_,
        v_G_662_,
        v_____do__lift_663_,
    );
    crate::leanh::lean_dec(v___x_661_);
    crate::leanh::lean_dec(v_next_660_);
    return v_res_664_;
}
pub unsafe fn l_Array_filterPairsM___redArg___lam__9(
    mut v___x_665_: *mut crate::leanh::LeanObject,
    mut v_next_666_: *mut crate::leanh::LeanObject,
    mut v___x_667_: u8,
    mut v_toPure_668_: *mut crate::leanh::LeanObject,
    mut v_snd_669_: *mut crate::leanh::LeanObject,
    mut v_fst_670_: *mut crate::leanh::LeanObject,
    mut v_next_671_: *mut crate::leanh::LeanObject,
    mut v_____x_672_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_fst_673_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_674_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_676_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_677_: u8 = 0;
    let mut v_removed_679_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_numRemoved_680_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_681_: u8 = 0;
    let mut v___x_682_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_683_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_684_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_686_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_687_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_688_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_689_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_691_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_692_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_693_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_694_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_695_: u8 = 0;
    let mut v___x_696_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_697_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_698_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_699_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_fst_673_ = crate::leanh::lean_ctor_get(v_____x_672_, 0);
                v_snd_674_ = crate::leanh::lean_ctor_get(v_____x_672_, 1);
                v_isSharedCheck_699_ = (!crate::leanh::lean_is_exclusive(v_____x_672_)) as u8;
                if v_isSharedCheck_699_ == 0 {
                    v___x_676_ = v_____x_672_;
                    v_isShared_677_ = v_isSharedCheck_699_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_snd_674_);
                    crate::leanh::lean_inc(v_fst_673_);
                    crate::leanh::lean_dec(v_____x_672_);
                    v___x_676_ = crate::leanh::lean_box(0);
                    v_isShared_677_ = v_isSharedCheck_699_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_695_ = (crate::leanh::lean_unbox(v_fst_673_) as u8);
                crate::leanh::lean_dec(v_fst_673_);
                if v___x_695_ == 0 {
                    v___x_696_ = lean_nat_add(v_snd_669_, v___x_665_);
                    crate::leanh::lean_dec(v_snd_669_);
                    v___x_697_ = crate::leanh::lean_box((v___x_667_) as usize);
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
                v___x_681_ = (crate::leanh::lean_unbox(v_snd_674_) as u8);
                crate::leanh::lean_dec(v_snd_674_);
                if v___x_681_ == 0 {
                    v___x_682_ = lean_nat_add(v_numRemoved_680_, v___x_665_);
                    crate::leanh::lean_dec(v_numRemoved_680_);
                    v___x_683_ = crate::leanh::lean_box((v___x_667_) as usize);
                    v___x_684_ = lean_array_set(v_removed_679_, v_next_666_, v___x_683_);
                    if v_isShared_677_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_676_, 1, v___x_682_);
                        crate::leanh::lean_ctor_set(v___x_676_, 0, v___x_684_);
                        v___x_686_ = v___x_676_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_689_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_689_, 0, v___x_684_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_689_, 1, v___x_682_);
                        v___x_686_ = v_reuseFailAlloc_689_;
                        state = 3;
                        continue;
                    }
                } else {
                    if v_isShared_677_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_676_, 1, v_numRemoved_680_);
                        crate::leanh::lean_ctor_set(v___x_676_, 0, v_removed_679_);
                        v___x_691_ = v___x_676_;
                        state = 4;
                        continue;
                    } else {
                        v_reuseFailAlloc_694_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_694_, 0, v_removed_679_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_694_, 1, v_numRemoved_680_);
                        v___x_691_ = v_reuseFailAlloc_694_;
                        state = 4;
                        continue;
                    }
                }
            }
            3 => {
                v___x_687_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_687_, 0, v___x_686_);
                v___x_688_ = crate::leanh::lean_apply_2(
                    v_toPure_668_,
                    crate::leanh::lean_box(0),
                    v___x_687_,
                );
                return v___x_688_;
            }
            4 => {
                v___x_692_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_692_, 0, v___x_691_);
                v___x_693_ = crate::leanh::lean_apply_2(
                    v_toPure_668_,
                    crate::leanh::lean_box(0),
                    v___x_692_,
                );
                return v___x_693_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Array_filterPairsM___redArg___lam__9___boxed(
    mut v___x_700_: *mut crate::leanh::LeanObject,
    mut v_next_701_: *mut crate::leanh::LeanObject,
    mut v___x_702_: *mut crate::leanh::LeanObject,
    mut v_toPure_703_: *mut crate::leanh::LeanObject,
    mut v_snd_704_: *mut crate::leanh::LeanObject,
    mut v_fst_705_: *mut crate::leanh::LeanObject,
    mut v_next_706_: *mut crate::leanh::LeanObject,
    mut v_____x_707_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1173__boxed_708_: u8 = 0;
    let mut v_res_709_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1173__boxed_708_ = (crate::leanh::lean_unbox(v___x_702_) as u8);
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
    crate::leanh::lean_dec(v_next_706_);
    crate::leanh::lean_dec(v_next_701_);
    crate::leanh::lean_dec(v___x_700_);
    return v_res_709_;
}
pub unsafe fn l_Array_filterPairsM___redArg___lam__10(
    mut v___x_710_: *mut crate::leanh::LeanObject,
    mut v_toPure_711_: *mut crate::leanh::LeanObject,
    mut v___x_712_: *mut crate::leanh::LeanObject,
    mut v_toBind_713_: *mut crate::leanh::LeanObject,
    mut v___f_714_: *mut crate::leanh::LeanObject,
    mut v_next_715_: *mut crate::leanh::LeanObject,
    mut v_a_716_: *mut crate::leanh::LeanObject,
    mut v_f_717_: *mut crate::leanh::LeanObject,
    mut v___x_718_: u8,
    mut v_next_719_: *mut crate::leanh::LeanObject,
    mut v_acc_720_: *mut crate::leanh::LeanObject,
    mut v_h_721_: *mut crate::leanh::LeanObject,
    mut v_G_722_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_723_: u8 = 0;
    let mut v___x_724_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_725_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_726_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_728_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_729_: u8 = 0;
    let mut v___f_730_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_732_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_733_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_734_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_735_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_736_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_738_: u8 = 0;
    let mut v___x_739_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_740_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_741_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_742_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_744_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_745_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_746_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_747_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_748_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_749_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_750_: u8 = 0;
    let mut v___x_751_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_752_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_753_: u8 = 0;
    let mut v___x_754_: u8 = 0;
    let mut v_isSharedCheck_755_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_723_ = lean_nat_dec_lt(v_next_719_, v___x_710_);
                if v___x_723_ == 0 {
                    crate::leanh::lean_dec(v_G_722_);
                    crate::leanh::lean_dec(v_next_719_);
                    crate::leanh::lean_dec(v_f_717_);
                    crate::leanh::lean_dec(v_next_715_);
                    crate::leanh::lean_dec(v___f_714_);
                    crate::leanh::lean_dec(v_toBind_713_);
                    crate::leanh::lean_dec(v___x_712_);
                    v___x_724_ = crate::leanh::lean_apply_2(
                        v_toPure_711_,
                        crate::leanh::lean_box(0),
                        v_acc_720_,
                    );
                    return v___x_724_;
                } else {
                    v_fst_725_ = crate::leanh::lean_ctor_get(v_acc_720_, 0);
                    v_snd_726_ = crate::leanh::lean_ctor_get(v_acc_720_, 1);
                    v_isSharedCheck_755_ = (!crate::leanh::lean_is_exclusive(v_acc_720_)) as u8;
                    if v_isSharedCheck_755_ == 0 {
                        v___x_728_ = v_acc_720_;
                        v_isShared_729_ = v_isSharedCheck_755_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_snd_726_);
                        crate::leanh::lean_inc(v_fst_725_);
                        crate::leanh::lean_dec(v_acc_720_);
                        v___x_728_ = crate::leanh::lean_box(0);
                        v_isShared_729_ = v_isSharedCheck_755_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                crate::leanh::lean_inc(v___x_712_);
                crate::leanh::lean_inc_n(v_next_719_, 2);
                crate::leanh::lean_inc_n(v_toPure_711_, 2);
                v___f_730_ = crate::leanh::lean_alloc_closure(
                    l_Array_filterPairsM___redArg___lam__8___boxed as *mut core::ffi::c_void,
                    5,
                    4,
                );
                crate::leanh::lean_closure_set(v___f_730_, 0, v_toPure_711_);
                crate::leanh::lean_closure_set(v___f_730_, 1, v_next_719_);
                crate::leanh::lean_closure_set(v___f_730_, 2, v___x_712_);
                crate::leanh::lean_closure_set(v___f_730_, 3, v_G_722_);
                v___x_735_ = crate::leanh::lean_box((v___x_723_) as usize);
                crate::leanh::lean_inc(v_next_715_);
                crate::leanh::lean_inc(v_fst_725_);
                crate::leanh::lean_inc(v_snd_726_);
                v___f_736_ = crate::leanh::lean_alloc_closure(
                    l_Array_filterPairsM___redArg___lam__9___boxed as *mut core::ffi::c_void,
                    8,
                    7,
                );
                crate::leanh::lean_closure_set(v___f_736_, 0, v___x_712_);
                crate::leanh::lean_closure_set(v___f_736_, 1, v_next_719_);
                crate::leanh::lean_closure_set(v___f_736_, 2, v___x_735_);
                crate::leanh::lean_closure_set(v___f_736_, 3, v_toPure_711_);
                crate::leanh::lean_closure_set(v___f_736_, 4, v_snd_726_);
                crate::leanh::lean_closure_set(v___f_736_, 5, v_fst_725_);
                crate::leanh::lean_closure_set(v___f_736_, 6, v_next_715_);
                v___x_748_ = crate::leanh::lean_box((v___x_718_) as usize);
                v___x_749_ = lean_array_get(v___x_748_, v_fst_725_, v_next_715_);
                crate::leanh::lean_dec(v___x_748_);
                v___x_750_ = (crate::leanh::lean_unbox(v___x_749_) as u8);
                if v___x_750_ == 0 {
                    crate::leanh::lean_dec(v___x_749_);
                    v___x_751_ = crate::leanh::lean_box((v___x_718_) as usize);
                    v___x_752_ = lean_array_get(v___x_751_, v_fst_725_, v_next_719_);
                    crate::leanh::lean_dec(v___x_751_);
                    v___x_753_ = (crate::leanh::lean_unbox(v___x_752_) as u8);
                    crate::leanh::lean_dec(v___x_752_);
                    v___y_738_ = v___x_753_;
                    state = 3;
                    continue;
                } else {
                    v___x_754_ = (crate::leanh::lean_unbox(v___x_749_) as u8);
                    crate::leanh::lean_dec(v___x_749_);
                    v___y_738_ = v___x_754_;
                    state = 3;
                    continue;
                }
            }
            2 => {
                crate::leanh::lean_inc(v_toBind_713_);
                v___x_733_ = crate::leanh::lean_apply_4(
                    v_toBind_713_,
                    crate::leanh::lean_box(0),
                    crate::leanh::lean_box(0),
                    v___y_732_,
                    v___f_714_,
                );
                v___x_734_ = crate::leanh::lean_apply_4(
                    v_toBind_713_,
                    crate::leanh::lean_box(0),
                    crate::leanh::lean_box(0),
                    v___x_733_,
                    v___f_730_,
                );
                return v___x_734_;
            }
            3 => {
                if v___y_738_ == 0 {
                    crate::leanh::lean_del_object(v___x_728_);
                    crate::leanh::lean_dec(v_snd_726_);
                    crate::leanh::lean_dec(v_fst_725_);
                    crate::leanh::lean_dec(v_toPure_711_);
                    v___x_739_ = lean_array_fget_borrowed(v_a_716_, v_next_715_);
                    crate::leanh::lean_dec(v_next_715_);
                    v___x_740_ = lean_array_fget_borrowed(v_a_716_, v_next_719_);
                    crate::leanh::lean_dec(v_next_719_);
                    crate::leanh::lean_inc(v___x_740_);
                    crate::leanh::lean_inc(v___x_739_);
                    v___x_741_ = crate::leanh::lean_apply_2(v_f_717_, v___x_739_, v___x_740_);
                    crate::leanh::lean_inc(v_toBind_713_);
                    v___x_742_ = crate::leanh::lean_apply_4(
                        v_toBind_713_,
                        crate::leanh::lean_box(0),
                        crate::leanh::lean_box(0),
                        v___x_741_,
                        v___f_736_,
                    );
                    v___y_732_ = v___x_742_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_dec_ref(v___f_736_);
                    crate::leanh::lean_dec(v_next_719_);
                    crate::leanh::lean_dec(v_f_717_);
                    crate::leanh::lean_dec(v_next_715_);
                    if v_isShared_729_ == 0 {
                        v___x_744_ = v___x_728_;
                        state = 4;
                        continue;
                    } else {
                        v_reuseFailAlloc_747_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_747_, 0, v_fst_725_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_747_, 1, v_snd_726_);
                        v___x_744_ = v_reuseFailAlloc_747_;
                        state = 4;
                        continue;
                    }
                }
            }
            4 => {
                v___x_745_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_745_, 0, v___x_744_);
                v___x_746_ = crate::leanh::lean_apply_2(
                    v_toPure_711_,
                    crate::leanh::lean_box(0),
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
    mut v___x_756_: *mut crate::leanh::LeanObject,
    mut v_toPure_757_: *mut crate::leanh::LeanObject,
    mut v___x_758_: *mut crate::leanh::LeanObject,
    mut v_toBind_759_: *mut crate::leanh::LeanObject,
    mut v___f_760_: *mut crate::leanh::LeanObject,
    mut v_next_761_: *mut crate::leanh::LeanObject,
    mut v_a_762_: *mut crate::leanh::LeanObject,
    mut v_f_763_: *mut crate::leanh::LeanObject,
    mut v___x_764_: *mut crate::leanh::LeanObject,
    mut v_next_765_: *mut crate::leanh::LeanObject,
    mut v_acc_766_: *mut crate::leanh::LeanObject,
    mut v_h_767_: *mut crate::leanh::LeanObject,
    mut v_G_768_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1234__boxed_769_: u8 = 0;
    let mut v_res_770_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1234__boxed_769_ = (crate::leanh::lean_unbox(v___x_764_) as u8);
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
    crate::leanh::lean_dec_ref(v_a_762_);
    crate::leanh::lean_dec(v___x_756_);
    return v_res_770_;
}
pub unsafe fn l_Array_filterPairsM___redArg___lam__11(
    mut v___x_771_: *mut crate::leanh::LeanObject,
    mut v_toPure_772_: *mut crate::leanh::LeanObject,
    mut v_toBind_773_: *mut crate::leanh::LeanObject,
    mut v___f_774_: *mut crate::leanh::LeanObject,
    mut v_a_775_: *mut crate::leanh::LeanObject,
    mut v_f_776_: *mut crate::leanh::LeanObject,
    mut v___x_777_: u8,
    mut v___f_778_: *mut crate::leanh::LeanObject,
    mut v___f_779_: *mut crate::leanh::LeanObject,
    mut v_next_780_: *mut crate::leanh::LeanObject,
    mut v_acc_781_: *mut crate::leanh::LeanObject,
    mut v_h_782_: *mut crate::leanh::LeanObject,
    mut v_G_783_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_784_: u8 = 0;
    let mut v___x_785_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_786_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_787_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_789_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_790_: u8 = 0;
    let mut v___f_791_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_792_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_793_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_794_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_795_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_797_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_798_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_799_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_800_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_801_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_802_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_803_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_784_ = lean_nat_dec_lt(v_next_780_, v___x_771_);
                if v___x_784_ == 0 {
                    crate::leanh::lean_dec(v_G_783_);
                    crate::leanh::lean_dec(v_next_780_);
                    crate::leanh::lean_dec(v___f_779_);
                    crate::leanh::lean_dec(v___f_778_);
                    crate::leanh::lean_dec(v_f_776_);
                    crate::leanh::lean_dec_ref(v_a_775_);
                    crate::leanh::lean_dec(v___f_774_);
                    crate::leanh::lean_dec(v_toBind_773_);
                    crate::leanh::lean_dec(v___x_771_);
                    v___x_785_ = crate::leanh::lean_apply_2(
                        v_toPure_772_,
                        crate::leanh::lean_box(0),
                        v_acc_781_,
                    );
                    return v___x_785_;
                } else {
                    v_fst_786_ = crate::leanh::lean_ctor_get(v_acc_781_, 0);
                    v_snd_787_ = crate::leanh::lean_ctor_get(v_acc_781_, 1);
                    v_isSharedCheck_803_ = (!crate::leanh::lean_is_exclusive(v_acc_781_)) as u8;
                    if v_isSharedCheck_803_ == 0 {
                        v___x_789_ = v_acc_781_;
                        v_isShared_790_ = v_isSharedCheck_803_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_snd_787_);
                        crate::leanh::lean_inc(v_fst_786_);
                        crate::leanh::lean_dec(v_acc_781_);
                        v___x_789_ = crate::leanh::lean_box(0);
                        v_isShared_790_ = v_isSharedCheck_803_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                crate::leanh::lean_inc_n(v_next_780_, 2);
                crate::leanh::lean_inc(v_toPure_772_);
                v___f_791_ = crate::leanh::lean_alloc_closure(
                    l_Array_filterPairsM___redArg___lam__7___boxed as *mut core::ffi::c_void,
                    4,
                    3,
                );
                crate::leanh::lean_closure_set(v___f_791_, 0, v_toPure_772_);
                crate::leanh::lean_closure_set(v___f_791_, 1, v_next_780_);
                crate::leanh::lean_closure_set(v___f_791_, 2, v_G_783_);
                v___x_792_ = crate::leanh::lean_unsigned_to_nat(1);
                v___x_793_ = crate::leanh::lean_box((v___x_777_) as usize);
                crate::leanh::lean_inc(v_toBind_773_);
                v___f_794_ = crate::leanh::lean_alloc_closure(
                    l_Array_filterPairsM___redArg___lam__10___boxed as *mut core::ffi::c_void,
                    13,
                    9,
                );
                crate::leanh::lean_closure_set(v___f_794_, 0, v___x_771_);
                crate::leanh::lean_closure_set(v___f_794_, 1, v_toPure_772_);
                crate::leanh::lean_closure_set(v___f_794_, 2, v___x_792_);
                crate::leanh::lean_closure_set(v___f_794_, 3, v_toBind_773_);
                crate::leanh::lean_closure_set(v___f_794_, 4, v___f_774_);
                crate::leanh::lean_closure_set(v___f_794_, 5, v_next_780_);
                crate::leanh::lean_closure_set(v___f_794_, 6, v_a_775_);
                crate::leanh::lean_closure_set(v___f_794_, 7, v_f_776_);
                crate::leanh::lean_closure_set(v___f_794_, 8, v___x_793_);
                v___x_795_ = lean_nat_add(v_next_780_, v___x_792_);
                crate::leanh::lean_dec(v_next_780_);
                if v_isShared_790_ == 0 {
                    v___x_797_ = v___x_789_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_802_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_802_, 0, v_fst_786_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_802_, 1, v_snd_787_);
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
                    crate::leanh::lean_box(0),
                );
                crate::leanh::lean_inc_n(v_toBind_773_, 2);
                v___x_799_ = crate::leanh::lean_apply_4(
                    v_toBind_773_,
                    crate::leanh::lean_box(0),
                    crate::leanh::lean_box(0),
                    v___x_798_,
                    v___f_778_,
                );
                v___x_800_ = crate::leanh::lean_apply_4(
                    v_toBind_773_,
                    crate::leanh::lean_box(0),
                    crate::leanh::lean_box(0),
                    v___x_799_,
                    v___f_779_,
                );
                v___x_801_ = crate::leanh::lean_apply_4(
                    v_toBind_773_,
                    crate::leanh::lean_box(0),
                    crate::leanh::lean_box(0),
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
    mut v___x_804_: *mut crate::leanh::LeanObject,
    mut v_toPure_805_: *mut crate::leanh::LeanObject,
    mut v_toBind_806_: *mut crate::leanh::LeanObject,
    mut v___f_807_: *mut crate::leanh::LeanObject,
    mut v_a_808_: *mut crate::leanh::LeanObject,
    mut v_f_809_: *mut crate::leanh::LeanObject,
    mut v___x_810_: *mut crate::leanh::LeanObject,
    mut v___f_811_: *mut crate::leanh::LeanObject,
    mut v___f_812_: *mut crate::leanh::LeanObject,
    mut v_next_813_: *mut crate::leanh::LeanObject,
    mut v_acc_814_: *mut crate::leanh::LeanObject,
    mut v_h_815_: *mut crate::leanh::LeanObject,
    mut v_G_816_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1307__boxed_817_: u8 = 0;
    let mut v_res_818_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1307__boxed_817_ = (crate::leanh::lean_unbox(v___x_810_) as u8);
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
    mut v_inst_819_: *mut crate::leanh::LeanObject,
    mut v_a_820_: *mut crate::leanh::LeanObject,
    mut v_f_821_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toApplicative_822_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_823_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_825_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_826_: u8 = 0;
    let mut v_toPure_827_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_828_: u8 = 0;
    let mut v___x_829_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_830_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_removed_831_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_832_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_833_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_834_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_835_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_836_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_837_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_838_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_839_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_840_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_842_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_843_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_844_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_845_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_846_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_toApplicative_822_ = crate::leanh::lean_ctor_get(v_inst_819_, 0);
                v_toBind_823_ = crate::leanh::lean_ctor_get(v_inst_819_, 1);
                v_isSharedCheck_846_ = (!crate::leanh::lean_is_exclusive(v_inst_819_)) as u8;
                if v_isSharedCheck_846_ == 0 {
                    v___x_825_ = v_inst_819_;
                    v_isShared_826_ = v_isSharedCheck_846_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_toBind_823_);
                    crate::leanh::lean_inc(v_toApplicative_822_);
                    crate::leanh::lean_dec(v_inst_819_);
                    v___x_825_ = crate::leanh::lean_box(0);
                    v_isShared_826_ = v_isSharedCheck_846_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_toPure_827_ = crate::leanh::lean_ctor_get(v_toApplicative_822_, 1);
                crate::leanh::lean_inc_n(v_toPure_827_, 6);
                crate::leanh::lean_dec_ref(v_toApplicative_822_);
                v___x_828_ = 0;
                v___x_829_ = lean_array_get_size(v_a_820_);
                v___x_830_ = crate::leanh::lean_box((v___x_828_) as usize);
                v_removed_831_ = lean_mk_array(v___x_829_, v___x_830_);
                v___f_832_ = crate::leanh::lean_alloc_closure(
                    l_Array_filterPairsM___redArg___lam__0 as *mut core::ffi::c_void,
                    2,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_832_, 0, v_toPure_827_);
                v___f_833_ = crate::leanh::lean_alloc_closure(
                    l_Array_filterPairsM___redArg___lam__2 as *mut core::ffi::c_void,
                    2,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_833_, 0, v_toPure_827_);
                v___f_834_ = crate::leanh::lean_alloc_closure(
                    l_Array_filterPairsM___redArg___lam__1 as *mut core::ffi::c_void,
                    2,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_834_, 0, v_toPure_827_);
                v___x_835_ = crate::leanh::lean_box((v___x_828_) as usize);
                crate::leanh::lean_inc_ref(v_a_820_);
                crate::leanh::lean_inc_n(v_toBind_823_, 2);
                v___f_836_ = crate::leanh::lean_alloc_closure(
                    l_Array_filterPairsM___redArg___lam__5___boxed as *mut core::ffi::c_void,
                    8,
                    7,
                );
                crate::leanh::lean_closure_set(v___f_836_, 0, v___x_829_);
                crate::leanh::lean_closure_set(v___f_836_, 1, v_toPure_827_);
                crate::leanh::lean_closure_set(v___f_836_, 2, v_toBind_823_);
                crate::leanh::lean_closure_set(v___f_836_, 3, v___f_833_);
                crate::leanh::lean_closure_set(v___f_836_, 4, v___x_835_);
                crate::leanh::lean_closure_set(v___f_836_, 5, v_a_820_);
                crate::leanh::lean_closure_set(v___f_836_, 6, v___f_834_);
                v___f_837_ = crate::leanh::lean_alloc_closure(
                    l_Array_filterPairsM___redArg___lam__6 as *mut core::ffi::c_void,
                    2,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_837_, 0, v_toPure_827_);
                v___x_838_ = crate::leanh::lean_box((v___x_828_) as usize);
                crate::leanh::lean_inc_ref(v___f_832_);
                v___f_839_ = crate::leanh::lean_alloc_closure(
                    l_Array_filterPairsM___redArg___lam__11___boxed as *mut core::ffi::c_void,
                    13,
                    9,
                );
                crate::leanh::lean_closure_set(v___f_839_, 0, v___x_829_);
                crate::leanh::lean_closure_set(v___f_839_, 1, v_toPure_827_);
                crate::leanh::lean_closure_set(v___f_839_, 2, v_toBind_823_);
                crate::leanh::lean_closure_set(v___f_839_, 3, v___f_832_);
                crate::leanh::lean_closure_set(v___f_839_, 4, v_a_820_);
                crate::leanh::lean_closure_set(v___f_839_, 5, v_f_821_);
                crate::leanh::lean_closure_set(v___f_839_, 6, v___x_838_);
                crate::leanh::lean_closure_set(v___f_839_, 7, v___f_837_);
                crate::leanh::lean_closure_set(v___f_839_, 8, v___f_832_);
                v___x_840_ = crate::leanh::lean_unsigned_to_nat(0);
                if v_isShared_826_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_825_, 1, v___x_840_);
                    crate::leanh::lean_ctor_set(v___x_825_, 0, v_removed_831_);
                    v___x_842_ = v___x_825_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_845_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_845_, 0, v_removed_831_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_845_, 1, v___x_840_);
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
                    crate::leanh::lean_box(0),
                );
                v___x_844_ = crate::leanh::lean_apply_4(
                    v_toBind_823_,
                    crate::leanh::lean_box(0),
                    crate::leanh::lean_box(0),
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
    mut v_m_847_: *mut crate::leanh::LeanObject,
    mut v_inst_848_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_849_: *mut crate::leanh::LeanObject,
    mut v_a_850_: *mut crate::leanh::LeanObject,
    mut v_f_851_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_852_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_852_ = l_Array_filterPairsM___redArg(v_inst_848_, v_a_850_, v_f_851_);
    return v___x_852_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Array_mask_spec__0___redArg(
    mut v_as_853_: *mut crate::leanh::LeanObject,
    mut v_sz_854_: usize,
    mut v_i_855_: usize,
    mut v_b_856_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_a_858_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_859_: usize = 0;
    let mut v___x_860_: usize = 0;
    let mut v___x_862_: u8 = 0;
    let mut v_snd_863_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_864_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_866_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_867_: u8 = 0;
    let mut v_array_868_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_start_869_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_stop_870_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_871_: u8 = 0;
    let mut v___x_873_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_874_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_876_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_877_: u8 = 0;
    let mut v_a_878_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_879_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_880_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_881_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_883_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_884_: u8 = 0;
    let mut v___x_886_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_887_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_888_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_890_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_891_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_892_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_893_: u8 = 0;
    let mut v_unused_894_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_895_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_896_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_897_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_862_ = lean_usize_dec_lt(v_i_855_, v_sz_854_);
                if v___x_862_ == 0 {
                    return v_b_856_;
                } else {
                    v_snd_863_ = crate::leanh::lean_ctor_get(v_b_856_, 1);
                    v_fst_864_ = crate::leanh::lean_ctor_get(v_b_856_, 0);
                    v_isSharedCheck_897_ = (!crate::leanh::lean_is_exclusive(v_b_856_)) as u8;
                    if v_isSharedCheck_897_ == 0 {
                        v___x_866_ = v_b_856_;
                        v_isShared_867_ = v_isSharedCheck_897_;
                        state = 2;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_snd_863_);
                        crate::leanh::lean_inc(v_fst_864_);
                        crate::leanh::lean_dec(v_b_856_);
                        v___x_866_ = crate::leanh::lean_box(0);
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
                v_array_868_ = crate::leanh::lean_ctor_get(v_snd_863_, 0);
                v_start_869_ = crate::leanh::lean_ctor_get(v_snd_863_, 1);
                v_stop_870_ = crate::leanh::lean_ctor_get(v_snd_863_, 2);
                v___x_871_ = lean_nat_dec_lt(v_start_869_, v_stop_870_);
                if v___x_871_ == 0 {
                    if v_isShared_867_ == 0 {
                        v___x_873_ = v___x_866_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_874_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_874_, 0, v_fst_864_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_874_, 1, v_snd_863_);
                        v___x_873_ = v_reuseFailAlloc_874_;
                        state = 3;
                        continue;
                    }
                } else {
                    crate::leanh::lean_inc(v_stop_870_);
                    crate::leanh::lean_inc(v_start_869_);
                    crate::leanh::lean_inc_ref(v_array_868_);
                    v_isSharedCheck_893_ = (!crate::leanh::lean_is_exclusive(v_snd_863_)) as u8;
                    if v_isSharedCheck_893_ == 0 {
                        v_unused_894_ = crate::leanh::lean_ctor_get(v_snd_863_, 2);
                        crate::leanh::lean_dec(v_unused_894_);
                        v_unused_895_ = crate::leanh::lean_ctor_get(v_snd_863_, 1);
                        crate::leanh::lean_dec(v_unused_895_);
                        v_unused_896_ = crate::leanh::lean_ctor_get(v_snd_863_, 0);
                        crate::leanh::lean_dec(v_unused_896_);
                        v___x_876_ = v_snd_863_;
                        v_isShared_877_ = v_isSharedCheck_893_;
                        state = 4;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v_snd_863_);
                        v___x_876_ = crate::leanh::lean_box(0);
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
                v___x_880_ = crate::leanh::lean_unsigned_to_nat(1);
                v___x_881_ = lean_nat_add(v_start_869_, v___x_880_);
                crate::leanh::lean_dec(v_start_869_);
                if v_isShared_877_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_876_, 1, v___x_881_);
                    v___x_883_ = v___x_876_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_892_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_892_, 0, v_array_868_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_892_, 1, v___x_881_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_892_, 2, v_stop_870_);
                    v___x_883_ = v_reuseFailAlloc_892_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v___x_884_ = (crate::leanh::lean_unbox(v_a_878_) as u8);
                if v___x_884_ == 0 {
                    crate::leanh::lean_dec(v___x_879_);
                    if v_isShared_867_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_866_, 1, v___x_883_);
                        v___x_886_ = v___x_866_;
                        state = 6;
                        continue;
                    } else {
                        v_reuseFailAlloc_887_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_887_, 0, v_fst_864_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_887_, 1, v___x_883_);
                        v___x_886_ = v_reuseFailAlloc_887_;
                        state = 6;
                        continue;
                    }
                } else {
                    v___x_888_ = lean_array_push(v_fst_864_, v___x_879_);
                    if v_isShared_867_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_866_, 1, v___x_883_);
                        crate::leanh::lean_ctor_set(v___x_866_, 0, v___x_888_);
                        v___x_890_ = v___x_866_;
                        state = 7;
                        continue;
                    } else {
                        v_reuseFailAlloc_891_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_891_, 0, v___x_888_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_891_, 1, v___x_883_);
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
    mut v_as_898_: *mut crate::leanh::LeanObject,
    mut v_sz_899_: *mut crate::leanh::LeanObject,
    mut v_i_900_: *mut crate::leanh::LeanObject,
    mut v_b_901_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_sz_boxed_902_: usize = 0;
    let mut v_i_boxed_903_: usize = 0;
    let mut v_res_904_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_902_ = crate::leanh::lean_unbox_usize(v_sz_899_);
    crate::leanh::lean_dec(v_sz_899_);
    v_i_boxed_903_ = crate::leanh::lean_unbox_usize(v_i_900_);
    crate::leanh::lean_dec(v_i_900_);
    v_res_904_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Array_mask_spec__0___redArg(v_as_898_, v_sz_boxed_902_, v_i_boxed_903_, v_b_901_);
    crate::leanh::lean_dec_ref(v_as_898_);
    return v_res_904_;
}
pub unsafe fn l_Array_mask___redArg(
    mut v_mask_907_: *mut crate::leanh::LeanObject,
    mut v_xs_908_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_909_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ys_910_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_911_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_912_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_913_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_914_: usize = 0;
    let mut v___x_915_: usize = 0;
    let mut v___x_916_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_917_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_909_ = crate::leanh::lean_unsigned_to_nat(0);
    v_ys_910_ = l_Array_mask___redArg___closed__0;
    v___x_911_ = lean_array_get_size(v_xs_908_);
    v___x_912_ = l_Array_toSubarray___redArg(v_xs_908_, v___x_909_, v___x_911_);
    v___x_913_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_913_, 0, v_ys_910_);
    crate::leanh::lean_ctor_set(v___x_913_, 1, v___x_912_);
    v_sz_914_ = lean_array_size(v_mask_907_);
    v___x_915_ = 0usize;
    v___x_916_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Array_mask_spec__0___redArg(v_mask_907_, v_sz_914_, v___x_915_, v___x_913_);
    v_fst_917_ = crate::leanh::lean_ctor_get(v___x_916_, 0);
    crate::leanh::lean_inc(v_fst_917_);
    crate::leanh::lean_dec_ref(v___x_916_);
    return v_fst_917_;
}
pub unsafe fn l_Array_mask___redArg___boxed(
    mut v_mask_918_: *mut crate::leanh::LeanObject,
    mut v_xs_919_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_920_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_920_ = l_Array_mask___redArg(v_mask_918_, v_xs_919_);
    crate::leanh::lean_dec_ref(v_mask_918_);
    return v_res_920_;
}
pub unsafe fn l_Array_mask(
    mut v_00_u03b1_921_: *mut crate::leanh::LeanObject,
    mut v_mask_922_: *mut crate::leanh::LeanObject,
    mut v_xs_923_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_924_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_924_ = l_Array_mask___redArg(v_mask_922_, v_xs_923_);
    return v___x_924_;
}
pub unsafe fn l_Array_mask___boxed(
    mut v_00_u03b1_925_: *mut crate::leanh::LeanObject,
    mut v_mask_926_: *mut crate::leanh::LeanObject,
    mut v_xs_927_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_928_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_928_ = l_Array_mask(v_00_u03b1_925_, v_mask_926_, v_xs_927_);
    crate::leanh::lean_dec_ref(v_mask_926_);
    return v_res_928_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Array_mask_spec__0(
    mut v_00_u03b1_929_: *mut crate::leanh::LeanObject,
    mut v_as_930_: *mut crate::leanh::LeanObject,
    mut v_sz_931_: usize,
    mut v_i_932_: usize,
    mut v_b_933_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_934_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_934_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Array_mask_spec__0___redArg(v_as_930_, v_sz_931_, v_i_932_, v_b_933_);
    return v___x_934_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Array_mask_spec__0___boxed(
    mut v_00_u03b1_935_: *mut crate::leanh::LeanObject,
    mut v_as_936_: *mut crate::leanh::LeanObject,
    mut v_sz_937_: *mut crate::leanh::LeanObject,
    mut v_i_938_: *mut crate::leanh::LeanObject,
    mut v_b_939_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_sz_boxed_940_: usize = 0;
    let mut v_i_boxed_941_: usize = 0;
    let mut v_res_942_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_940_ = crate::leanh::lean_unbox_usize(v_sz_937_);
    crate::leanh::lean_dec(v_sz_937_);
    v_i_boxed_941_ = crate::leanh::lean_unbox_usize(v_i_938_);
    crate::leanh::lean_dec(v_i_938_);
    v_res_942_ =
        l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Array_mask_spec__0(
            v_00_u03b1_935_,
            v_as_936_,
            v_sz_boxed_940_,
            v_i_boxed_941_,
            v_b_939_,
        );
    crate::leanh::lean_dec_ref(v_as_936_);
    return v_res_942_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Array_zipMasked_spec__0___redArg(
    mut v_xs_943_: *mut crate::leanh::LeanObject,
    mut v_ys_944_: *mut crate::leanh::LeanObject,
    mut v_as_945_: *mut crate::leanh::LeanObject,
    mut v_sz_946_: usize,
    mut v_i_947_: usize,
    mut v_b_948_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_a_950_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_951_: usize = 0;
    let mut v___x_952_: usize = 0;
    let mut v___x_954_: u8 = 0;
    let mut v_snd_955_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_956_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_958_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_959_: u8 = 0;
    let mut v_fst_960_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_961_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_963_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_964_: u8 = 0;
    let mut v_a_965_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_966_: u8 = 0;
    let mut v___x_967_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_968_: u8 = 0;
    let mut v___x_970_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_972_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_973_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_974_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_975_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_976_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_977_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_978_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_980_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_982_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_983_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_984_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_985_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_986_: u8 = 0;
    let mut v___x_988_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_990_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_991_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_992_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_993_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_994_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_995_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_996_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_998_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1000_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1001_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1002_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
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
                    v_snd_955_ = crate::leanh::lean_ctor_get(v_b_948_, 1);
                    v_fst_956_ = crate::leanh::lean_ctor_get(v_b_948_, 0);
                    v_isSharedCheck_1004_ = (!crate::leanh::lean_is_exclusive(v_b_948_)) as u8;
                    if v_isSharedCheck_1004_ == 0 {
                        v___x_958_ = v_b_948_;
                        v_isShared_959_ = v_isSharedCheck_1004_;
                        state = 2;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_snd_955_);
                        crate::leanh::lean_inc(v_fst_956_);
                        crate::leanh::lean_dec(v_b_948_);
                        v___x_958_ = crate::leanh::lean_box(0);
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
                v_fst_960_ = crate::leanh::lean_ctor_get(v_snd_955_, 0);
                v_snd_961_ = crate::leanh::lean_ctor_get(v_snd_955_, 1);
                v_isSharedCheck_1003_ = (!crate::leanh::lean_is_exclusive(v_snd_955_)) as u8;
                if v_isSharedCheck_1003_ == 0 {
                    v___x_963_ = v_snd_955_;
                    v_isShared_964_ = v_isSharedCheck_1003_;
                    state = 3;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_snd_961_);
                    crate::leanh::lean_inc(v_fst_960_);
                    crate::leanh::lean_dec(v_snd_955_);
                    v___x_963_ = crate::leanh::lean_box(0);
                    v_isShared_964_ = v_isSharedCheck_1003_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v_a_965_ = lean_array_uget_borrowed(v_as_945_, v_i_947_);
                v___x_966_ = (crate::leanh::lean_unbox(v_a_965_) as u8);
                if v___x_966_ == 0 {
                    v___x_967_ = lean_array_get_size(v_xs_943_);
                    v___x_968_ = lean_nat_dec_lt(v_fst_956_, v___x_967_);
                    if v___x_968_ == 0 {
                        if v_isShared_964_ == 0 {
                            v___x_970_ = v___x_963_;
                            state = 4;
                            continue;
                        } else {
                            v_reuseFailAlloc_974_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_974_, 0, v_fst_960_);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_974_, 1, v_snd_961_);
                            v___x_970_ = v_reuseFailAlloc_974_;
                            state = 4;
                            continue;
                        }
                    } else {
                        v___x_975_ = lean_array_fget_borrowed(v_xs_943_, v_fst_956_);
                        crate::leanh::lean_inc(v___x_975_);
                        v___x_976_ = lean_array_push(v_snd_961_, v___x_975_);
                        v___x_977_ = crate::leanh::lean_unsigned_to_nat(1);
                        v___x_978_ = lean_nat_add(v_fst_956_, v___x_977_);
                        crate::leanh::lean_dec(v_fst_956_);
                        if v_isShared_964_ == 0 {
                            crate::leanh::lean_ctor_set(v___x_963_, 1, v___x_976_);
                            v___x_980_ = v___x_963_;
                            state = 6;
                            continue;
                        } else {
                            v_reuseFailAlloc_984_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_984_, 0, v_fst_960_);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_984_, 1, v___x_976_);
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
                            v_reuseFailAlloc_992_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_992_, 0, v_fst_960_);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_992_, 1, v_snd_961_);
                            v___x_988_ = v_reuseFailAlloc_992_;
                            state = 8;
                            continue;
                        }
                    } else {
                        v___x_993_ = lean_array_fget_borrowed(v_ys_944_, v_fst_960_);
                        crate::leanh::lean_inc(v___x_993_);
                        v___x_994_ = lean_array_push(v_snd_961_, v___x_993_);
                        v___x_995_ = crate::leanh::lean_unsigned_to_nat(1);
                        v___x_996_ = lean_nat_add(v_fst_960_, v___x_995_);
                        crate::leanh::lean_dec(v_fst_960_);
                        if v_isShared_964_ == 0 {
                            crate::leanh::lean_ctor_set(v___x_963_, 1, v___x_994_);
                            crate::leanh::lean_ctor_set(v___x_963_, 0, v___x_996_);
                            v___x_998_ = v___x_963_;
                            state = 10;
                            continue;
                        } else {
                            v_reuseFailAlloc_1002_ =
                                crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_1002_, 0, v___x_996_);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_1002_, 1, v___x_994_);
                            v___x_998_ = v_reuseFailAlloc_1002_;
                            state = 10;
                            continue;
                        }
                    }
                }
            }
            4 => {
                if v_isShared_959_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_958_, 1, v___x_970_);
                    v___x_972_ = v___x_958_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_973_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_973_, 0, v_fst_956_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_973_, 1, v___x_970_);
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
                    crate::leanh::lean_ctor_set(v___x_958_, 1, v___x_980_);
                    crate::leanh::lean_ctor_set(v___x_958_, 0, v___x_978_);
                    v___x_982_ = v___x_958_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_983_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_983_, 0, v___x_978_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_983_, 1, v___x_980_);
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
                    crate::leanh::lean_ctor_set(v___x_958_, 1, v___x_988_);
                    v___x_990_ = v___x_958_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_991_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_991_, 0, v_fst_956_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_991_, 1, v___x_988_);
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
                    crate::leanh::lean_ctor_set(v___x_958_, 1, v___x_998_);
                    v___x_1000_ = v___x_958_;
                    state = 11;
                    continue;
                } else {
                    v_reuseFailAlloc_1001_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1001_, 0, v_fst_956_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1001_, 1, v___x_998_);
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
    mut v_xs_1005_: *mut crate::leanh::LeanObject,
    mut v_ys_1006_: *mut crate::leanh::LeanObject,
    mut v_as_1007_: *mut crate::leanh::LeanObject,
    mut v_sz_1008_: *mut crate::leanh::LeanObject,
    mut v_i_1009_: *mut crate::leanh::LeanObject,
    mut v_b_1010_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_sz_boxed_1011_: usize = 0;
    let mut v_i_boxed_1012_: usize = 0;
    let mut v_res_1013_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_1011_ = crate::leanh::lean_unbox_usize(v_sz_1008_);
    crate::leanh::lean_dec(v_sz_1008_);
    v_i_boxed_1012_ = crate::leanh::lean_unbox_usize(v_i_1009_);
    crate::leanh::lean_dec(v_i_1009_);
    v_res_1013_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Array_zipMasked_spec__0___redArg(v_xs_1005_, v_ys_1006_, v_as_1007_, v_sz_boxed_1011_, v_i_boxed_1012_, v_b_1010_);
    crate::leanh::lean_dec_ref(v_as_1007_);
    crate::leanh::lean_dec_ref(v_ys_1006_);
    crate::leanh::lean_dec_ref(v_xs_1005_);
    return v_res_1013_;
}
pub unsafe fn l_Array_zipMasked___redArg(
    mut v_mask_1020_: *mut crate::leanh::LeanObject,
    mut v_xs_1021_: *mut crate::leanh::LeanObject,
    mut v_ys_1022_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1023_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_1024_: usize = 0;
    let mut v___x_1025_: usize = 0;
    let mut v___x_1026_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1027_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1028_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1023_ = l_Array_zipMasked___redArg___closed__1;
    v_sz_1024_ = lean_array_size(v_mask_1020_);
    v___x_1025_ = 0usize;
    v___x_1026_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Array_zipMasked_spec__0___redArg(v_xs_1021_, v_ys_1022_, v_mask_1020_, v_sz_1024_, v___x_1025_, v___x_1023_);
    v_snd_1027_ = crate::leanh::lean_ctor_get(v___x_1026_, 1);
    crate::leanh::lean_inc(v_snd_1027_);
    crate::leanh::lean_dec_ref(v___x_1026_);
    v_snd_1028_ = crate::leanh::lean_ctor_get(v_snd_1027_, 1);
    crate::leanh::lean_inc(v_snd_1028_);
    crate::leanh::lean_dec(v_snd_1027_);
    return v_snd_1028_;
}
pub unsafe fn l_Array_zipMasked___redArg___boxed(
    mut v_mask_1029_: *mut crate::leanh::LeanObject,
    mut v_xs_1030_: *mut crate::leanh::LeanObject,
    mut v_ys_1031_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1032_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1032_ = l_Array_zipMasked___redArg(v_mask_1029_, v_xs_1030_, v_ys_1031_);
    crate::leanh::lean_dec_ref(v_ys_1031_);
    crate::leanh::lean_dec_ref(v_xs_1030_);
    crate::leanh::lean_dec_ref(v_mask_1029_);
    return v_res_1032_;
}
pub unsafe fn l_Array_zipMasked(
    mut v_00_u03b1_1033_: *mut crate::leanh::LeanObject,
    mut v_mask_1034_: *mut crate::leanh::LeanObject,
    mut v_xs_1035_: *mut crate::leanh::LeanObject,
    mut v_ys_1036_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1037_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1037_ = l_Array_zipMasked___redArg(v_mask_1034_, v_xs_1035_, v_ys_1036_);
    return v___x_1037_;
}
pub unsafe fn l_Array_zipMasked___boxed(
    mut v_00_u03b1_1038_: *mut crate::leanh::LeanObject,
    mut v_mask_1039_: *mut crate::leanh::LeanObject,
    mut v_xs_1040_: *mut crate::leanh::LeanObject,
    mut v_ys_1041_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1042_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1042_ = l_Array_zipMasked(v_00_u03b1_1038_, v_mask_1039_, v_xs_1040_, v_ys_1041_);
    crate::leanh::lean_dec_ref(v_ys_1041_);
    crate::leanh::lean_dec_ref(v_xs_1040_);
    crate::leanh::lean_dec_ref(v_mask_1039_);
    return v_res_1042_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Array_zipMasked_spec__0(
    mut v_00_u03b1_1043_: *mut crate::leanh::LeanObject,
    mut v_xs_1044_: *mut crate::leanh::LeanObject,
    mut v_ys_1045_: *mut crate::leanh::LeanObject,
    mut v_as_1046_: *mut crate::leanh::LeanObject,
    mut v_sz_1047_: usize,
    mut v_i_1048_: usize,
    mut v_b_1049_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1050_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1050_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Array_zipMasked_spec__0___redArg(v_xs_1044_, v_ys_1045_, v_as_1046_, v_sz_1047_, v_i_1048_, v_b_1049_);
    return v___x_1050_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Array_zipMasked_spec__0___boxed(
    mut v_00_u03b1_1051_: *mut crate::leanh::LeanObject,
    mut v_xs_1052_: *mut crate::leanh::LeanObject,
    mut v_ys_1053_: *mut crate::leanh::LeanObject,
    mut v_as_1054_: *mut crate::leanh::LeanObject,
    mut v_sz_1055_: *mut crate::leanh::LeanObject,
    mut v_i_1056_: *mut crate::leanh::LeanObject,
    mut v_b_1057_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_sz_boxed_1058_: usize = 0;
    let mut v_i_boxed_1059_: usize = 0;
    let mut v_res_1060_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_1058_ = crate::leanh::lean_unbox_usize(v_sz_1055_);
    crate::leanh::lean_dec(v_sz_1055_);
    v_i_boxed_1059_ = crate::leanh::lean_unbox_usize(v_i_1056_);
    crate::leanh::lean_dec(v_i_1056_);
    v_res_1060_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Array_zipMasked_spec__0(v_00_u03b1_1051_, v_xs_1052_, v_ys_1053_, v_as_1054_, v_sz_boxed_1058_, v_i_boxed_1059_, v_b_1057_);
    crate::leanh::lean_dec_ref(v_as_1054_);
    crate::leanh::lean_dec_ref(v_ys_1053_);
    crate::leanh::lean_dec_ref(v_xs_1052_);
    return v_res_1060_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Data_Array(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Init_Data_Stream(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Range_Polymorphic_Nat(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Range_Polymorphic_Iterators(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Data_Array(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_meta_initialized = true;
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lean_Data_Array(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Init_Data_Stream(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Range_Polymorphic_Nat(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Range_Polymorphic_Iterators(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Data_Array(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_Data_Array(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Lean_Data_Array(builtin);
}
