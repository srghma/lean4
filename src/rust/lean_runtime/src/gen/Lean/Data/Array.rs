// Lean compiler output
// Module: Lean.Data.Array
// Imports: Init.Data.Stream Init.Data.Range.Polymorphic.Nat Init.Data.Range.Polymorphic.Iterators
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
use crate::lean_imports_rs::Init::Data::Array::Basic::{
    lean_array_size, lean_array_uget_borrowed, lean_mk_array,
};
use crate::lean_imports_rs::Init::Data::Array::Set::lean_array_set;
use crate::lean_imports_rs::Init::Data::UInt::BasicAux::{lean_usize_add, lean_usize_dec_lt};
use crate::lean_imports_rs::Init::Prelude::{
    lean_array_fget, lean_array_fget_borrowed, lean_array_get, lean_array_get_size,
    lean_array_push, lean_mk_empty_array_with_capacity, lean_nat_add, lean_nat_dec_lt,
};
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_alloc_closure, lean_alloc_ctor, lean_apply_2,
    lean_apply_4, lean_box, lean_closure_set, lean_ctor_get, lean_ctor_set, lean_dec, lean_dec_ref,
    lean_dec_ref_known, lean_del_object, lean_inc, lean_inc_n, lean_inc_ref,
    lean_io_result_is_error, lean_io_result_mk_ok, lean_is_exclusive, lean_obj_tag, lean_unbox,
    lean_unbox_usize, lean_unsigned_to_nat,
};
pub static l_Array_mask___redArg___closed__0_value: LeanArrayObject<0> = LeanArrayObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<usize>() * 2
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 246,
    },
    m_size: 0,
    m_capacity: 0,
    m_data: [],
};
static mut l_Array_mask___redArg___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Array_mask___redArg___closed__0_value) as *mut LeanObject;
pub static l_Array_zipMasked___redArg___closed__0_value: LeanCtorObject<2> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 0,
    },
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut LeanObject,
        core::ptr::addr_of!(l_Array_mask___redArg___closed__0_value) as *mut LeanObject,
    ],
};
static mut l_Array_zipMasked___redArg___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Array_zipMasked___redArg___closed__0_value) as *mut LeanObject;
pub static l_Array_zipMasked___redArg___closed__1_value: LeanCtorObject<2> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 0,
    },
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut LeanObject,
        core::ptr::addr_of!(l_Array_zipMasked___redArg___closed__0_value) as *mut LeanObject,
    ],
};
static mut l_Array_zipMasked___redArg___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Array_zipMasked___redArg___closed__1_value) as *mut LeanObject;
pub unsafe fn l_Array_filterPairsM___redArg___lam__0(
    mut v_toPure_531_: *mut LeanObject,
    mut v_____do__lift_532_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_533_: *mut LeanObject = core::ptr::null_mut();
    v___x_533_ = lean_apply_2(v_toPure_531_, lean_box(0), v_____do__lift_532_);
    return v___x_533_;
}
pub unsafe fn l_Array_filterPairsM___redArg___lam__2(
    mut v_toPure_534_: *mut LeanObject,
    mut v_____do__lift_535_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_536_: *mut LeanObject = core::ptr::null_mut();
    v___x_536_ = lean_apply_2(v_toPure_534_, lean_box(0), v_____do__lift_535_);
    return v___x_536_;
}
pub unsafe fn l_Array_filterPairsM___redArg___lam__1(
    mut v_toPure_537_: *mut LeanObject,
    mut v_____s_538_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_539_: *mut LeanObject = core::ptr::null_mut();
    v___x_539_ = lean_apply_2(v_toPure_537_, lean_box(0), v_____s_538_);
    return v___x_539_;
}
pub unsafe fn l_Array_filterPairsM___redArg___lam__3(
    mut v_toPure_540_: *mut LeanObject,
    mut v_next_541_: *mut LeanObject,
    mut v_G_542_: *mut LeanObject,
    mut v_____do__lift_543_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_____do__lift_543_) == 0 {
        let mut v_a_544_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_545_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_G_542_);
        v_a_544_ = lean_ctor_get(v_____do__lift_543_, 0);
        lean_inc(v_a_544_);
        lean_dec_ref_known(v_____do__lift_543_, 1);
        v___x_545_ = lean_apply_2(v_toPure_540_, lean_box(0), v_a_544_);
        return v___x_545_;
    } else {
        let mut v_a_546_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_547_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_548_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_549_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_toPure_540_);
        v_a_546_ = lean_ctor_get(v_____do__lift_543_, 0);
        lean_inc(v_a_546_);
        lean_dec_ref_known(v_____do__lift_543_, 1);
        v___x_547_ = lean_unsigned_to_nat(1);
        v___x_548_ = lean_nat_add(v_next_541_, v___x_547_);
        v___x_549_ = lean_apply_4(v_G_542_, v___x_548_, v_a_546_, lean_box(0), lean_box(0));
        return v___x_549_;
    }
}
pub unsafe fn l_Array_filterPairsM___redArg___lam__3___boxed(
    mut v_toPure_550_: *mut LeanObject,
    mut v_next_551_: *mut LeanObject,
    mut v_G_552_: *mut LeanObject,
    mut v_____do__lift_553_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_554_: *mut LeanObject = core::ptr::null_mut();
    v_res_554_ = l_Array_filterPairsM___redArg___lam__3(
        v_toPure_550_,
        v_next_551_,
        v_G_552_,
        v_____do__lift_553_,
    );
    lean_dec(v_next_551_);
    return v_res_554_;
}
pub unsafe fn l_Array_filterPairsM___redArg___lam__4(
    mut v___x_555_: *mut LeanObject,
    mut v_toPure_556_: *mut LeanObject,
    mut v_toBind_557_: *mut LeanObject,
    mut v___f_558_: *mut LeanObject,
    mut v___x_559_: u8,
    mut v_fst_560_: *mut LeanObject,
    mut v_a_561_: *mut LeanObject,
    mut v_next_562_: *mut LeanObject,
    mut v_acc_563_: *mut LeanObject,
    mut v_h_564_: *mut LeanObject,
    mut v_G_565_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_566_: u8 = 0;
    let mut v___x_567_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_568_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_570_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_571_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_572_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_573_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_574_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_575_: u8 = 0;
    let mut v___x_576_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_577_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_578_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_579_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_580_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_581_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_566_ = lean_nat_dec_lt(v_next_562_, v___x_555_);
                if v___x_566_ == 0 {
                    lean_dec(v_G_565_);
                    lean_dec(v_next_562_);
                    lean_dec(v___f_558_);
                    lean_dec(v_toBind_557_);
                    v___x_567_ = lean_apply_2(v_toPure_556_, lean_box(0), v_acc_563_);
                    return v___x_567_;
                } else {
                    lean_inc(v_next_562_);
                    lean_inc(v_toPure_556_);
                    v___f_568_ = lean_alloc_closure(
                        l_Array_filterPairsM___redArg___lam__3___boxed as *mut core::ffi::c_void,
                        4,
                        3,
                    );
                    lean_closure_set(v___f_568_, 0, v_toPure_556_);
                    lean_closure_set(v___f_568_, 1, v_next_562_);
                    lean_closure_set(v___f_568_, 2, v_G_565_);
                    v___x_573_ = lean_box((v___x_559_) as usize);
                    v___x_574_ = lean_array_get(v___x_573_, v_fst_560_, v_next_562_);
                    lean_dec(v___x_573_);
                    v___x_575_ = (lean_unbox(v___x_574_) as u8);
                    lean_dec(v___x_574_);
                    if v___x_575_ == 0 {
                        v___x_576_ = lean_array_fget_borrowed(v_a_561_, v_next_562_);
                        lean_dec(v_next_562_);
                        lean_inc(v___x_576_);
                        v___x_577_ = lean_array_push(v_acc_563_, v___x_576_);
                        v___x_578_ = lean_alloc_ctor(1, 1, (0) as u32);
                        lean_ctor_set(v___x_578_, 0, v___x_577_);
                        v___x_579_ = lean_apply_2(v_toPure_556_, lean_box(0), v___x_578_);
                        v___y_570_ = v___x_579_;
                        state = 1;
                        continue;
                    } else {
                        lean_dec(v_next_562_);
                        v___x_580_ = lean_alloc_ctor(1, 1, (0) as u32);
                        lean_ctor_set(v___x_580_, 0, v_acc_563_);
                        v___x_581_ = lean_apply_2(v_toPure_556_, lean_box(0), v___x_580_);
                        v___y_570_ = v___x_581_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                lean_inc(v_toBind_557_);
                v___x_571_ = lean_apply_4(
                    v_toBind_557_,
                    lean_box(0),
                    lean_box(0),
                    v___y_570_,
                    v___f_558_,
                );
                v___x_572_ = lean_apply_4(
                    v_toBind_557_,
                    lean_box(0),
                    lean_box(0),
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
    mut v___x_582_: *mut LeanObject,
    mut v_toPure_583_: *mut LeanObject,
    mut v_toBind_584_: *mut LeanObject,
    mut v___f_585_: *mut LeanObject,
    mut v___x_586_: *mut LeanObject,
    mut v_fst_587_: *mut LeanObject,
    mut v_a_588_: *mut LeanObject,
    mut v_next_589_: *mut LeanObject,
    mut v_acc_590_: *mut LeanObject,
    mut v_h_591_: *mut LeanObject,
    mut v_G_592_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1057__boxed_593_: u8 = 0;
    let mut v_res_594_: *mut LeanObject = core::ptr::null_mut();
    v___x_1057__boxed_593_ = (lean_unbox(v___x_586_) as u8);
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
    lean_dec_ref(v_a_588_);
    lean_dec(v_fst_587_);
    lean_dec(v___x_582_);
    return v_res_594_;
}
pub unsafe fn l_Array_filterPairsM___redArg___lam__5(
    mut v___x_595_: *mut LeanObject,
    mut v_toPure_596_: *mut LeanObject,
    mut v_toBind_597_: *mut LeanObject,
    mut v___f_598_: *mut LeanObject,
    mut v___x_599_: u8,
    mut v_a_600_: *mut LeanObject,
    mut v___f_601_: *mut LeanObject,
    mut v_____s_602_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_fst_603_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_604_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_605_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_606_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_607_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_x27_608_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_609_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_610_: *mut LeanObject = core::ptr::null_mut();
    v_fst_603_ = lean_ctor_get(v_____s_602_, 0);
    lean_inc(v_fst_603_);
    v_snd_604_ = lean_ctor_get(v_____s_602_, 1);
    lean_inc(v_snd_604_);
    lean_dec_ref(v_____s_602_);
    v___x_605_ = lean_unsigned_to_nat(0);
    v___x_606_ = lean_box((v___x_599_) as usize);
    lean_inc(v_toBind_597_);
    v___f_607_ = lean_alloc_closure(
        l_Array_filterPairsM___redArg___lam__4___boxed as *mut core::ffi::c_void,
        11,
        7,
    );
    lean_closure_set(v___f_607_, 0, v___x_595_);
    lean_closure_set(v___f_607_, 1, v_toPure_596_);
    lean_closure_set(v___f_607_, 2, v_toBind_597_);
    lean_closure_set(v___f_607_, 3, v___f_598_);
    lean_closure_set(v___f_607_, 4, v___x_606_);
    lean_closure_set(v___f_607_, 5, v_fst_603_);
    lean_closure_set(v___f_607_, 6, v_a_600_);
    v_a_x27_608_ = lean_mk_empty_array_with_capacity(v_snd_604_);
    lean_dec(v_snd_604_);
    v___x_609_ =
        l_WellFounded_opaqueFix_u2083___redArg(v___f_607_, v___x_605_, v_a_x27_608_, lean_box(0));
    v___x_610_ = lean_apply_4(
        v_toBind_597_,
        lean_box(0),
        lean_box(0),
        v___x_609_,
        v___f_601_,
    );
    return v___x_610_;
}
pub unsafe fn l_Array_filterPairsM___redArg___lam__5___boxed(
    mut v___x_611_: *mut LeanObject,
    mut v_toPure_612_: *mut LeanObject,
    mut v_toBind_613_: *mut LeanObject,
    mut v___f_614_: *mut LeanObject,
    mut v___x_615_: *mut LeanObject,
    mut v_a_616_: *mut LeanObject,
    mut v___f_617_: *mut LeanObject,
    mut v_____s_618_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1098__boxed_619_: u8 = 0;
    let mut v_res_620_: *mut LeanObject = core::ptr::null_mut();
    v___x_1098__boxed_619_ = (lean_unbox(v___x_615_) as u8);
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
    mut v_toPure_621_: *mut LeanObject,
    mut v_____s_622_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_fst_623_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_624_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_626_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_627_: u8 = 0;
    let mut v___x_629_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_630_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_631_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_632_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_633_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_fst_623_ = lean_ctor_get(v_____s_622_, 0);
                v_snd_624_ = lean_ctor_get(v_____s_622_, 1);
                v_isSharedCheck_633_ = (!lean_is_exclusive(v_____s_622_)) as u8;
                if v_isSharedCheck_633_ == 0 {
                    v___x_626_ = v_____s_622_;
                    v_isShared_627_ = v_isSharedCheck_633_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_snd_624_);
                    lean_inc(v_fst_623_);
                    lean_dec(v_____s_622_);
                    v___x_626_ = lean_box(0);
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
                    v_reuseFailAlloc_632_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_632_, 0, v_fst_623_);
                    lean_ctor_set(v_reuseFailAlloc_632_, 1, v_snd_624_);
                    v___x_629_ = v_reuseFailAlloc_632_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_630_ = lean_alloc_ctor(1, 1, (0) as u32);
                lean_ctor_set(v___x_630_, 0, v___x_629_);
                v___x_631_ = lean_apply_2(v_toPure_621_, lean_box(0), v___x_630_);
                return v___x_631_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Array_filterPairsM___redArg___lam__7(
    mut v_toPure_634_: *mut LeanObject,
    mut v_next_635_: *mut LeanObject,
    mut v_G_636_: *mut LeanObject,
    mut v_____do__lift_637_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_____do__lift_637_) == 0 {
        let mut v_a_638_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_639_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_G_636_);
        v_a_638_ = lean_ctor_get(v_____do__lift_637_, 0);
        lean_inc(v_a_638_);
        lean_dec_ref_known(v_____do__lift_637_, 1);
        v___x_639_ = lean_apply_2(v_toPure_634_, lean_box(0), v_a_638_);
        return v___x_639_;
    } else {
        let mut v_a_640_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_641_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_642_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_643_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_toPure_634_);
        v_a_640_ = lean_ctor_get(v_____do__lift_637_, 0);
        lean_inc(v_a_640_);
        lean_dec_ref_known(v_____do__lift_637_, 1);
        v___x_641_ = lean_unsigned_to_nat(1);
        v___x_642_ = lean_nat_add(v_next_635_, v___x_641_);
        v___x_643_ = lean_apply_4(v_G_636_, v___x_642_, v_a_640_, lean_box(0), lean_box(0));
        return v___x_643_;
    }
}
pub unsafe fn l_Array_filterPairsM___redArg___lam__7___boxed(
    mut v_toPure_644_: *mut LeanObject,
    mut v_next_645_: *mut LeanObject,
    mut v_G_646_: *mut LeanObject,
    mut v_____do__lift_647_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_648_: *mut LeanObject = core::ptr::null_mut();
    v_res_648_ = l_Array_filterPairsM___redArg___lam__7(
        v_toPure_644_,
        v_next_645_,
        v_G_646_,
        v_____do__lift_647_,
    );
    lean_dec(v_next_645_);
    return v_res_648_;
}
pub unsafe fn l_Array_filterPairsM___redArg___lam__8(
    mut v_toPure_649_: *mut LeanObject,
    mut v_next_650_: *mut LeanObject,
    mut v___x_651_: *mut LeanObject,
    mut v_G_652_: *mut LeanObject,
    mut v_____do__lift_653_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_____do__lift_653_) == 0 {
        let mut v_a_654_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_655_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_G_652_);
        v_a_654_ = lean_ctor_get(v_____do__lift_653_, 0);
        lean_inc(v_a_654_);
        lean_dec_ref_known(v_____do__lift_653_, 1);
        v___x_655_ = lean_apply_2(v_toPure_649_, lean_box(0), v_a_654_);
        return v___x_655_;
    } else {
        let mut v_a_656_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_657_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_658_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_toPure_649_);
        v_a_656_ = lean_ctor_get(v_____do__lift_653_, 0);
        lean_inc(v_a_656_);
        lean_dec_ref_known(v_____do__lift_653_, 1);
        v___x_657_ = lean_nat_add(v_next_650_, v___x_651_);
        v___x_658_ = lean_apply_4(v_G_652_, v___x_657_, v_a_656_, lean_box(0), lean_box(0));
        return v___x_658_;
    }
}
pub unsafe fn l_Array_filterPairsM___redArg___lam__8___boxed(
    mut v_toPure_659_: *mut LeanObject,
    mut v_next_660_: *mut LeanObject,
    mut v___x_661_: *mut LeanObject,
    mut v_G_662_: *mut LeanObject,
    mut v_____do__lift_663_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_664_: *mut LeanObject = core::ptr::null_mut();
    v_res_664_ = l_Array_filterPairsM___redArg___lam__8(
        v_toPure_659_,
        v_next_660_,
        v___x_661_,
        v_G_662_,
        v_____do__lift_663_,
    );
    lean_dec(v___x_661_);
    lean_dec(v_next_660_);
    return v_res_664_;
}
pub unsafe fn l_Array_filterPairsM___redArg___lam__9(
    mut v___x_665_: *mut LeanObject,
    mut v_next_666_: *mut LeanObject,
    mut v___x_667_: u8,
    mut v_toPure_668_: *mut LeanObject,
    mut v_snd_669_: *mut LeanObject,
    mut v_fst_670_: *mut LeanObject,
    mut v_next_671_: *mut LeanObject,
    mut v_____x_672_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_fst_673_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_674_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_676_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_677_: u8 = 0;
    let mut v_removed_679_: *mut LeanObject = core::ptr::null_mut();
    let mut v_numRemoved_680_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_681_: u8 = 0;
    let mut v___x_682_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_683_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_684_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_686_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_687_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_688_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_689_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_691_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_692_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_693_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_694_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_695_: u8 = 0;
    let mut v___x_696_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_697_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_698_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_699_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_fst_673_ = lean_ctor_get(v_____x_672_, 0);
                v_snd_674_ = lean_ctor_get(v_____x_672_, 1);
                v_isSharedCheck_699_ = (!lean_is_exclusive(v_____x_672_)) as u8;
                if v_isSharedCheck_699_ == 0 {
                    v___x_676_ = v_____x_672_;
                    v_isShared_677_ = v_isSharedCheck_699_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_snd_674_);
                    lean_inc(v_fst_673_);
                    lean_dec(v_____x_672_);
                    v___x_676_ = lean_box(0);
                    v_isShared_677_ = v_isSharedCheck_699_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_695_ = (lean_unbox(v_fst_673_) as u8);
                lean_dec(v_fst_673_);
                if v___x_695_ == 0 {
                    v___x_696_ = lean_nat_add(v_snd_669_, v___x_665_);
                    lean_dec(v_snd_669_);
                    v___x_697_ = lean_box((v___x_667_) as usize);
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
                v___x_681_ = (lean_unbox(v_snd_674_) as u8);
                lean_dec(v_snd_674_);
                if v___x_681_ == 0 {
                    v___x_682_ = lean_nat_add(v_numRemoved_680_, v___x_665_);
                    lean_dec(v_numRemoved_680_);
                    v___x_683_ = lean_box((v___x_667_) as usize);
                    v___x_684_ = lean_array_set(v_removed_679_, v_next_666_, v___x_683_);
                    if v_isShared_677_ == 0 {
                        lean_ctor_set(v___x_676_, 1, v___x_682_);
                        lean_ctor_set(v___x_676_, 0, v___x_684_);
                        v___x_686_ = v___x_676_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_689_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_689_, 0, v___x_684_);
                        lean_ctor_set(v_reuseFailAlloc_689_, 1, v___x_682_);
                        v___x_686_ = v_reuseFailAlloc_689_;
                        state = 3;
                        continue;
                    }
                } else {
                    if v_isShared_677_ == 0 {
                        lean_ctor_set(v___x_676_, 1, v_numRemoved_680_);
                        lean_ctor_set(v___x_676_, 0, v_removed_679_);
                        v___x_691_ = v___x_676_;
                        state = 4;
                        continue;
                    } else {
                        v_reuseFailAlloc_694_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_694_, 0, v_removed_679_);
                        lean_ctor_set(v_reuseFailAlloc_694_, 1, v_numRemoved_680_);
                        v___x_691_ = v_reuseFailAlloc_694_;
                        state = 4;
                        continue;
                    }
                }
            }
            3 => {
                v___x_687_ = lean_alloc_ctor(1, 1, (0) as u32);
                lean_ctor_set(v___x_687_, 0, v___x_686_);
                v___x_688_ = lean_apply_2(v_toPure_668_, lean_box(0), v___x_687_);
                return v___x_688_;
            }
            4 => {
                v___x_692_ = lean_alloc_ctor(1, 1, (0) as u32);
                lean_ctor_set(v___x_692_, 0, v___x_691_);
                v___x_693_ = lean_apply_2(v_toPure_668_, lean_box(0), v___x_692_);
                return v___x_693_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Array_filterPairsM___redArg___lam__9___boxed(
    mut v___x_700_: *mut LeanObject,
    mut v_next_701_: *mut LeanObject,
    mut v___x_702_: *mut LeanObject,
    mut v_toPure_703_: *mut LeanObject,
    mut v_snd_704_: *mut LeanObject,
    mut v_fst_705_: *mut LeanObject,
    mut v_next_706_: *mut LeanObject,
    mut v_____x_707_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1173__boxed_708_: u8 = 0;
    let mut v_res_709_: *mut LeanObject = core::ptr::null_mut();
    v___x_1173__boxed_708_ = (lean_unbox(v___x_702_) as u8);
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
    lean_dec(v_next_706_);
    lean_dec(v_next_701_);
    lean_dec(v___x_700_);
    return v_res_709_;
}
pub unsafe fn l_Array_filterPairsM___redArg___lam__10(
    mut v___x_710_: *mut LeanObject,
    mut v_toPure_711_: *mut LeanObject,
    mut v___x_712_: *mut LeanObject,
    mut v_toBind_713_: *mut LeanObject,
    mut v___f_714_: *mut LeanObject,
    mut v_next_715_: *mut LeanObject,
    mut v_a_716_: *mut LeanObject,
    mut v_f_717_: *mut LeanObject,
    mut v___x_718_: u8,
    mut v_next_719_: *mut LeanObject,
    mut v_acc_720_: *mut LeanObject,
    mut v_h_721_: *mut LeanObject,
    mut v_G_722_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_723_: u8 = 0;
    let mut v___x_724_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_725_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_726_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_728_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_729_: u8 = 0;
    let mut v___f_730_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_732_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_733_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_734_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_735_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_736_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_738_: u8 = 0;
    let mut v___x_739_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_740_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_741_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_742_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_744_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_745_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_746_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_747_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_748_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_749_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_750_: u8 = 0;
    let mut v___x_751_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_752_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_753_: u8 = 0;
    let mut v___x_754_: u8 = 0;
    let mut v_isSharedCheck_755_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_723_ = lean_nat_dec_lt(v_next_719_, v___x_710_);
                if v___x_723_ == 0 {
                    lean_dec(v_G_722_);
                    lean_dec(v_next_719_);
                    lean_dec(v_f_717_);
                    lean_dec(v_next_715_);
                    lean_dec(v___f_714_);
                    lean_dec(v_toBind_713_);
                    lean_dec(v___x_712_);
                    v___x_724_ = lean_apply_2(v_toPure_711_, lean_box(0), v_acc_720_);
                    return v___x_724_;
                } else {
                    v_fst_725_ = lean_ctor_get(v_acc_720_, 0);
                    v_snd_726_ = lean_ctor_get(v_acc_720_, 1);
                    v_isSharedCheck_755_ = (!lean_is_exclusive(v_acc_720_)) as u8;
                    if v_isSharedCheck_755_ == 0 {
                        v___x_728_ = v_acc_720_;
                        v_isShared_729_ = v_isSharedCheck_755_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_snd_726_);
                        lean_inc(v_fst_725_);
                        lean_dec(v_acc_720_);
                        v___x_728_ = lean_box(0);
                        v_isShared_729_ = v_isSharedCheck_755_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                lean_inc(v___x_712_);
                lean_inc_n(v_next_719_, 2);
                lean_inc_n(v_toPure_711_, 2);
                v___f_730_ = lean_alloc_closure(
                    l_Array_filterPairsM___redArg___lam__8___boxed as *mut core::ffi::c_void,
                    5,
                    4,
                );
                lean_closure_set(v___f_730_, 0, v_toPure_711_);
                lean_closure_set(v___f_730_, 1, v_next_719_);
                lean_closure_set(v___f_730_, 2, v___x_712_);
                lean_closure_set(v___f_730_, 3, v_G_722_);
                v___x_735_ = lean_box((v___x_723_) as usize);
                lean_inc(v_next_715_);
                lean_inc(v_fst_725_);
                lean_inc(v_snd_726_);
                v___f_736_ = lean_alloc_closure(
                    l_Array_filterPairsM___redArg___lam__9___boxed as *mut core::ffi::c_void,
                    8,
                    7,
                );
                lean_closure_set(v___f_736_, 0, v___x_712_);
                lean_closure_set(v___f_736_, 1, v_next_719_);
                lean_closure_set(v___f_736_, 2, v___x_735_);
                lean_closure_set(v___f_736_, 3, v_toPure_711_);
                lean_closure_set(v___f_736_, 4, v_snd_726_);
                lean_closure_set(v___f_736_, 5, v_fst_725_);
                lean_closure_set(v___f_736_, 6, v_next_715_);
                v___x_748_ = lean_box((v___x_718_) as usize);
                v___x_749_ = lean_array_get(v___x_748_, v_fst_725_, v_next_715_);
                lean_dec(v___x_748_);
                v___x_750_ = (lean_unbox(v___x_749_) as u8);
                if v___x_750_ == 0 {
                    lean_dec(v___x_749_);
                    v___x_751_ = lean_box((v___x_718_) as usize);
                    v___x_752_ = lean_array_get(v___x_751_, v_fst_725_, v_next_719_);
                    lean_dec(v___x_751_);
                    v___x_753_ = (lean_unbox(v___x_752_) as u8);
                    lean_dec(v___x_752_);
                    v___y_738_ = v___x_753_;
                    state = 3;
                    continue;
                } else {
                    v___x_754_ = (lean_unbox(v___x_749_) as u8);
                    lean_dec(v___x_749_);
                    v___y_738_ = v___x_754_;
                    state = 3;
                    continue;
                }
            }
            2 => {
                lean_inc(v_toBind_713_);
                v___x_733_ = lean_apply_4(
                    v_toBind_713_,
                    lean_box(0),
                    lean_box(0),
                    v___y_732_,
                    v___f_714_,
                );
                v___x_734_ = lean_apply_4(
                    v_toBind_713_,
                    lean_box(0),
                    lean_box(0),
                    v___x_733_,
                    v___f_730_,
                );
                return v___x_734_;
            }
            3 => {
                if v___y_738_ == 0 {
                    lean_del_object(v___x_728_);
                    lean_dec(v_snd_726_);
                    lean_dec(v_fst_725_);
                    lean_dec(v_toPure_711_);
                    v___x_739_ = lean_array_fget_borrowed(v_a_716_, v_next_715_);
                    lean_dec(v_next_715_);
                    v___x_740_ = lean_array_fget_borrowed(v_a_716_, v_next_719_);
                    lean_dec(v_next_719_);
                    lean_inc(v___x_740_);
                    lean_inc(v___x_739_);
                    v___x_741_ = lean_apply_2(v_f_717_, v___x_739_, v___x_740_);
                    lean_inc(v_toBind_713_);
                    v___x_742_ = lean_apply_4(
                        v_toBind_713_,
                        lean_box(0),
                        lean_box(0),
                        v___x_741_,
                        v___f_736_,
                    );
                    v___y_732_ = v___x_742_;
                    state = 2;
                    continue;
                } else {
                    lean_dec_ref(v___f_736_);
                    lean_dec(v_next_719_);
                    lean_dec(v_f_717_);
                    lean_dec(v_next_715_);
                    if v_isShared_729_ == 0 {
                        v___x_744_ = v___x_728_;
                        state = 4;
                        continue;
                    } else {
                        v_reuseFailAlloc_747_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_747_, 0, v_fst_725_);
                        lean_ctor_set(v_reuseFailAlloc_747_, 1, v_snd_726_);
                        v___x_744_ = v_reuseFailAlloc_747_;
                        state = 4;
                        continue;
                    }
                }
            }
            4 => {
                v___x_745_ = lean_alloc_ctor(1, 1, (0) as u32);
                lean_ctor_set(v___x_745_, 0, v___x_744_);
                v___x_746_ = lean_apply_2(v_toPure_711_, lean_box(0), v___x_745_);
                v___y_732_ = v___x_746_;
                state = 2;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Array_filterPairsM___redArg___lam__10___boxed(
    mut v___x_756_: *mut LeanObject,
    mut v_toPure_757_: *mut LeanObject,
    mut v___x_758_: *mut LeanObject,
    mut v_toBind_759_: *mut LeanObject,
    mut v___f_760_: *mut LeanObject,
    mut v_next_761_: *mut LeanObject,
    mut v_a_762_: *mut LeanObject,
    mut v_f_763_: *mut LeanObject,
    mut v___x_764_: *mut LeanObject,
    mut v_next_765_: *mut LeanObject,
    mut v_acc_766_: *mut LeanObject,
    mut v_h_767_: *mut LeanObject,
    mut v_G_768_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1234__boxed_769_: u8 = 0;
    let mut v_res_770_: *mut LeanObject = core::ptr::null_mut();
    v___x_1234__boxed_769_ = (lean_unbox(v___x_764_) as u8);
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
    lean_dec_ref(v_a_762_);
    lean_dec(v___x_756_);
    return v_res_770_;
}
pub unsafe fn l_Array_filterPairsM___redArg___lam__11(
    mut v___x_771_: *mut LeanObject,
    mut v_toPure_772_: *mut LeanObject,
    mut v_toBind_773_: *mut LeanObject,
    mut v___f_774_: *mut LeanObject,
    mut v_a_775_: *mut LeanObject,
    mut v_f_776_: *mut LeanObject,
    mut v___x_777_: u8,
    mut v___f_778_: *mut LeanObject,
    mut v___f_779_: *mut LeanObject,
    mut v_next_780_: *mut LeanObject,
    mut v_acc_781_: *mut LeanObject,
    mut v_h_782_: *mut LeanObject,
    mut v_G_783_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_784_: u8 = 0;
    let mut v___x_785_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_786_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_787_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_789_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_790_: u8 = 0;
    let mut v___f_791_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_792_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_793_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_794_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_795_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_797_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_798_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_799_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_800_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_801_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_802_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_803_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_784_ = lean_nat_dec_lt(v_next_780_, v___x_771_);
                if v___x_784_ == 0 {
                    lean_dec(v_G_783_);
                    lean_dec(v_next_780_);
                    lean_dec(v___f_779_);
                    lean_dec(v___f_778_);
                    lean_dec(v_f_776_);
                    lean_dec_ref(v_a_775_);
                    lean_dec(v___f_774_);
                    lean_dec(v_toBind_773_);
                    lean_dec(v___x_771_);
                    v___x_785_ = lean_apply_2(v_toPure_772_, lean_box(0), v_acc_781_);
                    return v___x_785_;
                } else {
                    v_fst_786_ = lean_ctor_get(v_acc_781_, 0);
                    v_snd_787_ = lean_ctor_get(v_acc_781_, 1);
                    v_isSharedCheck_803_ = (!lean_is_exclusive(v_acc_781_)) as u8;
                    if v_isSharedCheck_803_ == 0 {
                        v___x_789_ = v_acc_781_;
                        v_isShared_790_ = v_isSharedCheck_803_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_snd_787_);
                        lean_inc(v_fst_786_);
                        lean_dec(v_acc_781_);
                        v___x_789_ = lean_box(0);
                        v_isShared_790_ = v_isSharedCheck_803_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                lean_inc_n(v_next_780_, 2);
                lean_inc(v_toPure_772_);
                v___f_791_ = lean_alloc_closure(
                    l_Array_filterPairsM___redArg___lam__7___boxed as *mut core::ffi::c_void,
                    4,
                    3,
                );
                lean_closure_set(v___f_791_, 0, v_toPure_772_);
                lean_closure_set(v___f_791_, 1, v_next_780_);
                lean_closure_set(v___f_791_, 2, v_G_783_);
                v___x_792_ = lean_unsigned_to_nat(1);
                v___x_793_ = lean_box((v___x_777_) as usize);
                lean_inc(v_toBind_773_);
                v___f_794_ = lean_alloc_closure(
                    l_Array_filterPairsM___redArg___lam__10___boxed as *mut core::ffi::c_void,
                    13,
                    9,
                );
                lean_closure_set(v___f_794_, 0, v___x_771_);
                lean_closure_set(v___f_794_, 1, v_toPure_772_);
                lean_closure_set(v___f_794_, 2, v___x_792_);
                lean_closure_set(v___f_794_, 3, v_toBind_773_);
                lean_closure_set(v___f_794_, 4, v___f_774_);
                lean_closure_set(v___f_794_, 5, v_next_780_);
                lean_closure_set(v___f_794_, 6, v_a_775_);
                lean_closure_set(v___f_794_, 7, v_f_776_);
                lean_closure_set(v___f_794_, 8, v___x_793_);
                v___x_795_ = lean_nat_add(v_next_780_, v___x_792_);
                lean_dec(v_next_780_);
                if v_isShared_790_ == 0 {
                    v___x_797_ = v___x_789_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_802_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_802_, 0, v_fst_786_);
                    lean_ctor_set(v_reuseFailAlloc_802_, 1, v_snd_787_);
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
                    lean_box(0),
                );
                lean_inc_n(v_toBind_773_, 2);
                v___x_799_ = lean_apply_4(
                    v_toBind_773_,
                    lean_box(0),
                    lean_box(0),
                    v___x_798_,
                    v___f_778_,
                );
                v___x_800_ = lean_apply_4(
                    v_toBind_773_,
                    lean_box(0),
                    lean_box(0),
                    v___x_799_,
                    v___f_779_,
                );
                v___x_801_ = lean_apply_4(
                    v_toBind_773_,
                    lean_box(0),
                    lean_box(0),
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
    mut v___x_804_: *mut LeanObject,
    mut v_toPure_805_: *mut LeanObject,
    mut v_toBind_806_: *mut LeanObject,
    mut v___f_807_: *mut LeanObject,
    mut v_a_808_: *mut LeanObject,
    mut v_f_809_: *mut LeanObject,
    mut v___x_810_: *mut LeanObject,
    mut v___f_811_: *mut LeanObject,
    mut v___f_812_: *mut LeanObject,
    mut v_next_813_: *mut LeanObject,
    mut v_acc_814_: *mut LeanObject,
    mut v_h_815_: *mut LeanObject,
    mut v_G_816_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1307__boxed_817_: u8 = 0;
    let mut v_res_818_: *mut LeanObject = core::ptr::null_mut();
    v___x_1307__boxed_817_ = (lean_unbox(v___x_810_) as u8);
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
    mut v_inst_819_: *mut LeanObject,
    mut v_a_820_: *mut LeanObject,
    mut v_f_821_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toApplicative_822_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toBind_823_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_825_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_826_: u8 = 0;
    let mut v_toPure_827_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_828_: u8 = 0;
    let mut v___x_829_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_830_: *mut LeanObject = core::ptr::null_mut();
    let mut v_removed_831_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_832_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_833_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_834_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_835_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_836_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_837_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_838_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_839_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_840_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_842_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_843_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_844_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_845_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_846_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_toApplicative_822_ = lean_ctor_get(v_inst_819_, 0);
                v_toBind_823_ = lean_ctor_get(v_inst_819_, 1);
                v_isSharedCheck_846_ = (!lean_is_exclusive(v_inst_819_)) as u8;
                if v_isSharedCheck_846_ == 0 {
                    v___x_825_ = v_inst_819_;
                    v_isShared_826_ = v_isSharedCheck_846_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_toBind_823_);
                    lean_inc(v_toApplicative_822_);
                    lean_dec(v_inst_819_);
                    v___x_825_ = lean_box(0);
                    v_isShared_826_ = v_isSharedCheck_846_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_toPure_827_ = lean_ctor_get(v_toApplicative_822_, 1);
                lean_inc_n(v_toPure_827_, 6);
                lean_dec_ref(v_toApplicative_822_);
                v___x_828_ = 0;
                v___x_829_ = lean_array_get_size(v_a_820_);
                v___x_830_ = lean_box((v___x_828_) as usize);
                v_removed_831_ = lean_mk_array(v___x_829_, v___x_830_);
                v___f_832_ = lean_alloc_closure(
                    l_Array_filterPairsM___redArg___lam__0 as *mut core::ffi::c_void,
                    2,
                    1,
                );
                lean_closure_set(v___f_832_, 0, v_toPure_827_);
                v___f_833_ = lean_alloc_closure(
                    l_Array_filterPairsM___redArg___lam__2 as *mut core::ffi::c_void,
                    2,
                    1,
                );
                lean_closure_set(v___f_833_, 0, v_toPure_827_);
                v___f_834_ = lean_alloc_closure(
                    l_Array_filterPairsM___redArg___lam__1 as *mut core::ffi::c_void,
                    2,
                    1,
                );
                lean_closure_set(v___f_834_, 0, v_toPure_827_);
                v___x_835_ = lean_box((v___x_828_) as usize);
                lean_inc_ref(v_a_820_);
                lean_inc_n(v_toBind_823_, 2);
                v___f_836_ = lean_alloc_closure(
                    l_Array_filterPairsM___redArg___lam__5___boxed as *mut core::ffi::c_void,
                    8,
                    7,
                );
                lean_closure_set(v___f_836_, 0, v___x_829_);
                lean_closure_set(v___f_836_, 1, v_toPure_827_);
                lean_closure_set(v___f_836_, 2, v_toBind_823_);
                lean_closure_set(v___f_836_, 3, v___f_833_);
                lean_closure_set(v___f_836_, 4, v___x_835_);
                lean_closure_set(v___f_836_, 5, v_a_820_);
                lean_closure_set(v___f_836_, 6, v___f_834_);
                v___f_837_ = lean_alloc_closure(
                    l_Array_filterPairsM___redArg___lam__6 as *mut core::ffi::c_void,
                    2,
                    1,
                );
                lean_closure_set(v___f_837_, 0, v_toPure_827_);
                v___x_838_ = lean_box((v___x_828_) as usize);
                lean_inc_ref(v___f_832_);
                v___f_839_ = lean_alloc_closure(
                    l_Array_filterPairsM___redArg___lam__11___boxed as *mut core::ffi::c_void,
                    13,
                    9,
                );
                lean_closure_set(v___f_839_, 0, v___x_829_);
                lean_closure_set(v___f_839_, 1, v_toPure_827_);
                lean_closure_set(v___f_839_, 2, v_toBind_823_);
                lean_closure_set(v___f_839_, 3, v___f_832_);
                lean_closure_set(v___f_839_, 4, v_a_820_);
                lean_closure_set(v___f_839_, 5, v_f_821_);
                lean_closure_set(v___f_839_, 6, v___x_838_);
                lean_closure_set(v___f_839_, 7, v___f_837_);
                lean_closure_set(v___f_839_, 8, v___f_832_);
                v___x_840_ = lean_unsigned_to_nat(0);
                if v_isShared_826_ == 0 {
                    lean_ctor_set(v___x_825_, 1, v___x_840_);
                    lean_ctor_set(v___x_825_, 0, v_removed_831_);
                    v___x_842_ = v___x_825_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_845_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_845_, 0, v_removed_831_);
                    lean_ctor_set(v_reuseFailAlloc_845_, 1, v___x_840_);
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
                    lean_box(0),
                );
                v___x_844_ = lean_apply_4(
                    v_toBind_823_,
                    lean_box(0),
                    lean_box(0),
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
    mut v_m_847_: *mut LeanObject,
    mut v_inst_848_: *mut LeanObject,
    mut v_00_u03b1_849_: *mut LeanObject,
    mut v_a_850_: *mut LeanObject,
    mut v_f_851_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_852_: *mut LeanObject = core::ptr::null_mut();
    v___x_852_ = l_Array_filterPairsM___redArg(v_inst_848_, v_a_850_, v_f_851_);
    return v___x_852_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Array_mask_spec__0___redArg(
    mut v_as_853_: *mut LeanObject,
    mut v_sz_854_: usize,
    mut v_i_855_: usize,
    mut v_b_856_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_858_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_859_: usize = 0;
    let mut v___x_860_: usize = 0;
    let mut v___x_862_: u8 = 0;
    let mut v_snd_863_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_864_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_866_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_867_: u8 = 0;
    let mut v_array_868_: *mut LeanObject = core::ptr::null_mut();
    let mut v_start_869_: *mut LeanObject = core::ptr::null_mut();
    let mut v_stop_870_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_871_: u8 = 0;
    let mut v___x_873_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_874_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_876_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_877_: u8 = 0;
    let mut v_a_878_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_879_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_880_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_881_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_883_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_884_: u8 = 0;
    let mut v___x_886_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_887_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_888_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_890_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_891_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_892_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_893_: u8 = 0;
    let mut v_unused_894_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_895_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_896_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_897_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_862_ = lean_usize_dec_lt(v_i_855_, v_sz_854_);
                if v___x_862_ == 0 {
                    return v_b_856_;
                } else {
                    v_snd_863_ = lean_ctor_get(v_b_856_, 1);
                    v_fst_864_ = lean_ctor_get(v_b_856_, 0);
                    v_isSharedCheck_897_ = (!lean_is_exclusive(v_b_856_)) as u8;
                    if v_isSharedCheck_897_ == 0 {
                        v___x_866_ = v_b_856_;
                        v_isShared_867_ = v_isSharedCheck_897_;
                        state = 2;
                        continue;
                    } else {
                        lean_inc(v_snd_863_);
                        lean_inc(v_fst_864_);
                        lean_dec(v_b_856_);
                        v___x_866_ = lean_box(0);
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
                v_array_868_ = lean_ctor_get(v_snd_863_, 0);
                v_start_869_ = lean_ctor_get(v_snd_863_, 1);
                v_stop_870_ = lean_ctor_get(v_snd_863_, 2);
                v___x_871_ = lean_nat_dec_lt(v_start_869_, v_stop_870_);
                if v___x_871_ == 0 {
                    if v_isShared_867_ == 0 {
                        v___x_873_ = v___x_866_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_874_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_874_, 0, v_fst_864_);
                        lean_ctor_set(v_reuseFailAlloc_874_, 1, v_snd_863_);
                        v___x_873_ = v_reuseFailAlloc_874_;
                        state = 3;
                        continue;
                    }
                } else {
                    lean_inc(v_stop_870_);
                    lean_inc(v_start_869_);
                    lean_inc_ref(v_array_868_);
                    v_isSharedCheck_893_ = (!lean_is_exclusive(v_snd_863_)) as u8;
                    if v_isSharedCheck_893_ == 0 {
                        v_unused_894_ = lean_ctor_get(v_snd_863_, 2);
                        lean_dec(v_unused_894_);
                        v_unused_895_ = lean_ctor_get(v_snd_863_, 1);
                        lean_dec(v_unused_895_);
                        v_unused_896_ = lean_ctor_get(v_snd_863_, 0);
                        lean_dec(v_unused_896_);
                        v___x_876_ = v_snd_863_;
                        v_isShared_877_ = v_isSharedCheck_893_;
                        state = 4;
                        continue;
                    } else {
                        lean_dec(v_snd_863_);
                        v___x_876_ = lean_box(0);
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
                v___x_880_ = lean_unsigned_to_nat(1);
                v___x_881_ = lean_nat_add(v_start_869_, v___x_880_);
                lean_dec(v_start_869_);
                if v_isShared_877_ == 0 {
                    lean_ctor_set(v___x_876_, 1, v___x_881_);
                    v___x_883_ = v___x_876_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_892_ = lean_alloc_ctor(0, 3, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_892_, 0, v_array_868_);
                    lean_ctor_set(v_reuseFailAlloc_892_, 1, v___x_881_);
                    lean_ctor_set(v_reuseFailAlloc_892_, 2, v_stop_870_);
                    v___x_883_ = v_reuseFailAlloc_892_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v___x_884_ = (lean_unbox(v_a_878_) as u8);
                if v___x_884_ == 0 {
                    lean_dec(v___x_879_);
                    if v_isShared_867_ == 0 {
                        lean_ctor_set(v___x_866_, 1, v___x_883_);
                        v___x_886_ = v___x_866_;
                        state = 6;
                        continue;
                    } else {
                        v_reuseFailAlloc_887_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_887_, 0, v_fst_864_);
                        lean_ctor_set(v_reuseFailAlloc_887_, 1, v___x_883_);
                        v___x_886_ = v_reuseFailAlloc_887_;
                        state = 6;
                        continue;
                    }
                } else {
                    v___x_888_ = lean_array_push(v_fst_864_, v___x_879_);
                    if v_isShared_867_ == 0 {
                        lean_ctor_set(v___x_866_, 1, v___x_883_);
                        lean_ctor_set(v___x_866_, 0, v___x_888_);
                        v___x_890_ = v___x_866_;
                        state = 7;
                        continue;
                    } else {
                        v_reuseFailAlloc_891_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_891_, 0, v___x_888_);
                        lean_ctor_set(v_reuseFailAlloc_891_, 1, v___x_883_);
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
    mut v_as_898_: *mut LeanObject,
    mut v_sz_899_: *mut LeanObject,
    mut v_i_900_: *mut LeanObject,
    mut v_b_901_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sz_boxed_902_: usize = 0;
    let mut v_i_boxed_903_: usize = 0;
    let mut v_res_904_: *mut LeanObject = core::ptr::null_mut();
    v_sz_boxed_902_ = lean_unbox_usize(v_sz_899_);
    lean_dec(v_sz_899_);
    v_i_boxed_903_ = lean_unbox_usize(v_i_900_);
    lean_dec(v_i_900_);
    v_res_904_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Array_mask_spec__0___redArg(v_as_898_, v_sz_boxed_902_, v_i_boxed_903_, v_b_901_);
    lean_dec_ref(v_as_898_);
    return v_res_904_;
}
pub unsafe fn l_Array_mask___redArg(
    mut v_mask_907_: *mut LeanObject,
    mut v_xs_908_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_909_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ys_910_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_911_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_912_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_913_: *mut LeanObject = core::ptr::null_mut();
    let mut v_sz_914_: usize = 0;
    let mut v___x_915_: usize = 0;
    let mut v___x_916_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_917_: *mut LeanObject = core::ptr::null_mut();
    v___x_909_ = lean_unsigned_to_nat(0);
    v_ys_910_ = l_Array_mask___redArg___closed__0;
    v___x_911_ = lean_array_get_size(v_xs_908_);
    v___x_912_ = l_Array_toSubarray___redArg(v_xs_908_, v___x_909_, v___x_911_);
    v___x_913_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_913_, 0, v_ys_910_);
    lean_ctor_set(v___x_913_, 1, v___x_912_);
    v_sz_914_ = lean_array_size(v_mask_907_);
    v___x_915_ = 0usize;
    v___x_916_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Array_mask_spec__0___redArg(v_mask_907_, v_sz_914_, v___x_915_, v___x_913_);
    v_fst_917_ = lean_ctor_get(v___x_916_, 0);
    lean_inc(v_fst_917_);
    lean_dec_ref(v___x_916_);
    return v_fst_917_;
}
pub unsafe fn l_Array_mask___redArg___boxed(
    mut v_mask_918_: *mut LeanObject,
    mut v_xs_919_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_920_: *mut LeanObject = core::ptr::null_mut();
    v_res_920_ = l_Array_mask___redArg(v_mask_918_, v_xs_919_);
    lean_dec_ref(v_mask_918_);
    return v_res_920_;
}
pub unsafe fn l_Array_mask(
    mut v_00_u03b1_921_: *mut LeanObject,
    mut v_mask_922_: *mut LeanObject,
    mut v_xs_923_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_924_: *mut LeanObject = core::ptr::null_mut();
    v___x_924_ = l_Array_mask___redArg(v_mask_922_, v_xs_923_);
    return v___x_924_;
}
pub unsafe fn l_Array_mask___boxed(
    mut v_00_u03b1_925_: *mut LeanObject,
    mut v_mask_926_: *mut LeanObject,
    mut v_xs_927_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_928_: *mut LeanObject = core::ptr::null_mut();
    v_res_928_ = l_Array_mask(v_00_u03b1_925_, v_mask_926_, v_xs_927_);
    lean_dec_ref(v_mask_926_);
    return v_res_928_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Array_mask_spec__0(
    mut v_00_u03b1_929_: *mut LeanObject,
    mut v_as_930_: *mut LeanObject,
    mut v_sz_931_: usize,
    mut v_i_932_: usize,
    mut v_b_933_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_934_: *mut LeanObject = core::ptr::null_mut();
    v___x_934_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Array_mask_spec__0___redArg(v_as_930_, v_sz_931_, v_i_932_, v_b_933_);
    return v___x_934_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Array_mask_spec__0___boxed(
    mut v_00_u03b1_935_: *mut LeanObject,
    mut v_as_936_: *mut LeanObject,
    mut v_sz_937_: *mut LeanObject,
    mut v_i_938_: *mut LeanObject,
    mut v_b_939_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sz_boxed_940_: usize = 0;
    let mut v_i_boxed_941_: usize = 0;
    let mut v_res_942_: *mut LeanObject = core::ptr::null_mut();
    v_sz_boxed_940_ = lean_unbox_usize(v_sz_937_);
    lean_dec(v_sz_937_);
    v_i_boxed_941_ = lean_unbox_usize(v_i_938_);
    lean_dec(v_i_938_);
    v_res_942_ =
        l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Array_mask_spec__0(
            v_00_u03b1_935_,
            v_as_936_,
            v_sz_boxed_940_,
            v_i_boxed_941_,
            v_b_939_,
        );
    lean_dec_ref(v_as_936_);
    return v_res_942_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Array_zipMasked_spec__0___redArg(
    mut v_xs_943_: *mut LeanObject,
    mut v_ys_944_: *mut LeanObject,
    mut v_as_945_: *mut LeanObject,
    mut v_sz_946_: usize,
    mut v_i_947_: usize,
    mut v_b_948_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_950_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_951_: usize = 0;
    let mut v___x_952_: usize = 0;
    let mut v___x_954_: u8 = 0;
    let mut v_snd_955_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_956_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_958_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_959_: u8 = 0;
    let mut v_fst_960_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_961_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_963_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_964_: u8 = 0;
    let mut v_a_965_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_966_: u8 = 0;
    let mut v___x_967_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_968_: u8 = 0;
    let mut v___x_970_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_972_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_973_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_974_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_975_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_976_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_977_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_978_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_980_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_982_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_983_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_984_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_985_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_986_: u8 = 0;
    let mut v___x_988_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_990_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_991_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_992_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_993_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_994_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_995_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_996_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_998_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1000_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1001_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1002_: *mut LeanObject = core::ptr::null_mut();
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
                    v_snd_955_ = lean_ctor_get(v_b_948_, 1);
                    v_fst_956_ = lean_ctor_get(v_b_948_, 0);
                    v_isSharedCheck_1004_ = (!lean_is_exclusive(v_b_948_)) as u8;
                    if v_isSharedCheck_1004_ == 0 {
                        v___x_958_ = v_b_948_;
                        v_isShared_959_ = v_isSharedCheck_1004_;
                        state = 2;
                        continue;
                    } else {
                        lean_inc(v_snd_955_);
                        lean_inc(v_fst_956_);
                        lean_dec(v_b_948_);
                        v___x_958_ = lean_box(0);
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
                v_fst_960_ = lean_ctor_get(v_snd_955_, 0);
                v_snd_961_ = lean_ctor_get(v_snd_955_, 1);
                v_isSharedCheck_1003_ = (!lean_is_exclusive(v_snd_955_)) as u8;
                if v_isSharedCheck_1003_ == 0 {
                    v___x_963_ = v_snd_955_;
                    v_isShared_964_ = v_isSharedCheck_1003_;
                    state = 3;
                    continue;
                } else {
                    lean_inc(v_snd_961_);
                    lean_inc(v_fst_960_);
                    lean_dec(v_snd_955_);
                    v___x_963_ = lean_box(0);
                    v_isShared_964_ = v_isSharedCheck_1003_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v_a_965_ = lean_array_uget_borrowed(v_as_945_, v_i_947_);
                v___x_966_ = (lean_unbox(v_a_965_) as u8);
                if v___x_966_ == 0 {
                    v___x_967_ = lean_array_get_size(v_xs_943_);
                    v___x_968_ = lean_nat_dec_lt(v_fst_956_, v___x_967_);
                    if v___x_968_ == 0 {
                        if v_isShared_964_ == 0 {
                            v___x_970_ = v___x_963_;
                            state = 4;
                            continue;
                        } else {
                            v_reuseFailAlloc_974_ = lean_alloc_ctor(0, 2, (0) as u32);
                            lean_ctor_set(v_reuseFailAlloc_974_, 0, v_fst_960_);
                            lean_ctor_set(v_reuseFailAlloc_974_, 1, v_snd_961_);
                            v___x_970_ = v_reuseFailAlloc_974_;
                            state = 4;
                            continue;
                        }
                    } else {
                        v___x_975_ = lean_array_fget_borrowed(v_xs_943_, v_fst_956_);
                        lean_inc(v___x_975_);
                        v___x_976_ = lean_array_push(v_snd_961_, v___x_975_);
                        v___x_977_ = lean_unsigned_to_nat(1);
                        v___x_978_ = lean_nat_add(v_fst_956_, v___x_977_);
                        lean_dec(v_fst_956_);
                        if v_isShared_964_ == 0 {
                            lean_ctor_set(v___x_963_, 1, v___x_976_);
                            v___x_980_ = v___x_963_;
                            state = 6;
                            continue;
                        } else {
                            v_reuseFailAlloc_984_ = lean_alloc_ctor(0, 2, (0) as u32);
                            lean_ctor_set(v_reuseFailAlloc_984_, 0, v_fst_960_);
                            lean_ctor_set(v_reuseFailAlloc_984_, 1, v___x_976_);
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
                            v_reuseFailAlloc_992_ = lean_alloc_ctor(0, 2, (0) as u32);
                            lean_ctor_set(v_reuseFailAlloc_992_, 0, v_fst_960_);
                            lean_ctor_set(v_reuseFailAlloc_992_, 1, v_snd_961_);
                            v___x_988_ = v_reuseFailAlloc_992_;
                            state = 8;
                            continue;
                        }
                    } else {
                        v___x_993_ = lean_array_fget_borrowed(v_ys_944_, v_fst_960_);
                        lean_inc(v___x_993_);
                        v___x_994_ = lean_array_push(v_snd_961_, v___x_993_);
                        v___x_995_ = lean_unsigned_to_nat(1);
                        v___x_996_ = lean_nat_add(v_fst_960_, v___x_995_);
                        lean_dec(v_fst_960_);
                        if v_isShared_964_ == 0 {
                            lean_ctor_set(v___x_963_, 1, v___x_994_);
                            lean_ctor_set(v___x_963_, 0, v___x_996_);
                            v___x_998_ = v___x_963_;
                            state = 10;
                            continue;
                        } else {
                            v_reuseFailAlloc_1002_ = lean_alloc_ctor(0, 2, (0) as u32);
                            lean_ctor_set(v_reuseFailAlloc_1002_, 0, v___x_996_);
                            lean_ctor_set(v_reuseFailAlloc_1002_, 1, v___x_994_);
                            v___x_998_ = v_reuseFailAlloc_1002_;
                            state = 10;
                            continue;
                        }
                    }
                }
            }
            4 => {
                if v_isShared_959_ == 0 {
                    lean_ctor_set(v___x_958_, 1, v___x_970_);
                    v___x_972_ = v___x_958_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_973_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_973_, 0, v_fst_956_);
                    lean_ctor_set(v_reuseFailAlloc_973_, 1, v___x_970_);
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
                    lean_ctor_set(v___x_958_, 1, v___x_980_);
                    lean_ctor_set(v___x_958_, 0, v___x_978_);
                    v___x_982_ = v___x_958_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_983_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_983_, 0, v___x_978_);
                    lean_ctor_set(v_reuseFailAlloc_983_, 1, v___x_980_);
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
                    lean_ctor_set(v___x_958_, 1, v___x_988_);
                    v___x_990_ = v___x_958_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_991_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_991_, 0, v_fst_956_);
                    lean_ctor_set(v_reuseFailAlloc_991_, 1, v___x_988_);
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
                    lean_ctor_set(v___x_958_, 1, v___x_998_);
                    v___x_1000_ = v___x_958_;
                    state = 11;
                    continue;
                } else {
                    v_reuseFailAlloc_1001_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1001_, 0, v_fst_956_);
                    lean_ctor_set(v_reuseFailAlloc_1001_, 1, v___x_998_);
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
    mut v_xs_1005_: *mut LeanObject,
    mut v_ys_1006_: *mut LeanObject,
    mut v_as_1007_: *mut LeanObject,
    mut v_sz_1008_: *mut LeanObject,
    mut v_i_1009_: *mut LeanObject,
    mut v_b_1010_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sz_boxed_1011_: usize = 0;
    let mut v_i_boxed_1012_: usize = 0;
    let mut v_res_1013_: *mut LeanObject = core::ptr::null_mut();
    v_sz_boxed_1011_ = lean_unbox_usize(v_sz_1008_);
    lean_dec(v_sz_1008_);
    v_i_boxed_1012_ = lean_unbox_usize(v_i_1009_);
    lean_dec(v_i_1009_);
    v_res_1013_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Array_zipMasked_spec__0___redArg(v_xs_1005_, v_ys_1006_, v_as_1007_, v_sz_boxed_1011_, v_i_boxed_1012_, v_b_1010_);
    lean_dec_ref(v_as_1007_);
    lean_dec_ref(v_ys_1006_);
    lean_dec_ref(v_xs_1005_);
    return v_res_1013_;
}
pub unsafe fn l_Array_zipMasked___redArg(
    mut v_mask_1020_: *mut LeanObject,
    mut v_xs_1021_: *mut LeanObject,
    mut v_ys_1022_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1023_: *mut LeanObject = core::ptr::null_mut();
    let mut v_sz_1024_: usize = 0;
    let mut v___x_1025_: usize = 0;
    let mut v___x_1026_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_1027_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_1028_: *mut LeanObject = core::ptr::null_mut();
    v___x_1023_ = l_Array_zipMasked___redArg___closed__1;
    v_sz_1024_ = lean_array_size(v_mask_1020_);
    v___x_1025_ = 0usize;
    v___x_1026_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Array_zipMasked_spec__0___redArg(v_xs_1021_, v_ys_1022_, v_mask_1020_, v_sz_1024_, v___x_1025_, v___x_1023_);
    v_snd_1027_ = lean_ctor_get(v___x_1026_, 1);
    lean_inc(v_snd_1027_);
    lean_dec_ref(v___x_1026_);
    v_snd_1028_ = lean_ctor_get(v_snd_1027_, 1);
    lean_inc(v_snd_1028_);
    lean_dec(v_snd_1027_);
    return v_snd_1028_;
}
pub unsafe fn l_Array_zipMasked___redArg___boxed(
    mut v_mask_1029_: *mut LeanObject,
    mut v_xs_1030_: *mut LeanObject,
    mut v_ys_1031_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1032_: *mut LeanObject = core::ptr::null_mut();
    v_res_1032_ = l_Array_zipMasked___redArg(v_mask_1029_, v_xs_1030_, v_ys_1031_);
    lean_dec_ref(v_ys_1031_);
    lean_dec_ref(v_xs_1030_);
    lean_dec_ref(v_mask_1029_);
    return v_res_1032_;
}
pub unsafe fn l_Array_zipMasked(
    mut v_00_u03b1_1033_: *mut LeanObject,
    mut v_mask_1034_: *mut LeanObject,
    mut v_xs_1035_: *mut LeanObject,
    mut v_ys_1036_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1037_: *mut LeanObject = core::ptr::null_mut();
    v___x_1037_ = l_Array_zipMasked___redArg(v_mask_1034_, v_xs_1035_, v_ys_1036_);
    return v___x_1037_;
}
pub unsafe fn l_Array_zipMasked___boxed(
    mut v_00_u03b1_1038_: *mut LeanObject,
    mut v_mask_1039_: *mut LeanObject,
    mut v_xs_1040_: *mut LeanObject,
    mut v_ys_1041_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1042_: *mut LeanObject = core::ptr::null_mut();
    v_res_1042_ = l_Array_zipMasked(v_00_u03b1_1038_, v_mask_1039_, v_xs_1040_, v_ys_1041_);
    lean_dec_ref(v_ys_1041_);
    lean_dec_ref(v_xs_1040_);
    lean_dec_ref(v_mask_1039_);
    return v_res_1042_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Array_zipMasked_spec__0(
    mut v_00_u03b1_1043_: *mut LeanObject,
    mut v_xs_1044_: *mut LeanObject,
    mut v_ys_1045_: *mut LeanObject,
    mut v_as_1046_: *mut LeanObject,
    mut v_sz_1047_: usize,
    mut v_i_1048_: usize,
    mut v_b_1049_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1050_: *mut LeanObject = core::ptr::null_mut();
    v___x_1050_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Array_zipMasked_spec__0___redArg(v_xs_1044_, v_ys_1045_, v_as_1046_, v_sz_1047_, v_i_1048_, v_b_1049_);
    return v___x_1050_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Array_zipMasked_spec__0___boxed(
    mut v_00_u03b1_1051_: *mut LeanObject,
    mut v_xs_1052_: *mut LeanObject,
    mut v_ys_1053_: *mut LeanObject,
    mut v_as_1054_: *mut LeanObject,
    mut v_sz_1055_: *mut LeanObject,
    mut v_i_1056_: *mut LeanObject,
    mut v_b_1057_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sz_boxed_1058_: usize = 0;
    let mut v_i_boxed_1059_: usize = 0;
    let mut v_res_1060_: *mut LeanObject = core::ptr::null_mut();
    v_sz_boxed_1058_ = lean_unbox_usize(v_sz_1055_);
    lean_dec(v_sz_1055_);
    v_i_boxed_1059_ = lean_unbox_usize(v_i_1056_);
    lean_dec(v_i_1056_);
    v_res_1060_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Array_zipMasked_spec__0(v_00_u03b1_1051_, v_xs_1052_, v_ys_1053_, v_as_1054_, v_sz_boxed_1058_, v_i_boxed_1059_, v_b_1057_);
    lean_dec_ref(v_as_1054_);
    lean_dec_ref(v_ys_1053_);
    lean_dec_ref(v_xs_1052_);
    return v_res_1060_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Data_Array(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Init_Data_Stream(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Range_Polymorphic_Nat(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Range_Polymorphic_Iterators(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Data_Array(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_meta_initialized = true;
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lean_Data_Array(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Init_Data_Stream(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Data_Range_Polymorphic_Nat(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Data_Range_Polymorphic_Iterators(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Data_Array(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Lean_Data_Array(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Lean_Data_Array(builtin);
}
