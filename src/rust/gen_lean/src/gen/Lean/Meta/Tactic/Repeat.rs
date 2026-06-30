// Lean compiler output
// Module: Lean.Meta.Tactic.Repeat
// Imports: Lean.Meta.Basic Init.Data.Nat.Linear Init.Omega
use crate::ffi::{
    lean_array_get_size, lean_array_push, lean_array_to_list, lean_nat_dec_eq, lean_nat_dec_le,
    lean_nat_dec_lt, lean_nat_sub, lean_usize_of_nat,
};
use crate::r#gen::Init::Control::Basic::l_Functor_mapRev___redArg;
use crate::r#gen::Init::Data::Array::Basic::{
    l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold, l_Array_appendList,
    l_List_foldl___at___00Array_appendList_spec__0___redArg,
};
use crate::r#gen::Init::Data::Nat::Linear::{
    initialize_Init_Data_Nat_Linear, runtime_initialize_Init_Data_Nat_Linear,
};
use crate::r#gen::Init::Omega::{initialize_Init_Omega, runtime_initialize_Init_Omega};
use crate::r#gen::Init::Prelude::{l_Bool_not___boxed, l_List_foldl___redArg};
use crate::r#gen::Lean::Exception::l_Lean_throwError___redArg;
use crate::r#gen::Lean::Message::l_Lean_stringToMessageData;
use crate::r#gen::Lean::Meta::Basic::{
    initialize_Lean_Meta_Basic, runtime_initialize_Lean_Meta_Basic,
};
use crate::r#gen::Lean::MetavarContext::l_Lean_MVarId_isAssigned___redArg;
use crate::r#gen::Lean::Util::MonadBacktrack::l_Lean_observing_x3f___redArg;
pub static l___private_Lean_Meta_Tactic_Repeat_0__Lean_Meta_repeat_x27Core_go___redArg___lam__1___closed__0_value: leanh::LeanClosureObject<1> = leanh::LeanClosureObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut leanh::LeanObject>()*1) as u16, other: 0, tag: 245 }, m_fun: l_Array_appendList as *const core::ffi::c_void, m_arity: 3, m_num_fixed: 1, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Repeat_0__Lean_Meta_repeat_x27Core_go___redArg___lam__1___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Repeat_0__Lean_Meta_repeat_x27Core_go___redArg___lam__1___closed__0_value) as *mut leanh::LeanObject;
pub static l_Lean_Meta_repeat_x27Core___redArg___lam__1___closed__0_value:
    leanh::LeanClosureObject<0> = leanh::LeanClosureObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Bool_not___boxed as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Meta_repeat_x27Core___redArg___lam__1___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_repeat_x27Core___redArg___lam__1___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Meta_repeat_x27Core___redArg___closed__0_value: leanh::LeanArrayObject<0> =
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
static mut l_Lean_Meta_repeat_x27Core___redArg___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_repeat_x27Core___redArg___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Meta_repeat_x27___redArg___closed__0_value: leanh::LeanClosureObject<0> =
    leanh::LeanClosureObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut leanh::LeanObject>() * 0)
                as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Lean_Meta_repeat_x27___redArg___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Meta_repeat_x27___redArg___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_repeat_x27___redArg___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Meta_repeat1_x27___redArg___lam__0___closed__0_value:
    leanh::LeanStringObject<28> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 28,
    m_capacity: 28,
    m_length: 27,
    m_data: [
        96, 114, 101, 112, 101, 97, 116, 49, 39, 96, 32, 109, 97, 100, 101, 32, 110, 111, 32, 112,
        114, 111, 103, 114, 101, 115, 115, 0,
    ],
};
static mut l_Lean_Meta_repeat1_x27___redArg___lam__0___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_repeat1_x27___redArg___lam__0___closed__0_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Meta_repeat1_x27___redArg___lam__0___closed__1_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_repeat1_x27___redArg___lam__0___closed__1: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub unsafe fn l___private_Lean_Meta_Tactic_Repeat_0__Lean_Meta_repeat_x27Core_go___redArg___lam__0___boxed(
    mut v_a_446_: *mut leanh::LeanObject,
    mut v_head_447_: *mut leanh::LeanObject,
    mut v_inst_448_: *mut leanh::LeanObject,
    mut v_inst_449_: *mut leanh::LeanObject,
    mut v_inst_450_: *mut leanh::LeanObject,
    mut v_inst_451_: *mut leanh::LeanObject,
    mut v_f_452_: *mut leanh::LeanObject,
    mut v_n_453_: *mut leanh::LeanObject,
    mut v_a_454_: *mut leanh::LeanObject,
    mut v_tail_455_: *mut leanh::LeanObject,
    mut v_a_456_: *mut leanh::LeanObject,
    mut v___x_457_: *mut leanh::LeanObject,
    mut v_____do__lift_458_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_a_279__boxed_459_: u8 = 0;
    let mut v___x_282__boxed_460_: u8 = 0;
    let mut v_res_461_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_a_279__boxed_459_ = (leanh::lean_unbox(v_a_454_) as u8);
    v___x_282__boxed_460_ = (leanh::lean_unbox(v___x_457_) as u8);
    v_res_461_ =
        l___private_Lean_Meta_Tactic_Repeat_0__Lean_Meta_repeat_x27Core_go___redArg___lam__0(
            v_a_446_,
            v_head_447_,
            v_inst_448_,
            v_inst_449_,
            v_inst_450_,
            v_inst_451_,
            v_f_452_,
            v_n_453_,
            v_a_279__boxed_459_,
            v_tail_455_,
            v_a_456_,
            v___x_282__boxed_460_,
            v_____do__lift_458_,
        );
    return v_res_461_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Repeat_0__Lean_Meta_repeat_x27Core_go___redArg___lam__1(
    mut v_a_462_: *mut leanh::LeanObject,
    mut v_a_463_: *mut leanh::LeanObject,
    mut v_head_464_: *mut leanh::LeanObject,
    mut v_tail_465_: *mut leanh::LeanObject,
    mut v_a_466_: *mut leanh::LeanObject,
    mut v_a_467_: u8,
    mut v_toPure_468_: *mut leanh::LeanObject,
    mut v_inst_469_: *mut leanh::LeanObject,
    mut v_inst_470_: *mut leanh::LeanObject,
    mut v_inst_471_: *mut leanh::LeanObject,
    mut v_inst_472_: *mut leanh::LeanObject,
    mut v_f_473_: *mut leanh::LeanObject,
    mut v_toBind_474_: *mut leanh::LeanObject,
    mut v_____do__lift_475_: u8,
) -> *mut leanh::LeanObject {
    if v_____do__lift_475_ == 0 {
        let mut v_zero_476_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_isZero_477_: u8 = 0;
        v_zero_476_ = leanh::lean_unsigned_to_nat(0);
        v_isZero_477_ = lean_nat_dec_eq(v_a_462_, v_zero_476_);
        if v_isZero_477_ == 1 {
            let mut v___x_478_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_479_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_480_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_481_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_482_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_483_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_484_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_toBind_474_);
            leanh::lean_dec(v_f_473_);
            leanh::lean_dec_ref(v_inst_472_);
            leanh::lean_dec_ref(v_inst_471_);
            leanh::lean_dec_ref(v_inst_470_);
            leanh::lean_dec_ref(v_inst_469_);
            leanh::lean_dec(v_a_462_);
            v___x_478_ = l___private_Lean_Meta_Tactic_Repeat_0__Lean_Meta_repeat_x27Core_go___redArg___lam__1___closed__0;
            v___x_479_ = lean_array_push(v_a_463_, v_head_464_);
            v___x_480_ =
                l_List_foldl___at___00Array_appendList_spec__0___redArg(v___x_479_, v_tail_465_);
            v___x_481_ = l_List_foldl___redArg(v___x_478_, v___x_480_, v_a_466_);
            v___x_482_ = leanh::lean_box((v_a_467_) as usize);
            v___x_483_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
            leanh::lean_ctor_set(v___x_483_, 0, v___x_482_);
            leanh::lean_ctor_set(v___x_483_, 1, v___x_481_);
            v___x_484_ =
                leanh::lean_apply_2(v_toPure_468_, leanh::lean_box(0), v___x_483_);
            return v___x_484_;
        } else {
            let mut v_one_485_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_n_486_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_487_: u8 = 0;
            let mut v___x_488_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_489_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___f_490_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_491_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_492_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_493_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_toPure_468_);
            v_one_485_ = leanh::lean_unsigned_to_nat(1);
            v_n_486_ = lean_nat_sub(v_a_462_, v_one_485_);
            leanh::lean_dec(v_a_462_);
            v___x_487_ = 1;
            v___x_488_ = leanh::lean_box((v_a_467_) as usize);
            v___x_489_ = leanh::lean_box((v___x_487_) as usize);
            leanh::lean_inc(v_f_473_);
            leanh::lean_inc_ref(v_inst_471_);
            leanh::lean_inc_ref(v_inst_470_);
            leanh::lean_inc_ref(v_inst_469_);
            leanh::lean_inc(v_head_464_);
            v___f_490_ = leanh::lean_alloc_closure(l___private_Lean_Meta_Tactic_Repeat_0__Lean_Meta_repeat_x27Core_go___redArg___lam__0___boxed as *mut core::ffi::c_void, 13, 12);
            leanh::lean_closure_set(v___f_490_, 0, v_a_463_);
            leanh::lean_closure_set(v___f_490_, 1, v_head_464_);
            leanh::lean_closure_set(v___f_490_, 2, v_inst_469_);
            leanh::lean_closure_set(v___f_490_, 3, v_inst_470_);
            leanh::lean_closure_set(v___f_490_, 4, v_inst_471_);
            leanh::lean_closure_set(v___f_490_, 5, v_inst_472_);
            leanh::lean_closure_set(v___f_490_, 6, v_f_473_);
            leanh::lean_closure_set(v___f_490_, 7, v_n_486_);
            leanh::lean_closure_set(v___f_490_, 8, v___x_488_);
            leanh::lean_closure_set(v___f_490_, 9, v_tail_465_);
            leanh::lean_closure_set(v___f_490_, 10, v_a_466_);
            leanh::lean_closure_set(v___f_490_, 11, v___x_489_);
            v___x_491_ = leanh::lean_apply_1(v_f_473_, v_head_464_);
            v___x_492_ =
                l_Lean_observing_x3f___redArg(v_inst_469_, v_inst_471_, v_inst_470_, v___x_491_);
            v___x_493_ = leanh::lean_apply_4(
                v_toBind_474_,
                leanh::lean_box(0),
                leanh::lean_box(0),
                v___x_492_,
                v___f_490_,
            );
            return v___x_493_;
        }
    } else {
        let mut v___x_494_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_toBind_474_);
        leanh::lean_dec(v_toPure_468_);
        leanh::lean_dec(v_head_464_);
        v___x_494_ = l___private_Lean_Meta_Tactic_Repeat_0__Lean_Meta_repeat_x27Core_go___redArg(
            v_inst_469_,
            v_inst_470_,
            v_inst_471_,
            v_inst_472_,
            v_f_473_,
            v_a_462_,
            v_a_467_,
            v_tail_465_,
            v_a_466_,
            v_a_463_,
        );
        return v___x_494_;
    }
}
pub unsafe fn l___private_Lean_Meta_Tactic_Repeat_0__Lean_Meta_repeat_x27Core_go___redArg___lam__1___boxed(
    mut v_a_495_: *mut leanh::LeanObject,
    mut v_a_496_: *mut leanh::LeanObject,
    mut v_head_497_: *mut leanh::LeanObject,
    mut v_tail_498_: *mut leanh::LeanObject,
    mut v_a_499_: *mut leanh::LeanObject,
    mut v_a_500_: *mut leanh::LeanObject,
    mut v_toPure_501_: *mut leanh::LeanObject,
    mut v_inst_502_: *mut leanh::LeanObject,
    mut v_inst_503_: *mut leanh::LeanObject,
    mut v_inst_504_: *mut leanh::LeanObject,
    mut v_inst_505_: *mut leanh::LeanObject,
    mut v_f_506_: *mut leanh::LeanObject,
    mut v_toBind_507_: *mut leanh::LeanObject,
    mut v_____do__lift_508_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_a_314__boxed_509_: u8 = 0;
    let mut v_____do__lift_319__boxed_510_: u8 = 0;
    let mut v_res_511_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_a_314__boxed_509_ = (leanh::lean_unbox(v_a_500_) as u8);
    v_____do__lift_319__boxed_510_ = (leanh::lean_unbox(v_____do__lift_508_) as u8);
    v_res_511_ =
        l___private_Lean_Meta_Tactic_Repeat_0__Lean_Meta_repeat_x27Core_go___redArg___lam__1(
            v_a_495_,
            v_a_496_,
            v_head_497_,
            v_tail_498_,
            v_a_499_,
            v_a_314__boxed_509_,
            v_toPure_501_,
            v_inst_502_,
            v_inst_503_,
            v_inst_504_,
            v_inst_505_,
            v_f_506_,
            v_toBind_507_,
            v_____do__lift_319__boxed_510_,
        );
    return v_res_511_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Repeat_0__Lean_Meta_repeat_x27Core_go___redArg(
    mut v_inst_512_: *mut leanh::LeanObject,
    mut v_inst_513_: *mut leanh::LeanObject,
    mut v_inst_514_: *mut leanh::LeanObject,
    mut v_inst_515_: *mut leanh::LeanObject,
    mut v_f_516_: *mut leanh::LeanObject,
    mut v_a_517_: *mut leanh::LeanObject,
    mut v_a_518_: u8,
    mut v_a_519_: *mut leanh::LeanObject,
    mut v_a_520_: *mut leanh::LeanObject,
    mut v_a_521_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_toApplicative_522_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_524_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_525_: u8 = 0;
    let mut v_toPure_526_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_527_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_529_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_530_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_531_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_532_: u8 = 0;
    let mut v_unused_533_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_534_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_head_535_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_536_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toApplicative_538_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_539_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_540_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_head_541_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_542_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_543_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_544_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_545_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_546_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_a_519_) == 0 {
                    if leanh::lean_obj_tag(v_a_520_) == 0 {
                        v_toApplicative_522_ = leanh::lean_ctor_get(v_inst_512_, 0);
                        leanh::lean_inc_ref(v_toApplicative_522_);
                        leanh::lean_dec(v_a_517_);
                        leanh::lean_dec(v_f_516_);
                        leanh::lean_dec_ref(v_inst_515_);
                        leanh::lean_dec_ref(v_inst_514_);
                        leanh::lean_dec_ref(v_inst_513_);
                        v_isSharedCheck_532_ =
                            (!leanh::lean_is_exclusive(v_inst_512_)) as u8;
                        if v_isSharedCheck_532_ == 0 {
                            v_unused_533_ = leanh::lean_ctor_get(v_inst_512_, 1);
                            leanh::lean_dec(v_unused_533_);
                            v_unused_534_ = leanh::lean_ctor_get(v_inst_512_, 0);
                            leanh::lean_dec(v_unused_534_);
                            v___x_524_ = v_inst_512_;
                            v_isShared_525_ = v_isSharedCheck_532_;
                            state = 1;
                            continue;
                        } else {
                            leanh::lean_dec(v_inst_512_);
                            v___x_524_ = leanh::lean_box(0);
                            v_isShared_525_ = v_isSharedCheck_532_;
                            state = 1;
                            continue;
                        }
                    } else {
                        v_head_535_ = leanh::lean_ctor_get(v_a_520_, 0);
                        leanh::lean_inc(v_head_535_);
                        v_tail_536_ = leanh::lean_ctor_get(v_a_520_, 1);
                        leanh::lean_inc(v_tail_536_);
                        leanh::lean_dec_ref_known(v_a_520_, 2);
                        v_a_519_ = v_head_535_;
                        v_a_520_ = v_tail_536_;
                        state = 0;
                        continue;
                    }
                } else {
                    v_toApplicative_538_ = leanh::lean_ctor_get(v_inst_512_, 0);
                    v_toBind_539_ = leanh::lean_ctor_get(v_inst_512_, 1);
                    leanh::lean_inc_n(v_toBind_539_, 2);
                    v_toPure_540_ = leanh::lean_ctor_get(v_toApplicative_538_, 1);
                    v_head_541_ = leanh::lean_ctor_get(v_a_519_, 0);
                    leanh::lean_inc_n(v_head_541_, 2);
                    v_tail_542_ = leanh::lean_ctor_get(v_a_519_, 1);
                    leanh::lean_inc(v_tail_542_);
                    leanh::lean_dec_ref_known(v_a_519_, 2);
                    v___x_543_ = leanh::lean_box((v_a_518_) as usize);
                    leanh::lean_inc_ref(v_inst_515_);
                    leanh::lean_inc_ref(v_inst_512_);
                    leanh::lean_inc(v_toPure_540_);
                    v___f_544_ = leanh::lean_alloc_closure(l___private_Lean_Meta_Tactic_Repeat_0__Lean_Meta_repeat_x27Core_go___redArg___lam__1___boxed as *mut core::ffi::c_void, 14, 13);
                    leanh::lean_closure_set(v___f_544_, 0, v_a_517_);
                    leanh::lean_closure_set(v___f_544_, 1, v_a_521_);
                    leanh::lean_closure_set(v___f_544_, 2, v_head_541_);
                    leanh::lean_closure_set(v___f_544_, 3, v_tail_542_);
                    leanh::lean_closure_set(v___f_544_, 4, v_a_520_);
                    leanh::lean_closure_set(v___f_544_, 5, v___x_543_);
                    leanh::lean_closure_set(v___f_544_, 6, v_toPure_540_);
                    leanh::lean_closure_set(v___f_544_, 7, v_inst_512_);
                    leanh::lean_closure_set(v___f_544_, 8, v_inst_513_);
                    leanh::lean_closure_set(v___f_544_, 9, v_inst_514_);
                    leanh::lean_closure_set(v___f_544_, 10, v_inst_515_);
                    leanh::lean_closure_set(v___f_544_, 11, v_f_516_);
                    leanh::lean_closure_set(v___f_544_, 12, v_toBind_539_);
                    v___x_545_ =
                        l_Lean_MVarId_isAssigned___redArg(v_inst_512_, v_inst_515_, v_head_541_);
                    v___x_546_ = leanh::lean_apply_4(
                        v_toBind_539_,
                        leanh::lean_box(0),
                        leanh::lean_box(0),
                        v___x_545_,
                        v___f_544_,
                    );
                    return v___x_546_;
                }
            }
            1 => {
                v_toPure_526_ = leanh::lean_ctor_get(v_toApplicative_522_, 1);
                leanh::lean_inc(v_toPure_526_);
                leanh::lean_dec_ref(v_toApplicative_522_);
                v___x_527_ = leanh::lean_box((v_a_518_) as usize);
                if v_isShared_525_ == 0 {
                    leanh::lean_ctor_set(v___x_524_, 1, v_a_521_);
                    leanh::lean_ctor_set(v___x_524_, 0, v___x_527_);
                    v___x_529_ = v___x_524_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_531_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_531_, 0, v___x_527_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_531_, 1, v_a_521_);
                    v___x_529_ = v_reuseFailAlloc_531_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_530_ = leanh::lean_apply_2(
                    v_toPure_526_,
                    leanh::lean_box(0),
                    v___x_529_,
                );
                return v___x_530_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Tactic_Repeat_0__Lean_Meta_repeat_x27Core_go___redArg___lam__0(
    mut v_a_547_: *mut leanh::LeanObject,
    mut v_head_548_: *mut leanh::LeanObject,
    mut v_inst_549_: *mut leanh::LeanObject,
    mut v_inst_550_: *mut leanh::LeanObject,
    mut v_inst_551_: *mut leanh::LeanObject,
    mut v_inst_552_: *mut leanh::LeanObject,
    mut v_f_553_: *mut leanh::LeanObject,
    mut v_n_554_: *mut leanh::LeanObject,
    mut v_a_555_: u8,
    mut v_tail_556_: *mut leanh::LeanObject,
    mut v_a_557_: *mut leanh::LeanObject,
    mut v___x_558_: u8,
    mut v_____do__lift_559_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_____do__lift_559_) == 0 {
        let mut v___x_560_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_561_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_560_ = lean_array_push(v_a_547_, v_head_548_);
        v___x_561_ = l___private_Lean_Meta_Tactic_Repeat_0__Lean_Meta_repeat_x27Core_go___redArg(
            v_inst_549_,
            v_inst_550_,
            v_inst_551_,
            v_inst_552_,
            v_f_553_,
            v_n_554_,
            v_a_555_,
            v_tail_556_,
            v_a_557_,
            v___x_560_,
        );
        return v___x_561_;
    } else {
        let mut v_val_562_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_563_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_564_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_head_548_);
        v_val_562_ = leanh::lean_ctor_get(v_____do__lift_559_, 0);
        leanh::lean_inc(v_val_562_);
        leanh::lean_dec_ref_known(v_____do__lift_559_, 1);
        v___x_563_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
        leanh::lean_ctor_set(v___x_563_, 0, v_tail_556_);
        leanh::lean_ctor_set(v___x_563_, 1, v_a_557_);
        v___x_564_ = l___private_Lean_Meta_Tactic_Repeat_0__Lean_Meta_repeat_x27Core_go___redArg(
            v_inst_549_,
            v_inst_550_,
            v_inst_551_,
            v_inst_552_,
            v_f_553_,
            v_n_554_,
            v___x_558_,
            v_val_562_,
            v___x_563_,
            v_a_547_,
        );
        return v___x_564_;
    }
}
pub unsafe fn l___private_Lean_Meta_Tactic_Repeat_0__Lean_Meta_repeat_x27Core_go___redArg___boxed(
    mut v_inst_565_: *mut leanh::LeanObject,
    mut v_inst_566_: *mut leanh::LeanObject,
    mut v_inst_567_: *mut leanh::LeanObject,
    mut v_inst_568_: *mut leanh::LeanObject,
    mut v_f_569_: *mut leanh::LeanObject,
    mut v_a_570_: *mut leanh::LeanObject,
    mut v_a_571_: *mut leanh::LeanObject,
    mut v_a_572_: *mut leanh::LeanObject,
    mut v_a_573_: *mut leanh::LeanObject,
    mut v_a_574_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_a_294__boxed_575_: u8 = 0;
    let mut v_res_576_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_a_294__boxed_575_ = (leanh::lean_unbox(v_a_571_) as u8);
    v_res_576_ = l___private_Lean_Meta_Tactic_Repeat_0__Lean_Meta_repeat_x27Core_go___redArg(
        v_inst_565_,
        v_inst_566_,
        v_inst_567_,
        v_inst_568_,
        v_f_569_,
        v_a_570_,
        v_a_294__boxed_575_,
        v_a_572_,
        v_a_573_,
        v_a_574_,
    );
    return v_res_576_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Repeat_0__Lean_Meta_repeat_x27Core_go(
    mut v_m_577_: *mut leanh::LeanObject,
    mut v_00_u03b5_578_: *mut leanh::LeanObject,
    mut v_s_579_: *mut leanh::LeanObject,
    mut v_inst_580_: *mut leanh::LeanObject,
    mut v_inst_581_: *mut leanh::LeanObject,
    mut v_inst_582_: *mut leanh::LeanObject,
    mut v_inst_583_: *mut leanh::LeanObject,
    mut v_f_584_: *mut leanh::LeanObject,
    mut v_a_585_: *mut leanh::LeanObject,
    mut v_a_586_: u8,
    mut v_a_587_: *mut leanh::LeanObject,
    mut v_a_588_: *mut leanh::LeanObject,
    mut v_a_589_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_590_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_590_ = l___private_Lean_Meta_Tactic_Repeat_0__Lean_Meta_repeat_x27Core_go___redArg(
        v_inst_580_,
        v_inst_581_,
        v_inst_582_,
        v_inst_583_,
        v_f_584_,
        v_a_585_,
        v_a_586_,
        v_a_587_,
        v_a_588_,
        v_a_589_,
    );
    return v___x_590_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Repeat_0__Lean_Meta_repeat_x27Core_go___boxed(
    mut v_m_591_: *mut leanh::LeanObject,
    mut v_00_u03b5_592_: *mut leanh::LeanObject,
    mut v_s_593_: *mut leanh::LeanObject,
    mut v_inst_594_: *mut leanh::LeanObject,
    mut v_inst_595_: *mut leanh::LeanObject,
    mut v_inst_596_: *mut leanh::LeanObject,
    mut v_inst_597_: *mut leanh::LeanObject,
    mut v_f_598_: *mut leanh::LeanObject,
    mut v_a_599_: *mut leanh::LeanObject,
    mut v_a_600_: *mut leanh::LeanObject,
    mut v_a_601_: *mut leanh::LeanObject,
    mut v_a_602_: *mut leanh::LeanObject,
    mut v_a_603_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_a_457__boxed_604_: u8 = 0;
    let mut v_res_605_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_a_457__boxed_604_ = (leanh::lean_unbox(v_a_600_) as u8);
    v_res_605_ = l___private_Lean_Meta_Tactic_Repeat_0__Lean_Meta_repeat_x27Core_go(
        v_m_591_,
        v_00_u03b5_592_,
        v_s_593_,
        v_inst_594_,
        v_inst_595_,
        v_inst_596_,
        v_inst_597_,
        v_f_598_,
        v_a_599_,
        v_a_457__boxed_604_,
        v_a_601_,
        v_a_602_,
        v_a_603_,
    );
    return v_res_605_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Repeat_0__Lean_Meta_repeat_x27Core_go_match__5_splitter___redArg(
    mut v_x_606_: *mut leanh::LeanObject,
    mut v_x_607_: u8,
    mut v_x_608_: *mut leanh::LeanObject,
    mut v_x_609_: *mut leanh::LeanObject,
    mut v_x_610_: *mut leanh::LeanObject,
    mut v_h__1_611_: *mut leanh::LeanObject,
    mut v_h__2_612_: *mut leanh::LeanObject,
    mut v_h__3_613_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_x_608_) == 0 {
        leanh::lean_dec(v_h__3_613_);
        if leanh::lean_obj_tag(v_x_609_) == 0 {
            let mut v___x_614_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_615_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__2_612_);
            v___x_614_ = leanh::lean_box((v_x_607_) as usize);
            v___x_615_ = leanh::lean_apply_3(v_h__1_611_, v_x_606_, v___x_614_, v_x_610_);
            return v___x_615_;
        } else {
            let mut v_head_616_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_tail_617_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_618_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_619_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__1_611_);
            v_head_616_ = leanh::lean_ctor_get(v_x_609_, 0);
            leanh::lean_inc(v_head_616_);
            v_tail_617_ = leanh::lean_ctor_get(v_x_609_, 1);
            leanh::lean_inc(v_tail_617_);
            leanh::lean_dec_ref_known(v_x_609_, 2);
            v___x_618_ = leanh::lean_box((v_x_607_) as usize);
            v___x_619_ = leanh::lean_apply_5(
                v_h__2_612_,
                v_x_606_,
                v___x_618_,
                v_head_616_,
                v_tail_617_,
                v_x_610_,
            );
            return v___x_619_;
        }
    } else {
        let mut v_head_620_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_tail_621_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_622_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_623_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__2_612_);
        leanh::lean_dec(v_h__1_611_);
        v_head_620_ = leanh::lean_ctor_get(v_x_608_, 0);
        leanh::lean_inc(v_head_620_);
        v_tail_621_ = leanh::lean_ctor_get(v_x_608_, 1);
        leanh::lean_inc(v_tail_621_);
        leanh::lean_dec_ref_known(v_x_608_, 2);
        v___x_622_ = leanh::lean_box((v_x_607_) as usize);
        v___x_623_ = leanh::lean_apply_6(
            v_h__3_613_,
            v_x_606_,
            v___x_622_,
            v_head_620_,
            v_tail_621_,
            v_x_609_,
            v_x_610_,
        );
        return v___x_623_;
    }
}
pub unsafe fn l___private_Lean_Meta_Tactic_Repeat_0__Lean_Meta_repeat_x27Core_go_match__5_splitter___redArg___boxed(
    mut v_x_624_: *mut leanh::LeanObject,
    mut v_x_625_: *mut leanh::LeanObject,
    mut v_x_626_: *mut leanh::LeanObject,
    mut v_x_627_: *mut leanh::LeanObject,
    mut v_x_628_: *mut leanh::LeanObject,
    mut v_h__1_629_: *mut leanh::LeanObject,
    mut v_h__2_630_: *mut leanh::LeanObject,
    mut v_h__3_631_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_x_43__boxed_632_: u8 = 0;
    let mut v_res_633_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_x_43__boxed_632_ = (leanh::lean_unbox(v_x_625_) as u8);
    v_res_633_ = l___private_Lean_Meta_Tactic_Repeat_0__Lean_Meta_repeat_x27Core_go_match__5_splitter___redArg(v_x_624_, v_x_43__boxed_632_, v_x_626_, v_x_627_, v_x_628_, v_h__1_629_, v_h__2_630_, v_h__3_631_);
    return v_res_633_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Repeat_0__Lean_Meta_repeat_x27Core_go_match__5_splitter(
    mut v_motive_634_: *mut leanh::LeanObject,
    mut v_x_635_: *mut leanh::LeanObject,
    mut v_x_636_: u8,
    mut v_x_637_: *mut leanh::LeanObject,
    mut v_x_638_: *mut leanh::LeanObject,
    mut v_x_639_: *mut leanh::LeanObject,
    mut v_h__1_640_: *mut leanh::LeanObject,
    mut v_h__2_641_: *mut leanh::LeanObject,
    mut v_h__3_642_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_x_637_) == 0 {
        leanh::lean_dec(v_h__3_642_);
        if leanh::lean_obj_tag(v_x_638_) == 0 {
            let mut v___x_643_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_644_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__2_641_);
            v___x_643_ = leanh::lean_box((v_x_636_) as usize);
            v___x_644_ = leanh::lean_apply_3(v_h__1_640_, v_x_635_, v___x_643_, v_x_639_);
            return v___x_644_;
        } else {
            let mut v_head_645_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_tail_646_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_647_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_648_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__1_640_);
            v_head_645_ = leanh::lean_ctor_get(v_x_638_, 0);
            leanh::lean_inc(v_head_645_);
            v_tail_646_ = leanh::lean_ctor_get(v_x_638_, 1);
            leanh::lean_inc(v_tail_646_);
            leanh::lean_dec_ref_known(v_x_638_, 2);
            v___x_647_ = leanh::lean_box((v_x_636_) as usize);
            v___x_648_ = leanh::lean_apply_5(
                v_h__2_641_,
                v_x_635_,
                v___x_647_,
                v_head_645_,
                v_tail_646_,
                v_x_639_,
            );
            return v___x_648_;
        }
    } else {
        let mut v_head_649_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_tail_650_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_651_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_652_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__2_641_);
        leanh::lean_dec(v_h__1_640_);
        v_head_649_ = leanh::lean_ctor_get(v_x_637_, 0);
        leanh::lean_inc(v_head_649_);
        v_tail_650_ = leanh::lean_ctor_get(v_x_637_, 1);
        leanh::lean_inc(v_tail_650_);
        leanh::lean_dec_ref_known(v_x_637_, 2);
        v___x_651_ = leanh::lean_box((v_x_636_) as usize);
        v___x_652_ = leanh::lean_apply_6(
            v_h__3_642_,
            v_x_635_,
            v___x_651_,
            v_head_649_,
            v_tail_650_,
            v_x_638_,
            v_x_639_,
        );
        return v___x_652_;
    }
}
pub unsafe fn l___private_Lean_Meta_Tactic_Repeat_0__Lean_Meta_repeat_x27Core_go_match__5_splitter___boxed(
    mut v_motive_653_: *mut leanh::LeanObject,
    mut v_x_654_: *mut leanh::LeanObject,
    mut v_x_655_: *mut leanh::LeanObject,
    mut v_x_656_: *mut leanh::LeanObject,
    mut v_x_657_: *mut leanh::LeanObject,
    mut v_x_658_: *mut leanh::LeanObject,
    mut v_h__1_659_: *mut leanh::LeanObject,
    mut v_h__2_660_: *mut leanh::LeanObject,
    mut v_h__3_661_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_x_78__boxed_662_: u8 = 0;
    let mut v_res_663_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_x_78__boxed_662_ = (leanh::lean_unbox(v_x_655_) as u8);
    v_res_663_ =
        l___private_Lean_Meta_Tactic_Repeat_0__Lean_Meta_repeat_x27Core_go_match__5_splitter(
            v_motive_653_,
            v_x_654_,
            v_x_78__boxed_662_,
            v_x_656_,
            v_x_657_,
            v_x_658_,
            v_h__1_659_,
            v_h__2_660_,
            v_h__3_661_,
        );
    return v_res_663_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Repeat_0__Lean_Meta_repeat_x27Core_go_match__3_splitter___redArg(
    mut v_n_664_: *mut leanh::LeanObject,
    mut v_h__1_665_: *mut leanh::LeanObject,
    mut v_h__2_666_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_zero_667_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isZero_668_: u8 = 0;
    v_zero_667_ = leanh::lean_unsigned_to_nat(0);
    v_isZero_668_ = lean_nat_dec_eq(v_n_664_, v_zero_667_);
    if v_isZero_668_ == 1 {
        let mut v___x_669_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_670_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__2_666_);
        v___x_669_ = leanh::lean_box(0);
        v___x_670_ = leanh::lean_apply_1(v_h__1_665_, v___x_669_);
        return v___x_670_;
    } else {
        let mut v_one_671_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_n_672_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_673_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__1_665_);
        v_one_671_ = leanh::lean_unsigned_to_nat(1);
        v_n_672_ = lean_nat_sub(v_n_664_, v_one_671_);
        v___x_673_ = leanh::lean_apply_1(v_h__2_666_, v_n_672_);
        return v___x_673_;
    }
}
pub unsafe fn l___private_Lean_Meta_Tactic_Repeat_0__Lean_Meta_repeat_x27Core_go_match__3_splitter___redArg___boxed(
    mut v_n_674_: *mut leanh::LeanObject,
    mut v_h__1_675_: *mut leanh::LeanObject,
    mut v_h__2_676_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_677_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_677_ = l___private_Lean_Meta_Tactic_Repeat_0__Lean_Meta_repeat_x27Core_go_match__3_splitter___redArg(v_n_674_, v_h__1_675_, v_h__2_676_);
    leanh::lean_dec(v_n_674_);
    return v_res_677_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Repeat_0__Lean_Meta_repeat_x27Core_go_match__3_splitter(
    mut v_motive_678_: *mut leanh::LeanObject,
    mut v_n_679_: *mut leanh::LeanObject,
    mut v_h__1_680_: *mut leanh::LeanObject,
    mut v_h__2_681_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_zero_682_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isZero_683_: u8 = 0;
    v_zero_682_ = leanh::lean_unsigned_to_nat(0);
    v_isZero_683_ = lean_nat_dec_eq(v_n_679_, v_zero_682_);
    if v_isZero_683_ == 1 {
        let mut v___x_684_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_685_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__2_681_);
        v___x_684_ = leanh::lean_box(0);
        v___x_685_ = leanh::lean_apply_1(v_h__1_680_, v___x_684_);
        return v___x_685_;
    } else {
        let mut v_one_686_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_n_687_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_688_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__1_680_);
        v_one_686_ = leanh::lean_unsigned_to_nat(1);
        v_n_687_ = lean_nat_sub(v_n_679_, v_one_686_);
        v___x_688_ = leanh::lean_apply_1(v_h__2_681_, v_n_687_);
        return v___x_688_;
    }
}
pub unsafe fn l___private_Lean_Meta_Tactic_Repeat_0__Lean_Meta_repeat_x27Core_go_match__3_splitter___boxed(
    mut v_motive_689_: *mut leanh::LeanObject,
    mut v_n_690_: *mut leanh::LeanObject,
    mut v_h__1_691_: *mut leanh::LeanObject,
    mut v_h__2_692_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_693_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_693_ =
        l___private_Lean_Meta_Tactic_Repeat_0__Lean_Meta_repeat_x27Core_go_match__3_splitter(
            v_motive_689_,
            v_n_690_,
            v_h__1_691_,
            v_h__2_692_,
        );
    leanh::lean_dec(v_n_690_);
    return v_res_693_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Repeat_0__List_map__unattach_match__1_splitter___redArg(
    mut v_x_694_: *mut leanh::LeanObject,
    mut v_h__1_695_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_696_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_696_ = leanh::lean_apply_2(v_h__1_695_, v_x_694_, leanh::lean_box(0));
    return v___x_696_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Repeat_0__List_map__unattach_match__1_splitter(
    mut v_00_u03b1_697_: *mut leanh::LeanObject,
    mut v_P_698_: *mut leanh::LeanObject,
    mut v_motive_699_: *mut leanh::LeanObject,
    mut v_x_700_: *mut leanh::LeanObject,
    mut v_h__1_701_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_702_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_702_ = leanh::lean_apply_2(v_h__1_701_, v_x_700_, leanh::lean_box(0));
    return v___x_702_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Repeat_0__Lean_Meta_repeat_x27Core_go_match__1_splitter___redArg(
    mut v_____do__lift_703_: *mut leanh::LeanObject,
    mut v_h__1_704_: *mut leanh::LeanObject,
    mut v_h__2_705_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_____do__lift_703_) == 0 {
        let mut v___x_706_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_707_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__1_704_);
        v___x_706_ = leanh::lean_box(0);
        v___x_707_ = leanh::lean_apply_1(v_h__2_705_, v___x_706_);
        return v___x_707_;
    } else {
        let mut v_val_708_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_709_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__2_705_);
        v_val_708_ = leanh::lean_ctor_get(v_____do__lift_703_, 0);
        leanh::lean_inc(v_val_708_);
        leanh::lean_dec_ref_known(v_____do__lift_703_, 1);
        v___x_709_ = leanh::lean_apply_1(v_h__1_704_, v_val_708_);
        return v___x_709_;
    }
}
pub unsafe fn l___private_Lean_Meta_Tactic_Repeat_0__Lean_Meta_repeat_x27Core_go_match__1_splitter(
    mut v_motive_710_: *mut leanh::LeanObject,
    mut v_____do__lift_711_: *mut leanh::LeanObject,
    mut v_h__1_712_: *mut leanh::LeanObject,
    mut v_h__2_713_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_____do__lift_711_) == 0 {
        let mut v___x_714_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_715_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__1_712_);
        v___x_714_ = leanh::lean_box(0);
        v___x_715_ = leanh::lean_apply_1(v_h__2_713_, v___x_714_);
        return v___x_715_;
    } else {
        let mut v_val_716_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_717_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__2_713_);
        v_val_716_ = leanh::lean_ctor_get(v_____do__lift_711_, 0);
        leanh::lean_inc(v_val_716_);
        leanh::lean_dec_ref_known(v_____do__lift_711_, 1);
        v___x_717_ = leanh::lean_apply_1(v_h__1_712_, v_val_716_);
        return v___x_717_;
    }
}
pub unsafe fn l_Lean_Meta_repeat_x27Core___redArg___lam__0(
    mut v_toPure_718_: *mut leanh::LeanObject,
    mut v_acc_719_: *mut leanh::LeanObject,
    mut v_a_720_: *mut leanh::LeanObject,
    mut v_____do__lift_721_: u8,
) -> *mut leanh::LeanObject {
    if v_____do__lift_721_ == 0 {
        let mut v___x_722_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_a_720_);
        v___x_722_ =
            leanh::lean_apply_2(v_toPure_718_, leanh::lean_box(0), v_acc_719_);
        return v___x_722_;
    } else {
        let mut v___x_723_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_724_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_723_ = lean_array_push(v_acc_719_, v_a_720_);
        v___x_724_ =
            leanh::lean_apply_2(v_toPure_718_, leanh::lean_box(0), v___x_723_);
        return v___x_724_;
    }
}
pub unsafe fn l_Lean_Meta_repeat_x27Core___redArg___lam__0___boxed(
    mut v_toPure_725_: *mut leanh::LeanObject,
    mut v_acc_726_: *mut leanh::LeanObject,
    mut v_a_727_: *mut leanh::LeanObject,
    mut v_____do__lift_728_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_____do__lift_200__boxed_729_: u8 = 0;
    let mut v_res_730_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_____do__lift_200__boxed_729_ = (leanh::lean_unbox(v_____do__lift_728_) as u8);
    v_res_730_ = l_Lean_Meta_repeat_x27Core___redArg___lam__0(
        v_toPure_725_,
        v_acc_726_,
        v_a_727_,
        v_____do__lift_200__boxed_729_,
    );
    return v_res_730_;
}
pub unsafe fn l_Lean_Meta_repeat_x27Core___redArg___lam__1(
    mut v_toFunctor_732_: *mut leanh::LeanObject,
    mut v_toPure_733_: *mut leanh::LeanObject,
    mut v_inst_734_: *mut leanh::LeanObject,
    mut v_inst_735_: *mut leanh::LeanObject,
    mut v_toBind_736_: *mut leanh::LeanObject,
    mut v_acc_737_: *mut leanh::LeanObject,
    mut v_a_738_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_map_739_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_740_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_741_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_742_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_743_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_744_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_map_739_ = leanh::lean_ctor_get(v_toFunctor_732_, 0);
    leanh::lean_inc(v_map_739_);
    leanh::lean_dec_ref(v_toFunctor_732_);
    leanh::lean_inc(v_a_738_);
    v___f_740_ = leanh::lean_alloc_closure(
        l_Lean_Meta_repeat_x27Core___redArg___lam__0___boxed as *mut core::ffi::c_void,
        4,
        3,
    );
    leanh::lean_closure_set(v___f_740_, 0, v_toPure_733_);
    leanh::lean_closure_set(v___f_740_, 1, v_acc_737_);
    leanh::lean_closure_set(v___f_740_, 2, v_a_738_);
    v___x_741_ = l_Lean_Meta_repeat_x27Core___redArg___lam__1___closed__0;
    v___x_742_ = l_Lean_MVarId_isAssigned___redArg(v_inst_734_, v_inst_735_, v_a_738_);
    v___x_743_ = leanh::lean_apply_4(
        v_map_739_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v___x_741_,
        v___x_742_,
    );
    v___x_744_ = leanh::lean_apply_4(
        v_toBind_736_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v___x_743_,
        v___f_740_,
    );
    return v___x_744_;
}
pub unsafe fn l_Lean_Meta_repeat_x27Core___redArg___lam__2(
    mut v_fst_745_: u8,
    mut v_toPure_746_: *mut leanh::LeanObject,
    mut v_____do__lift_747_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_748_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_749_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_750_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_751_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_748_ = lean_array_to_list(v_____do__lift_747_);
    v___x_749_ = leanh::lean_box((v_fst_745_) as usize);
    v___x_750_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_750_, 0, v___x_749_);
    leanh::lean_ctor_set(v___x_750_, 1, v___x_748_);
    v___x_751_ = leanh::lean_apply_2(v_toPure_746_, leanh::lean_box(0), v___x_750_);
    return v___x_751_;
}
pub unsafe fn l_Lean_Meta_repeat_x27Core___redArg___lam__2___boxed(
    mut v_fst_752_: *mut leanh::LeanObject,
    mut v_toPure_753_: *mut leanh::LeanObject,
    mut v_____do__lift_754_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_fst_226__boxed_755_: u8 = 0;
    let mut v_res_756_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_fst_226__boxed_755_ = (leanh::lean_unbox(v_fst_752_) as u8);
    v_res_756_ = l_Lean_Meta_repeat_x27Core___redArg___lam__2(
        v_fst_226__boxed_755_,
        v_toPure_753_,
        v_____do__lift_754_,
    );
    return v_res_756_;
}
pub unsafe fn l_Lean_Meta_repeat_x27Core___redArg___lam__3(
    mut v_toPure_757_: *mut leanh::LeanObject,
    mut v___x_758_: *mut leanh::LeanObject,
    mut v___x_759_: *mut leanh::LeanObject,
    mut v_toBind_760_: *mut leanh::LeanObject,
    mut v_inst_761_: *mut leanh::LeanObject,
    mut v___f_762_: *mut leanh::LeanObject,
    mut v_____x_763_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_fst_764_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_765_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_766_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_767_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_768_: u8 = 0;
    v_fst_764_ = leanh::lean_ctor_get(v_____x_763_, 0);
    leanh::lean_inc(v_fst_764_);
    v_snd_765_ = leanh::lean_ctor_get(v_____x_763_, 1);
    leanh::lean_inc(v_snd_765_);
    leanh::lean_dec_ref(v_____x_763_);
    leanh::lean_inc(v_toPure_757_);
    v___f_766_ = leanh::lean_alloc_closure(
        l_Lean_Meta_repeat_x27Core___redArg___lam__2___boxed as *mut core::ffi::c_void,
        3,
        2,
    );
    leanh::lean_closure_set(v___f_766_, 0, v_fst_764_);
    leanh::lean_closure_set(v___f_766_, 1, v_toPure_757_);
    v___x_767_ = lean_array_get_size(v_snd_765_);
    v___x_768_ = lean_nat_dec_lt(v___x_758_, v___x_767_);
    if v___x_768_ == 0 {
        let mut v___x_769_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_770_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_snd_765_);
        leanh::lean_dec(v___f_762_);
        leanh::lean_dec_ref(v_inst_761_);
        v___x_769_ =
            leanh::lean_apply_2(v_toPure_757_, leanh::lean_box(0), v___x_759_);
        v___x_770_ = leanh::lean_apply_4(
            v_toBind_760_,
            leanh::lean_box(0),
            leanh::lean_box(0),
            v___x_769_,
            v___f_766_,
        );
        return v___x_770_;
    } else {
        let mut v___x_771_: u8 = 0;
        v___x_771_ = lean_nat_dec_le(v___x_767_, v___x_767_);
        if v___x_771_ == 0 {
            if v___x_768_ == 0 {
                let mut v___x_772_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_773_: *mut leanh::LeanObject = core::ptr::null_mut();
                leanh::lean_dec(v_snd_765_);
                leanh::lean_dec(v___f_762_);
                leanh::lean_dec_ref(v_inst_761_);
                v___x_772_ = leanh::lean_apply_2(
                    v_toPure_757_,
                    leanh::lean_box(0),
                    v___x_759_,
                );
                v___x_773_ = leanh::lean_apply_4(
                    v_toBind_760_,
                    leanh::lean_box(0),
                    leanh::lean_box(0),
                    v___x_772_,
                    v___f_766_,
                );
                return v___x_773_;
            } else {
                let mut v___x_774_: usize = 0;
                let mut v___x_775_: usize = 0;
                let mut v___x_776_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_777_: *mut leanh::LeanObject = core::ptr::null_mut();
                leanh::lean_dec(v_toPure_757_);
                v___x_774_ = 0usize;
                v___x_775_ = lean_usize_of_nat(v___x_767_);
                v___x_776_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                    leanh::lean_box(0),
                    leanh::lean_box(0),
                    leanh::lean_box(0),
                    v_inst_761_,
                    v___f_762_,
                    v_snd_765_,
                    v___x_774_,
                    v___x_775_,
                    v___x_759_,
                );
                v___x_777_ = leanh::lean_apply_4(
                    v_toBind_760_,
                    leanh::lean_box(0),
                    leanh::lean_box(0),
                    v___x_776_,
                    v___f_766_,
                );
                return v___x_777_;
            }
        } else {
            let mut v___x_778_: usize = 0;
            let mut v___x_779_: usize = 0;
            let mut v___x_780_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_781_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_toPure_757_);
            v___x_778_ = 0usize;
            v___x_779_ = lean_usize_of_nat(v___x_767_);
            v___x_780_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                leanh::lean_box(0),
                leanh::lean_box(0),
                leanh::lean_box(0),
                v_inst_761_,
                v___f_762_,
                v_snd_765_,
                v___x_778_,
                v___x_779_,
                v___x_759_,
            );
            v___x_781_ = leanh::lean_apply_4(
                v_toBind_760_,
                leanh::lean_box(0),
                leanh::lean_box(0),
                v___x_780_,
                v___f_766_,
            );
            return v___x_781_;
        }
    }
}
pub unsafe fn l_Lean_Meta_repeat_x27Core___redArg___lam__3___boxed(
    mut v_toPure_782_: *mut leanh::LeanObject,
    mut v___x_783_: *mut leanh::LeanObject,
    mut v___x_784_: *mut leanh::LeanObject,
    mut v_toBind_785_: *mut leanh::LeanObject,
    mut v_inst_786_: *mut leanh::LeanObject,
    mut v___f_787_: *mut leanh::LeanObject,
    mut v_____x_788_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_789_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_789_ = l_Lean_Meta_repeat_x27Core___redArg___lam__3(
        v_toPure_782_,
        v___x_783_,
        v___x_784_,
        v_toBind_785_,
        v_inst_786_,
        v___f_787_,
        v_____x_788_,
    );
    leanh::lean_dec(v___x_783_);
    return v_res_789_;
}
pub unsafe fn l_Lean_Meta_repeat_x27Core___redArg(
    mut v_inst_792_: *mut leanh::LeanObject,
    mut v_inst_793_: *mut leanh::LeanObject,
    mut v_inst_794_: *mut leanh::LeanObject,
    mut v_inst_795_: *mut leanh::LeanObject,
    mut v_f_796_: *mut leanh::LeanObject,
    mut v_goals_797_: *mut leanh::LeanObject,
    mut v_maxIters_798_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_toApplicative_799_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_800_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toFunctor_801_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_802_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_803_: u8 = 0;
    let mut v___x_804_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_805_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_806_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_807_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_808_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_809_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_810_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_799_ = leanh::lean_ctor_get(v_inst_792_, 0);
    v_toBind_800_ = leanh::lean_ctor_get(v_inst_792_, 1);
    leanh::lean_inc_n(v_toBind_800_, 3);
    v_toFunctor_801_ = leanh::lean_ctor_get(v_toApplicative_799_, 0);
    v_toPure_802_ = leanh::lean_ctor_get(v_toApplicative_799_, 1);
    leanh::lean_inc_n(v_toPure_802_, 2);
    v___x_803_ = 0;
    v___x_804_ = leanh::lean_box(0);
    v___x_805_ = leanh::lean_unsigned_to_nat(0);
    v___x_806_ = l_Lean_Meta_repeat_x27Core___redArg___closed__0;
    leanh::lean_inc_ref(v_inst_795_);
    leanh::lean_inc_ref_n(v_inst_792_, 2);
    v___x_807_ = l___private_Lean_Meta_Tactic_Repeat_0__Lean_Meta_repeat_x27Core_go___redArg(
        v_inst_792_,
        v_inst_793_,
        v_inst_794_,
        v_inst_795_,
        v_f_796_,
        v_maxIters_798_,
        v___x_803_,
        v_goals_797_,
        v___x_804_,
        v___x_806_,
    );
    leanh::lean_inc_ref(v_toFunctor_801_);
    v___f_808_ = leanh::lean_alloc_closure(
        l_Lean_Meta_repeat_x27Core___redArg___lam__1 as *mut core::ffi::c_void,
        7,
        5,
    );
    leanh::lean_closure_set(v___f_808_, 0, v_toFunctor_801_);
    leanh::lean_closure_set(v___f_808_, 1, v_toPure_802_);
    leanh::lean_closure_set(v___f_808_, 2, v_inst_792_);
    leanh::lean_closure_set(v___f_808_, 3, v_inst_795_);
    leanh::lean_closure_set(v___f_808_, 4, v_toBind_800_);
    v___f_809_ = leanh::lean_alloc_closure(
        l_Lean_Meta_repeat_x27Core___redArg___lam__3___boxed as *mut core::ffi::c_void,
        7,
        6,
    );
    leanh::lean_closure_set(v___f_809_, 0, v_toPure_802_);
    leanh::lean_closure_set(v___f_809_, 1, v___x_805_);
    leanh::lean_closure_set(v___f_809_, 2, v___x_806_);
    leanh::lean_closure_set(v___f_809_, 3, v_toBind_800_);
    leanh::lean_closure_set(v___f_809_, 4, v_inst_792_);
    leanh::lean_closure_set(v___f_809_, 5, v___f_808_);
    v___x_810_ = leanh::lean_apply_4(
        v_toBind_800_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v___x_807_,
        v___f_809_,
    );
    return v___x_810_;
}
pub unsafe fn l_Lean_Meta_repeat_x27Core(
    mut v_m_811_: *mut leanh::LeanObject,
    mut v_00_u03b5_812_: *mut leanh::LeanObject,
    mut v_s_813_: *mut leanh::LeanObject,
    mut v_inst_814_: *mut leanh::LeanObject,
    mut v_inst_815_: *mut leanh::LeanObject,
    mut v_inst_816_: *mut leanh::LeanObject,
    mut v_inst_817_: *mut leanh::LeanObject,
    mut v_f_818_: *mut leanh::LeanObject,
    mut v_goals_819_: *mut leanh::LeanObject,
    mut v_maxIters_820_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_821_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_821_ = l_Lean_Meta_repeat_x27Core___redArg(
        v_inst_814_,
        v_inst_815_,
        v_inst_816_,
        v_inst_817_,
        v_f_818_,
        v_goals_819_,
        v_maxIters_820_,
    );
    return v___x_821_;
}
pub unsafe fn l_Lean_Meta_repeat_x27___redArg___lam__0(
    mut v_x_822_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_snd_823_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_snd_823_ = leanh::lean_ctor_get(v_x_822_, 1);
    leanh::lean_inc(v_snd_823_);
    return v_snd_823_;
}
pub unsafe fn l_Lean_Meta_repeat_x27___redArg___lam__0___boxed(
    mut v_x_824_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_825_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_825_ = l_Lean_Meta_repeat_x27___redArg___lam__0(v_x_824_);
    leanh::lean_dec_ref(v_x_824_);
    return v_res_825_;
}
pub unsafe fn l_Lean_Meta_repeat_x27___redArg(
    mut v_inst_827_: *mut leanh::LeanObject,
    mut v_inst_828_: *mut leanh::LeanObject,
    mut v_inst_829_: *mut leanh::LeanObject,
    mut v_inst_830_: *mut leanh::LeanObject,
    mut v_f_831_: *mut leanh::LeanObject,
    mut v_goals_832_: *mut leanh::LeanObject,
    mut v_maxIters_833_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_toApplicative_834_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toFunctor_835_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_836_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_837_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_838_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_834_ = leanh::lean_ctor_get(v_inst_827_, 0);
    v_toFunctor_835_ = leanh::lean_ctor_get(v_toApplicative_834_, 0);
    leanh::lean_inc_ref(v_toFunctor_835_);
    v___f_836_ = l_Lean_Meta_repeat_x27___redArg___closed__0;
    v___x_837_ = l_Lean_Meta_repeat_x27Core___redArg(
        v_inst_827_,
        v_inst_828_,
        v_inst_829_,
        v_inst_830_,
        v_f_831_,
        v_goals_832_,
        v_maxIters_833_,
    );
    v___x_838_ = l_Functor_mapRev___redArg(v_toFunctor_835_, v___x_837_, v___f_836_);
    return v___x_838_;
}
pub unsafe fn l_Lean_Meta_repeat_x27(
    mut v_m_839_: *mut leanh::LeanObject,
    mut v_00_u03b5_840_: *mut leanh::LeanObject,
    mut v_s_841_: *mut leanh::LeanObject,
    mut v_inst_842_: *mut leanh::LeanObject,
    mut v_inst_843_: *mut leanh::LeanObject,
    mut v_inst_844_: *mut leanh::LeanObject,
    mut v_inst_845_: *mut leanh::LeanObject,
    mut v_f_846_: *mut leanh::LeanObject,
    mut v_goals_847_: *mut leanh::LeanObject,
    mut v_maxIters_848_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_849_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_849_ = l_Lean_Meta_repeat_x27___redArg(
        v_inst_842_,
        v_inst_843_,
        v_inst_844_,
        v_inst_845_,
        v_f_846_,
        v_goals_847_,
        v_maxIters_848_,
    );
    return v___x_849_;
}
pub unsafe fn _init_l_Lean_Meta_repeat1_x27___redArg___lam__0___closed__1()
-> *mut leanh::LeanObject {
    let mut v___x_851_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_852_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_851_ = l_Lean_Meta_repeat1_x27___redArg___lam__0___closed__0;
    v___x_852_ = l_Lean_stringToMessageData(v___x_851_);
    return v___x_852_;
}
pub unsafe fn l_Lean_Meta_repeat1_x27___redArg___lam__0(
    mut v_toPure_853_: *mut leanh::LeanObject,
    mut v_inst_854_: *mut leanh::LeanObject,
    mut v_inst_855_: *mut leanh::LeanObject,
    mut v_____x_856_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_fst_857_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_858_: u8 = 0;
    v_fst_857_ = leanh::lean_ctor_get(v_____x_856_, 0);
    v___x_858_ = (leanh::lean_unbox(v_fst_857_) as u8);
    if v___x_858_ == 1 {
        let mut v_snd_859_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_860_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec_ref(v_inst_855_);
        leanh::lean_dec_ref(v_inst_854_);
        v_snd_859_ = leanh::lean_ctor_get(v_____x_856_, 1);
        leanh::lean_inc(v_snd_859_);
        leanh::lean_dec_ref(v_____x_856_);
        v___x_860_ =
            leanh::lean_apply_2(v_toPure_853_, leanh::lean_box(0), v_snd_859_);
        return v___x_860_;
    } else {
        let mut v___x_861_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_862_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec_ref(v_____x_856_);
        leanh::lean_dec(v_toPure_853_);
        v___x_861_ = leanh::lean_obj_once(
            core::ptr::addr_of_mut!(l_Lean_Meta_repeat1_x27___redArg___lam__0___closed__1),
            core::ptr::addr_of_mut!(l_Lean_Meta_repeat1_x27___redArg___lam__0___closed__1_once),
            _init_l_Lean_Meta_repeat1_x27___redArg___lam__0___closed__1,
        );
        v___x_862_ = l_Lean_throwError___redArg(v_inst_854_, v_inst_855_, v___x_861_);
        return v___x_862_;
    }
}
pub unsafe fn l_Lean_Meta_repeat1_x27___redArg(
    mut v_inst_863_: *mut leanh::LeanObject,
    mut v_inst_864_: *mut leanh::LeanObject,
    mut v_inst_865_: *mut leanh::LeanObject,
    mut v_inst_866_: *mut leanh::LeanObject,
    mut v_inst_867_: *mut leanh::LeanObject,
    mut v_f_868_: *mut leanh::LeanObject,
    mut v_goals_869_: *mut leanh::LeanObject,
    mut v_maxIters_870_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_toApplicative_871_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_872_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_873_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_874_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_875_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_876_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_871_ = leanh::lean_ctor_get(v_inst_863_, 0);
    v_toBind_872_ = leanh::lean_ctor_get(v_inst_863_, 1);
    leanh::lean_inc(v_toBind_872_);
    v_toPure_873_ = leanh::lean_ctor_get(v_toApplicative_871_, 1);
    leanh::lean_inc(v_toPure_873_);
    leanh::lean_inc_ref(v_inst_863_);
    v___x_874_ = l_Lean_Meta_repeat_x27Core___redArg(
        v_inst_863_,
        v_inst_865_,
        v_inst_866_,
        v_inst_867_,
        v_f_868_,
        v_goals_869_,
        v_maxIters_870_,
    );
    v___f_875_ = leanh::lean_alloc_closure(
        l_Lean_Meta_repeat1_x27___redArg___lam__0 as *mut core::ffi::c_void,
        4,
        3,
    );
    leanh::lean_closure_set(v___f_875_, 0, v_toPure_873_);
    leanh::lean_closure_set(v___f_875_, 1, v_inst_863_);
    leanh::lean_closure_set(v___f_875_, 2, v_inst_864_);
    v___x_876_ = leanh::lean_apply_4(
        v_toBind_872_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v___x_874_,
        v___f_875_,
    );
    return v___x_876_;
}
pub unsafe fn l_Lean_Meta_repeat1_x27(
    mut v_m_877_: *mut leanh::LeanObject,
    mut v_00_u03b5_878_: *mut leanh::LeanObject,
    mut v_s_879_: *mut leanh::LeanObject,
    mut v_inst_880_: *mut leanh::LeanObject,
    mut v_inst_881_: *mut leanh::LeanObject,
    mut v_inst_882_: *mut leanh::LeanObject,
    mut v_inst_883_: *mut leanh::LeanObject,
    mut v_inst_884_: *mut leanh::LeanObject,
    mut v_f_885_: *mut leanh::LeanObject,
    mut v_goals_886_: *mut leanh::LeanObject,
    mut v_maxIters_887_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_888_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_888_ = l_Lean_Meta_repeat1_x27___redArg(
        v_inst_880_,
        v_inst_881_,
        v_inst_882_,
        v_inst_883_,
        v_inst_884_,
        v_f_885_,
        v_goals_886_,
        v_maxIters_887_,
    );
    return v___x_888_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Meta_Tactic_Repeat(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Meta_Basic(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Nat_Linear(builtin);
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
pub unsafe fn meta_initialize_Lean_Meta_Tactic_Repeat(
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
pub unsafe fn initialize_Lean_Meta_Tactic_Repeat(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Meta_Basic(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Nat_Linear(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_Omega(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_Repeat(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_Meta_Tactic_Repeat(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return initialize_Lean_Meta_Tactic_Repeat(builtin);
}