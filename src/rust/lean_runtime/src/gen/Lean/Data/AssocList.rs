// Lean compiler output
// Module: Lean.Data.AssocList
// Imports: Init.Data.List.Impl
use crate::r#gen::Init::Control::Id::{
    l_Id_instMonad___lam__0, l_Id_instMonad___lam__1___boxed, l_Id_instMonad___lam__2___boxed,
    l_Id_instMonad___lam__3, l_Id_instMonad___lam__4___boxed, l_Id_instMonad___lam__5___boxed,
    l_Id_instMonad___lam__6,
};
use crate::r#gen::Init::Data::List::Basic::l_List_reverse___redArg;
use crate::r#gen::Init::Data::List::Impl::{
    initialize_Init_Data_List_Impl, runtime_initialize_Init_Data_List_Impl,
};
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_alloc_closure, lean_alloc_ctor, lean_apply_1,
    lean_apply_2, lean_apply_3, lean_apply_4, lean_box, lean_closure_set, lean_ctor_get,
    lean_ctor_set, lean_dec, lean_dec_ref, lean_dec_ref_known, lean_del_object, lean_inc,
    lean_inc_n, lean_inc_ref, lean_io_result_is_error, lean_io_result_mk_ok, lean_is_exclusive,
    lean_obj_tag, lean_unbox, lean_unsigned_to_nat,
};
pub static l_Lean_AssocList_foldl___redArg___closed__0_value: LeanClosureObject<0> =
    LeanClosureObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Id_instMonad___lam__0 as *const core::ffi::c_void,
        m_arity: 4,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_AssocList_foldl___redArg___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_AssocList_foldl___redArg___closed__0_value) as *mut LeanObject;
pub static l_Lean_AssocList_foldl___redArg___closed__1_value: LeanClosureObject<0> =
    LeanClosureObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Id_instMonad___lam__1___boxed as *const core::ffi::c_void,
        m_arity: 4,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_AssocList_foldl___redArg___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_AssocList_foldl___redArg___closed__1_value) as *mut LeanObject;
pub static l_Lean_AssocList_foldl___redArg___closed__2_value: LeanClosureObject<0> =
    LeanClosureObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Id_instMonad___lam__2___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_AssocList_foldl___redArg___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_AssocList_foldl___redArg___closed__2_value) as *mut LeanObject;
pub static l_Lean_AssocList_foldl___redArg___closed__3_value: LeanClosureObject<0> =
    LeanClosureObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Id_instMonad___lam__3 as *const core::ffi::c_void,
        m_arity: 4,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_AssocList_foldl___redArg___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_AssocList_foldl___redArg___closed__3_value) as *mut LeanObject;
pub static l_Lean_AssocList_foldl___redArg___closed__4_value: LeanClosureObject<0> =
    LeanClosureObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Id_instMonad___lam__4___boxed as *const core::ffi::c_void,
        m_arity: 4,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_AssocList_foldl___redArg___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_AssocList_foldl___redArg___closed__4_value) as *mut LeanObject;
pub static l_Lean_AssocList_foldl___redArg___closed__5_value: LeanClosureObject<0> =
    LeanClosureObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Id_instMonad___lam__5___boxed as *const core::ffi::c_void,
        m_arity: 4,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_AssocList_foldl___redArg___closed__5: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_AssocList_foldl___redArg___closed__5_value) as *mut LeanObject;
pub static l_Lean_AssocList_foldl___redArg___closed__6_value: LeanClosureObject<0> =
    LeanClosureObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Id_instMonad___lam__6 as *const core::ffi::c_void,
        m_arity: 4,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_AssocList_foldl___redArg___closed__6: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_AssocList_foldl___redArg___closed__6_value) as *mut LeanObject;
pub static l_Lean_AssocList_foldl___redArg___closed__7_value: LeanCtorObject<2> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 0,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_AssocList_foldl___redArg___closed__0_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_AssocList_foldl___redArg___closed__1_value) as *mut LeanObject,
    ],
};
static mut l_Lean_AssocList_foldl___redArg___closed__7: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_AssocList_foldl___redArg___closed__7_value) as *mut LeanObject;
pub static l_Lean_AssocList_foldl___redArg___closed__8_value: LeanCtorObject<5> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 5
            + 0) as u16,
        other: 5,
        tag: 0,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_AssocList_foldl___redArg___closed__7_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_AssocList_foldl___redArg___closed__2_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_AssocList_foldl___redArg___closed__3_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_AssocList_foldl___redArg___closed__4_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_AssocList_foldl___redArg___closed__5_value) as *mut LeanObject,
    ],
};
static mut l_Lean_AssocList_foldl___redArg___closed__8: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_AssocList_foldl___redArg___closed__8_value) as *mut LeanObject;
pub static l_Lean_AssocList_foldl___redArg___closed__9_value: LeanCtorObject<2> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 0,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_AssocList_foldl___redArg___closed__8_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_AssocList_foldl___redArg___closed__6_value) as *mut LeanObject,
    ],
};
static mut l_Lean_AssocList_foldl___redArg___closed__9: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_AssocList_foldl___redArg___closed__9_value) as *mut LeanObject;
pub unsafe fn l_Lean_AssocList_ctorIdx___redArg(mut v_x_519_: *mut LeanObject) -> *mut LeanObject {
    if lean_obj_tag(v_x_519_) == 0 {
        let mut v___x_520_: *mut LeanObject = core::ptr::null_mut();
        v___x_520_ = lean_unsigned_to_nat(0);
        return v___x_520_;
    } else {
        let mut v___x_521_: *mut LeanObject = core::ptr::null_mut();
        v___x_521_ = lean_unsigned_to_nat(1);
        return v___x_521_;
    }
}
pub unsafe fn l_Lean_AssocList_ctorIdx___redArg___boxed(
    mut v_x_522_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_523_: *mut LeanObject = core::ptr::null_mut();
    v_res_523_ = l_Lean_AssocList_ctorIdx___redArg(v_x_522_);
    lean_dec(v_x_522_);
    return v_res_523_;
}
pub unsafe fn l_Lean_AssocList_ctorIdx(
    mut v_00_u03b1_524_: *mut LeanObject,
    mut v_00_u03b2_525_: *mut LeanObject,
    mut v_x_526_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_527_: *mut LeanObject = core::ptr::null_mut();
    v___x_527_ = l_Lean_AssocList_ctorIdx___redArg(v_x_526_);
    return v___x_527_;
}
pub unsafe fn l_Lean_AssocList_ctorIdx___boxed(
    mut v_00_u03b1_528_: *mut LeanObject,
    mut v_00_u03b2_529_: *mut LeanObject,
    mut v_x_530_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_531_: *mut LeanObject = core::ptr::null_mut();
    v_res_531_ = l_Lean_AssocList_ctorIdx(v_00_u03b1_528_, v_00_u03b2_529_, v_x_530_);
    lean_dec(v_x_530_);
    return v_res_531_;
}
pub unsafe fn l_Lean_AssocList_ctorElim___redArg(
    mut v_t_532_: *mut LeanObject,
    mut v_k_533_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_t_532_) == 0 {
        return v_k_533_;
    } else {
        let mut v_key_534_: *mut LeanObject = core::ptr::null_mut();
        let mut v_value_535_: *mut LeanObject = core::ptr::null_mut();
        let mut v_tail_536_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_537_: *mut LeanObject = core::ptr::null_mut();
        v_key_534_ = lean_ctor_get(v_t_532_, 0);
        lean_inc(v_key_534_);
        v_value_535_ = lean_ctor_get(v_t_532_, 1);
        lean_inc(v_value_535_);
        v_tail_536_ = lean_ctor_get(v_t_532_, 2);
        lean_inc(v_tail_536_);
        lean_dec_ref_known(v_t_532_, 3);
        v___x_537_ = lean_apply_3(v_k_533_, v_key_534_, v_value_535_, v_tail_536_);
        return v___x_537_;
    }
}
pub unsafe fn l_Lean_AssocList_ctorElim(
    mut v_00_u03b1_538_: *mut LeanObject,
    mut v_00_u03b2_539_: *mut LeanObject,
    mut v_motive_540_: *mut LeanObject,
    mut v_ctorIdx_541_: *mut LeanObject,
    mut v_t_542_: *mut LeanObject,
    mut v_h_543_: *mut LeanObject,
    mut v_k_544_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_545_: *mut LeanObject = core::ptr::null_mut();
    v___x_545_ = l_Lean_AssocList_ctorElim___redArg(v_t_542_, v_k_544_);
    return v___x_545_;
}
pub unsafe fn l_Lean_AssocList_ctorElim___boxed(
    mut v_00_u03b1_546_: *mut LeanObject,
    mut v_00_u03b2_547_: *mut LeanObject,
    mut v_motive_548_: *mut LeanObject,
    mut v_ctorIdx_549_: *mut LeanObject,
    mut v_t_550_: *mut LeanObject,
    mut v_h_551_: *mut LeanObject,
    mut v_k_552_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_553_: *mut LeanObject = core::ptr::null_mut();
    v_res_553_ = l_Lean_AssocList_ctorElim(
        v_00_u03b1_546_,
        v_00_u03b2_547_,
        v_motive_548_,
        v_ctorIdx_549_,
        v_t_550_,
        v_h_551_,
        v_k_552_,
    );
    lean_dec(v_ctorIdx_549_);
    return v_res_553_;
}
pub unsafe fn l_Lean_AssocList_nil_elim___redArg(
    mut v_t_554_: *mut LeanObject,
    mut v_nil_555_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_556_: *mut LeanObject = core::ptr::null_mut();
    v___x_556_ = l_Lean_AssocList_ctorElim___redArg(v_t_554_, v_nil_555_);
    return v___x_556_;
}
pub unsafe fn l_Lean_AssocList_nil_elim(
    mut v_00_u03b1_557_: *mut LeanObject,
    mut v_00_u03b2_558_: *mut LeanObject,
    mut v_motive_559_: *mut LeanObject,
    mut v_t_560_: *mut LeanObject,
    mut v_h_561_: *mut LeanObject,
    mut v_nil_562_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_563_: *mut LeanObject = core::ptr::null_mut();
    v___x_563_ = l_Lean_AssocList_ctorElim___redArg(v_t_560_, v_nil_562_);
    return v___x_563_;
}
pub unsafe fn l_Lean_AssocList_cons_elim___redArg(
    mut v_t_564_: *mut LeanObject,
    mut v_cons_565_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_566_: *mut LeanObject = core::ptr::null_mut();
    v___x_566_ = l_Lean_AssocList_ctorElim___redArg(v_t_564_, v_cons_565_);
    return v___x_566_;
}
pub unsafe fn l_Lean_AssocList_cons_elim(
    mut v_00_u03b1_567_: *mut LeanObject,
    mut v_00_u03b2_568_: *mut LeanObject,
    mut v_motive_569_: *mut LeanObject,
    mut v_t_570_: *mut LeanObject,
    mut v_h_571_: *mut LeanObject,
    mut v_cons_572_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_573_: *mut LeanObject = core::ptr::null_mut();
    v___x_573_ = l_Lean_AssocList_ctorElim___redArg(v_t_570_, v_cons_572_);
    return v___x_573_;
}
pub unsafe fn l_Lean_instInhabitedAssocList_default(
    mut v_00_u03b1_574_: *mut LeanObject,
    mut v_00_u03b2_575_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_576_: *mut LeanObject = core::ptr::null_mut();
    v___x_576_ = lean_box(0);
    return v___x_576_;
}
pub unsafe fn l_Lean_instInhabitedAssocList(
    mut v_a_577_: *mut LeanObject,
    mut v_a_578_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_579_: *mut LeanObject = core::ptr::null_mut();
    v___x_579_ = lean_box(0);
    return v___x_579_;
}
pub unsafe fn l_Lean_AssocList_empty(
    mut v_00_u03b1_580_: *mut LeanObject,
    mut v_00_u03b2_581_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_582_: *mut LeanObject = core::ptr::null_mut();
    v___x_582_ = lean_box(0);
    return v___x_582_;
}
pub unsafe fn l_Lean_AssocList_instEmptyCollection(
    mut v_00_u03b1_583_: *mut LeanObject,
    mut v_00_u03b2_584_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_585_: *mut LeanObject = core::ptr::null_mut();
    v___x_585_ = lean_box(0);
    return v___x_585_;
}
pub unsafe fn l_Lean_AssocList_insertNew___redArg(
    mut v_m_586_: *mut LeanObject,
    mut v_k_587_: *mut LeanObject,
    mut v_v_588_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_589_: *mut LeanObject = core::ptr::null_mut();
    v___x_589_ = lean_alloc_ctor(1, 3, (0) as u32);
    lean_ctor_set(v___x_589_, 0, v_k_587_);
    lean_ctor_set(v___x_589_, 1, v_v_588_);
    lean_ctor_set(v___x_589_, 2, v_m_586_);
    return v___x_589_;
}
pub unsafe fn l_Lean_AssocList_insertNew(
    mut v_00_u03b1_590_: *mut LeanObject,
    mut v_00_u03b2_591_: *mut LeanObject,
    mut v_m_592_: *mut LeanObject,
    mut v_k_593_: *mut LeanObject,
    mut v_v_594_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_595_: *mut LeanObject = core::ptr::null_mut();
    v___x_595_ = lean_alloc_ctor(1, 3, (0) as u32);
    lean_ctor_set(v___x_595_, 0, v_k_593_);
    lean_ctor_set(v___x_595_, 1, v_v_594_);
    lean_ctor_set(v___x_595_, 2, v_m_592_);
    return v___x_595_;
}
pub unsafe fn l_Lean_AssocList_isEmpty___redArg(mut v_x_596_: *mut LeanObject) -> u8 {
    if lean_obj_tag(v_x_596_) == 0 {
        let mut v___x_597_: u8 = 0;
        v___x_597_ = 1;
        return v___x_597_;
    } else {
        let mut v___x_598_: u8 = 0;
        v___x_598_ = 0;
        return v___x_598_;
    }
}
pub unsafe fn l_Lean_AssocList_isEmpty___redArg___boxed(
    mut v_x_599_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_600_: u8 = 0;
    let mut v_r_601_: *mut LeanObject = core::ptr::null_mut();
    v_res_600_ = l_Lean_AssocList_isEmpty___redArg(v_x_599_);
    lean_dec(v_x_599_);
    v_r_601_ = lean_box((v_res_600_) as usize);
    return v_r_601_;
}
pub unsafe fn l_Lean_AssocList_isEmpty(
    mut v_00_u03b1_602_: *mut LeanObject,
    mut v_00_u03b2_603_: *mut LeanObject,
    mut v_x_604_: *mut LeanObject,
) -> u8 {
    let mut v___x_605_: u8 = 0;
    v___x_605_ = l_Lean_AssocList_isEmpty___redArg(v_x_604_);
    return v___x_605_;
}
pub unsafe fn l_Lean_AssocList_isEmpty___boxed(
    mut v_00_u03b1_606_: *mut LeanObject,
    mut v_00_u03b2_607_: *mut LeanObject,
    mut v_x_608_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_609_: u8 = 0;
    let mut v_r_610_: *mut LeanObject = core::ptr::null_mut();
    v_res_609_ = l_Lean_AssocList_isEmpty(v_00_u03b1_606_, v_00_u03b2_607_, v_x_608_);
    lean_dec(v_x_608_);
    v_r_610_ = lean_box((v_res_609_) as usize);
    return v_r_610_;
}
pub unsafe fn l_Lean_AssocList_foldlM___redArg(
    mut v_inst_611_: *mut LeanObject,
    mut v_f_612_: *mut LeanObject,
    mut v_x_613_: *mut LeanObject,
    mut v_x_614_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_614_) == 0 {
        let mut v_toApplicative_615_: *mut LeanObject = core::ptr::null_mut();
        let mut v_toPure_616_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_617_: *mut LeanObject = core::ptr::null_mut();
        v_toApplicative_615_ = lean_ctor_get(v_inst_611_, 0);
        lean_inc_ref(v_toApplicative_615_);
        lean_dec(v_f_612_);
        lean_dec_ref(v_inst_611_);
        v_toPure_616_ = lean_ctor_get(v_toApplicative_615_, 1);
        lean_inc(v_toPure_616_);
        lean_dec_ref(v_toApplicative_615_);
        v___x_617_ = lean_apply_2(v_toPure_616_, lean_box(0), v_x_613_);
        return v___x_617_;
    } else {
        let mut v_toBind_618_: *mut LeanObject = core::ptr::null_mut();
        let mut v_key_619_: *mut LeanObject = core::ptr::null_mut();
        let mut v_value_620_: *mut LeanObject = core::ptr::null_mut();
        let mut v_tail_621_: *mut LeanObject = core::ptr::null_mut();
        let mut v___f_622_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_623_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_624_: *mut LeanObject = core::ptr::null_mut();
        v_toBind_618_ = lean_ctor_get(v_inst_611_, 1);
        lean_inc(v_toBind_618_);
        v_key_619_ = lean_ctor_get(v_x_614_, 0);
        lean_inc(v_key_619_);
        v_value_620_ = lean_ctor_get(v_x_614_, 1);
        lean_inc(v_value_620_);
        v_tail_621_ = lean_ctor_get(v_x_614_, 2);
        lean_inc(v_tail_621_);
        lean_dec_ref_known(v_x_614_, 3);
        lean_inc(v_f_612_);
        v___f_622_ = lean_alloc_closure(
            l_Lean_AssocList_foldlM___redArg___lam__0 as *mut core::ffi::c_void,
            4,
            3,
        );
        lean_closure_set(v___f_622_, 0, v_inst_611_);
        lean_closure_set(v___f_622_, 1, v_f_612_);
        lean_closure_set(v___f_622_, 2, v_tail_621_);
        v___x_623_ = lean_apply_3(v_f_612_, v_x_613_, v_key_619_, v_value_620_);
        v___x_624_ = lean_apply_4(
            v_toBind_618_,
            lean_box(0),
            lean_box(0),
            v___x_623_,
            v___f_622_,
        );
        return v___x_624_;
    }
}
pub unsafe fn l_Lean_AssocList_foldlM___redArg___lam__0(
    mut v_inst_625_: *mut LeanObject,
    mut v_f_626_: *mut LeanObject,
    mut v_tail_627_: *mut LeanObject,
    mut v_d_628_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_629_: *mut LeanObject = core::ptr::null_mut();
    v___x_629_ = l_Lean_AssocList_foldlM___redArg(v_inst_625_, v_f_626_, v_d_628_, v_tail_627_);
    return v___x_629_;
}
pub unsafe fn l_Lean_AssocList_foldlM(
    mut v_00_u03b1_630_: *mut LeanObject,
    mut v_00_u03b2_631_: *mut LeanObject,
    mut v_00_u03b4_632_: *mut LeanObject,
    mut v_m_633_: *mut LeanObject,
    mut v_inst_634_: *mut LeanObject,
    mut v_f_635_: *mut LeanObject,
    mut v_x_636_: *mut LeanObject,
    mut v_x_637_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_638_: *mut LeanObject = core::ptr::null_mut();
    v___x_638_ = l_Lean_AssocList_foldlM___redArg(v_inst_634_, v_f_635_, v_x_636_, v_x_637_);
    return v___x_638_;
}
pub unsafe fn l_Lean_AssocList_foldl___redArg___lam__0(
    mut v_f_639_: *mut LeanObject,
    mut v_x1_640_: *mut LeanObject,
    mut v_x2_641_: *mut LeanObject,
    mut v_x3_642_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_643_: *mut LeanObject = core::ptr::null_mut();
    v___x_643_ = lean_apply_3(v_f_639_, v_x1_640_, v_x2_641_, v_x3_642_);
    return v___x_643_;
}
pub unsafe fn l_Lean_AssocList_foldl___redArg(
    mut v_f_663_: *mut LeanObject,
    mut v_init_664_: *mut LeanObject,
    mut v_as_665_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_666_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_667_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_668_: *mut LeanObject = core::ptr::null_mut();
    v___f_666_ = lean_alloc_closure(
        l_Lean_AssocList_foldl___redArg___lam__0 as *mut core::ffi::c_void,
        4,
        1,
    );
    lean_closure_set(v___f_666_, 0, v_f_663_);
    v___x_667_ = l_Lean_AssocList_foldl___redArg___closed__9;
    v___x_668_ = l_Lean_AssocList_foldlM___redArg(v___x_667_, v___f_666_, v_init_664_, v_as_665_);
    return v___x_668_;
}
pub unsafe fn l_Lean_AssocList_foldl(
    mut v_00_u03b1_669_: *mut LeanObject,
    mut v_00_u03b2_670_: *mut LeanObject,
    mut v_00_u03b4_671_: *mut LeanObject,
    mut v_f_672_: *mut LeanObject,
    mut v_init_673_: *mut LeanObject,
    mut v_as_674_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_675_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_676_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_677_: *mut LeanObject = core::ptr::null_mut();
    v___f_675_ = lean_alloc_closure(
        l_Lean_AssocList_foldl___redArg___lam__0 as *mut core::ffi::c_void,
        4,
        1,
    );
    lean_closure_set(v___f_675_, 0, v_f_672_);
    v___x_676_ = l_Lean_AssocList_foldl___redArg___closed__9;
    v___x_677_ = l_Lean_AssocList_foldlM___redArg(v___x_676_, v___f_675_, v_init_673_, v_as_674_);
    return v___x_677_;
}
pub unsafe fn l_Lean_AssocList_foldlM___at___00Lean_AssocList_toList_spec__0___redArg(
    mut v_x_678_: *mut LeanObject,
    mut v_x_679_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_key_680_: *mut LeanObject = core::ptr::null_mut();
    let mut v_value_681_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_682_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_683_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_684_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_679_) == 0 {
                    return v_x_678_;
                } else {
                    v_key_680_ = lean_ctor_get(v_x_679_, 0);
                    v_value_681_ = lean_ctor_get(v_x_679_, 1);
                    v_tail_682_ = lean_ctor_get(v_x_679_, 2);
                    lean_inc(v_value_681_);
                    lean_inc(v_key_680_);
                    v___x_683_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v___x_683_, 0, v_key_680_);
                    lean_ctor_set(v___x_683_, 1, v_value_681_);
                    v___x_684_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v___x_684_, 0, v___x_683_);
                    lean_ctor_set(v___x_684_, 1, v_x_678_);
                    v_x_678_ = v___x_684_;
                    v_x_679_ = v_tail_682_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_AssocList_foldlM___at___00Lean_AssocList_toList_spec__0___redArg___boxed(
    mut v_x_686_: *mut LeanObject,
    mut v_x_687_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_688_: *mut LeanObject = core::ptr::null_mut();
    v_res_688_ =
        l_Lean_AssocList_foldlM___at___00Lean_AssocList_toList_spec__0___redArg(v_x_686_, v_x_687_);
    lean_dec(v_x_687_);
    return v_res_688_;
}
pub unsafe fn l_Lean_AssocList_toList___redArg(mut v_as_689_: *mut LeanObject) -> *mut LeanObject {
    let mut v___x_690_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_691_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_692_: *mut LeanObject = core::ptr::null_mut();
    v___x_690_ = lean_box(0);
    v___x_691_ = l_Lean_AssocList_foldlM___at___00Lean_AssocList_toList_spec__0___redArg(
        v___x_690_, v_as_689_,
    );
    v___x_692_ = l_List_reverse___redArg(v___x_691_);
    return v___x_692_;
}
pub unsafe fn l_Lean_AssocList_toList___redArg___boxed(
    mut v_as_693_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_694_: *mut LeanObject = core::ptr::null_mut();
    v_res_694_ = l_Lean_AssocList_toList___redArg(v_as_693_);
    lean_dec(v_as_693_);
    return v_res_694_;
}
pub unsafe fn l_Lean_AssocList_toList(
    mut v_00_u03b1_695_: *mut LeanObject,
    mut v_00_u03b2_696_: *mut LeanObject,
    mut v_as_697_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_698_: *mut LeanObject = core::ptr::null_mut();
    v___x_698_ = l_Lean_AssocList_toList___redArg(v_as_697_);
    return v___x_698_;
}
pub unsafe fn l_Lean_AssocList_toList___boxed(
    mut v_00_u03b1_699_: *mut LeanObject,
    mut v_00_u03b2_700_: *mut LeanObject,
    mut v_as_701_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_702_: *mut LeanObject = core::ptr::null_mut();
    v_res_702_ = l_Lean_AssocList_toList(v_00_u03b1_699_, v_00_u03b2_700_, v_as_701_);
    lean_dec(v_as_701_);
    return v_res_702_;
}
pub unsafe fn l_Lean_AssocList_foldlM___at___00Lean_AssocList_toList_spec__0(
    mut v_00_u03b1_703_: *mut LeanObject,
    mut v_00_u03b2_704_: *mut LeanObject,
    mut v_x_705_: *mut LeanObject,
    mut v_x_706_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_707_: *mut LeanObject = core::ptr::null_mut();
    v___x_707_ =
        l_Lean_AssocList_foldlM___at___00Lean_AssocList_toList_spec__0___redArg(v_x_705_, v_x_706_);
    return v___x_707_;
}
pub unsafe fn l_Lean_AssocList_foldlM___at___00Lean_AssocList_toList_spec__0___boxed(
    mut v_00_u03b1_708_: *mut LeanObject,
    mut v_00_u03b2_709_: *mut LeanObject,
    mut v_x_710_: *mut LeanObject,
    mut v_x_711_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_712_: *mut LeanObject = core::ptr::null_mut();
    v_res_712_ = l_Lean_AssocList_foldlM___at___00Lean_AssocList_toList_spec__0(
        v_00_u03b1_708_,
        v_00_u03b2_709_,
        v_x_710_,
        v_x_711_,
    );
    lean_dec(v_x_711_);
    return v_res_712_;
}
pub unsafe fn l_Lean_AssocList_forM___redArg(
    mut v_inst_713_: *mut LeanObject,
    mut v_f_714_: *mut LeanObject,
    mut v_x_715_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_715_) == 0 {
        let mut v_toApplicative_716_: *mut LeanObject = core::ptr::null_mut();
        let mut v_toPure_717_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_718_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_719_: *mut LeanObject = core::ptr::null_mut();
        v_toApplicative_716_ = lean_ctor_get(v_inst_713_, 0);
        lean_inc_ref(v_toApplicative_716_);
        lean_dec(v_f_714_);
        lean_dec_ref(v_inst_713_);
        v_toPure_717_ = lean_ctor_get(v_toApplicative_716_, 1);
        lean_inc(v_toPure_717_);
        lean_dec_ref(v_toApplicative_716_);
        v___x_718_ = lean_box(0);
        v___x_719_ = lean_apply_2(v_toPure_717_, lean_box(0), v___x_718_);
        return v___x_719_;
    } else {
        let mut v_toBind_720_: *mut LeanObject = core::ptr::null_mut();
        let mut v_key_721_: *mut LeanObject = core::ptr::null_mut();
        let mut v_value_722_: *mut LeanObject = core::ptr::null_mut();
        let mut v_tail_723_: *mut LeanObject = core::ptr::null_mut();
        let mut v___f_724_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_725_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_726_: *mut LeanObject = core::ptr::null_mut();
        v_toBind_720_ = lean_ctor_get(v_inst_713_, 1);
        lean_inc(v_toBind_720_);
        v_key_721_ = lean_ctor_get(v_x_715_, 0);
        lean_inc(v_key_721_);
        v_value_722_ = lean_ctor_get(v_x_715_, 1);
        lean_inc(v_value_722_);
        v_tail_723_ = lean_ctor_get(v_x_715_, 2);
        lean_inc(v_tail_723_);
        lean_dec_ref_known(v_x_715_, 3);
        lean_inc(v_f_714_);
        v___f_724_ = lean_alloc_closure(
            l_Lean_AssocList_forM___redArg___lam__0 as *mut core::ffi::c_void,
            4,
            3,
        );
        lean_closure_set(v___f_724_, 0, v_inst_713_);
        lean_closure_set(v___f_724_, 1, v_f_714_);
        lean_closure_set(v___f_724_, 2, v_tail_723_);
        v___x_725_ = lean_apply_2(v_f_714_, v_key_721_, v_value_722_);
        v___x_726_ = lean_apply_4(
            v_toBind_720_,
            lean_box(0),
            lean_box(0),
            v___x_725_,
            v___f_724_,
        );
        return v___x_726_;
    }
}
pub unsafe fn l_Lean_AssocList_forM___redArg___lam__0(
    mut v_inst_727_: *mut LeanObject,
    mut v_f_728_: *mut LeanObject,
    mut v_tail_729_: *mut LeanObject,
    mut v_____r_730_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_731_: *mut LeanObject = core::ptr::null_mut();
    v___x_731_ = l_Lean_AssocList_forM___redArg(v_inst_727_, v_f_728_, v_tail_729_);
    return v___x_731_;
}
pub unsafe fn l_Lean_AssocList_forM(
    mut v_00_u03b1_732_: *mut LeanObject,
    mut v_00_u03b2_733_: *mut LeanObject,
    mut v_m_734_: *mut LeanObject,
    mut v_inst_735_: *mut LeanObject,
    mut v_f_736_: *mut LeanObject,
    mut v_x_737_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_738_: *mut LeanObject = core::ptr::null_mut();
    v___x_738_ = l_Lean_AssocList_forM___redArg(v_inst_735_, v_f_736_, v_x_737_);
    return v___x_738_;
}
pub unsafe fn l_Lean_AssocList_mapKey___redArg(
    mut v_f_739_: *mut LeanObject,
    mut v_x_740_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_741_: *mut LeanObject = core::ptr::null_mut();
    let mut v_key_742_: *mut LeanObject = core::ptr::null_mut();
    let mut v_value_743_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_744_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_746_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_747_: u8 = 0;
    let mut v___x_748_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_749_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_751_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_752_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_753_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_740_) == 0 {
                    lean_dec(v_f_739_);
                    v___x_741_ = lean_box(0);
                    return v___x_741_;
                } else {
                    v_key_742_ = lean_ctor_get(v_x_740_, 0);
                    v_value_743_ = lean_ctor_get(v_x_740_, 1);
                    v_tail_744_ = lean_ctor_get(v_x_740_, 2);
                    v_isSharedCheck_753_ = (!lean_is_exclusive(v_x_740_)) as u8;
                    if v_isSharedCheck_753_ == 0 {
                        v___x_746_ = v_x_740_;
                        v_isShared_747_ = v_isSharedCheck_753_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_tail_744_);
                        lean_inc(v_value_743_);
                        lean_inc(v_key_742_);
                        lean_dec(v_x_740_);
                        v___x_746_ = lean_box(0);
                        v_isShared_747_ = v_isSharedCheck_753_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                lean_inc(v_f_739_);
                v___x_748_ = lean_apply_1(v_f_739_, v_key_742_);
                v___x_749_ = l_Lean_AssocList_mapKey___redArg(v_f_739_, v_tail_744_);
                if v_isShared_747_ == 0 {
                    lean_ctor_set(v___x_746_, 2, v___x_749_);
                    lean_ctor_set(v___x_746_, 0, v___x_748_);
                    v___x_751_ = v___x_746_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_752_ = lean_alloc_ctor(1, 3, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_752_, 0, v___x_748_);
                    lean_ctor_set(v_reuseFailAlloc_752_, 1, v_value_743_);
                    lean_ctor_set(v_reuseFailAlloc_752_, 2, v___x_749_);
                    v___x_751_ = v_reuseFailAlloc_752_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_751_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_AssocList_mapKey(
    mut v_00_u03b1_754_: *mut LeanObject,
    mut v_00_u03b2_755_: *mut LeanObject,
    mut v_00_u03b4_756_: *mut LeanObject,
    mut v_f_757_: *mut LeanObject,
    mut v_x_758_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_759_: *mut LeanObject = core::ptr::null_mut();
    v___x_759_ = l_Lean_AssocList_mapKey___redArg(v_f_757_, v_x_758_);
    return v___x_759_;
}
pub unsafe fn l_Lean_AssocList_mapVal___redArg(
    mut v_f_760_: *mut LeanObject,
    mut v_x_761_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_762_: *mut LeanObject = core::ptr::null_mut();
    let mut v_key_763_: *mut LeanObject = core::ptr::null_mut();
    let mut v_value_764_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_765_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_767_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_768_: u8 = 0;
    let mut v___x_769_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_770_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_772_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_773_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_774_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_761_) == 0 {
                    lean_dec(v_f_760_);
                    v___x_762_ = lean_box(0);
                    return v___x_762_;
                } else {
                    v_key_763_ = lean_ctor_get(v_x_761_, 0);
                    v_value_764_ = lean_ctor_get(v_x_761_, 1);
                    v_tail_765_ = lean_ctor_get(v_x_761_, 2);
                    v_isSharedCheck_774_ = (!lean_is_exclusive(v_x_761_)) as u8;
                    if v_isSharedCheck_774_ == 0 {
                        v___x_767_ = v_x_761_;
                        v_isShared_768_ = v_isSharedCheck_774_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_tail_765_);
                        lean_inc(v_value_764_);
                        lean_inc(v_key_763_);
                        lean_dec(v_x_761_);
                        v___x_767_ = lean_box(0);
                        v_isShared_768_ = v_isSharedCheck_774_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                lean_inc(v_f_760_);
                v___x_769_ = lean_apply_1(v_f_760_, v_value_764_);
                v___x_770_ = l_Lean_AssocList_mapVal___redArg(v_f_760_, v_tail_765_);
                if v_isShared_768_ == 0 {
                    lean_ctor_set(v___x_767_, 2, v___x_770_);
                    lean_ctor_set(v___x_767_, 1, v___x_769_);
                    v___x_772_ = v___x_767_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_773_ = lean_alloc_ctor(1, 3, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_773_, 0, v_key_763_);
                    lean_ctor_set(v_reuseFailAlloc_773_, 1, v___x_769_);
                    lean_ctor_set(v_reuseFailAlloc_773_, 2, v___x_770_);
                    v___x_772_ = v_reuseFailAlloc_773_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_772_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_AssocList_mapVal(
    mut v_00_u03b1_775_: *mut LeanObject,
    mut v_00_u03b2_776_: *mut LeanObject,
    mut v_00_u03b4_777_: *mut LeanObject,
    mut v_f_778_: *mut LeanObject,
    mut v_x_779_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_780_: *mut LeanObject = core::ptr::null_mut();
    v___x_780_ = l_Lean_AssocList_mapVal___redArg(v_f_778_, v_x_779_);
    return v___x_780_;
}
pub unsafe fn l_Lean_AssocList_findEntry_x3f___redArg(
    mut v_inst_781_: *mut LeanObject,
    mut v_a_782_: *mut LeanObject,
    mut v_x_783_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_784_: *mut LeanObject = core::ptr::null_mut();
    let mut v_key_785_: *mut LeanObject = core::ptr::null_mut();
    let mut v_value_786_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_787_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_788_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_789_: u8 = 0;
    let mut v___x_791_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_792_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_783_) == 0 {
                    lean_dec(v_a_782_);
                    lean_dec_ref(v_inst_781_);
                    v___x_784_ = lean_box(0);
                    return v___x_784_;
                } else {
                    v_key_785_ = lean_ctor_get(v_x_783_, 0);
                    lean_inc_n(v_key_785_, 2);
                    v_value_786_ = lean_ctor_get(v_x_783_, 1);
                    lean_inc(v_value_786_);
                    v_tail_787_ = lean_ctor_get(v_x_783_, 2);
                    lean_inc(v_tail_787_);
                    lean_dec_ref_known(v_x_783_, 3);
                    lean_inc_ref(v_inst_781_);
                    lean_inc(v_a_782_);
                    v___x_788_ = lean_apply_2(v_inst_781_, v_key_785_, v_a_782_);
                    v___x_789_ = (lean_unbox(v___x_788_) as u8);
                    if v___x_789_ == 0 {
                        lean_dec(v_value_786_);
                        lean_dec(v_key_785_);
                        v_x_783_ = v_tail_787_;
                        state = 0;
                        continue;
                    } else {
                        lean_dec(v_tail_787_);
                        lean_dec(v_a_782_);
                        lean_dec_ref(v_inst_781_);
                        v___x_791_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v___x_791_, 0, v_key_785_);
                        lean_ctor_set(v___x_791_, 1, v_value_786_);
                        v___x_792_ = lean_alloc_ctor(1, 1, (0) as u32);
                        lean_ctor_set(v___x_792_, 0, v___x_791_);
                        return v___x_792_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_AssocList_findEntry_x3f(
    mut v_00_u03b1_793_: *mut LeanObject,
    mut v_00_u03b2_794_: *mut LeanObject,
    mut v_inst_795_: *mut LeanObject,
    mut v_a_796_: *mut LeanObject,
    mut v_x_797_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_798_: *mut LeanObject = core::ptr::null_mut();
    v___x_798_ = l_Lean_AssocList_findEntry_x3f___redArg(v_inst_795_, v_a_796_, v_x_797_);
    return v___x_798_;
}
pub unsafe fn l_Lean_AssocList_find_x3f___redArg(
    mut v_inst_799_: *mut LeanObject,
    mut v_a_800_: *mut LeanObject,
    mut v_x_801_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_802_: *mut LeanObject = core::ptr::null_mut();
    let mut v_key_803_: *mut LeanObject = core::ptr::null_mut();
    let mut v_value_804_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_805_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_806_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_807_: u8 = 0;
    let mut v___x_809_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_801_) == 0 {
                    lean_dec(v_a_800_);
                    lean_dec_ref(v_inst_799_);
                    v___x_802_ = lean_box(0);
                    return v___x_802_;
                } else {
                    v_key_803_ = lean_ctor_get(v_x_801_, 0);
                    lean_inc(v_key_803_);
                    v_value_804_ = lean_ctor_get(v_x_801_, 1);
                    lean_inc(v_value_804_);
                    v_tail_805_ = lean_ctor_get(v_x_801_, 2);
                    lean_inc(v_tail_805_);
                    lean_dec_ref_known(v_x_801_, 3);
                    lean_inc_ref(v_inst_799_);
                    lean_inc(v_a_800_);
                    v___x_806_ = lean_apply_2(v_inst_799_, v_key_803_, v_a_800_);
                    v___x_807_ = (lean_unbox(v___x_806_) as u8);
                    if v___x_807_ == 0 {
                        lean_dec(v_value_804_);
                        v_x_801_ = v_tail_805_;
                        state = 0;
                        continue;
                    } else {
                        lean_dec(v_tail_805_);
                        lean_dec(v_a_800_);
                        lean_dec_ref(v_inst_799_);
                        v___x_809_ = lean_alloc_ctor(1, 1, (0) as u32);
                        lean_ctor_set(v___x_809_, 0, v_value_804_);
                        return v___x_809_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_AssocList_find_x3f(
    mut v_00_u03b1_810_: *mut LeanObject,
    mut v_00_u03b2_811_: *mut LeanObject,
    mut v_inst_812_: *mut LeanObject,
    mut v_a_813_: *mut LeanObject,
    mut v_x_814_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_815_: *mut LeanObject = core::ptr::null_mut();
    v___x_815_ = l_Lean_AssocList_find_x3f___redArg(v_inst_812_, v_a_813_, v_x_814_);
    return v___x_815_;
}
pub unsafe fn l_Lean_AssocList_contains___redArg(
    mut v_inst_816_: *mut LeanObject,
    mut v_a_817_: *mut LeanObject,
    mut v_x_818_: *mut LeanObject,
) -> u8 {
    let mut v___x_819_: u8 = 0;
    let mut v_key_820_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_821_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_822_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_823_: u8 = 0;
    let mut v___x_825_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_818_) == 0 {
                    lean_dec(v_a_817_);
                    lean_dec_ref(v_inst_816_);
                    v___x_819_ = 0;
                    return v___x_819_;
                } else {
                    v_key_820_ = lean_ctor_get(v_x_818_, 0);
                    lean_inc(v_key_820_);
                    v_tail_821_ = lean_ctor_get(v_x_818_, 2);
                    lean_inc(v_tail_821_);
                    lean_dec_ref_known(v_x_818_, 3);
                    lean_inc_ref(v_inst_816_);
                    lean_inc(v_a_817_);
                    v___x_822_ = lean_apply_2(v_inst_816_, v_key_820_, v_a_817_);
                    v___x_823_ = (lean_unbox(v___x_822_) as u8);
                    if v___x_823_ == 0 {
                        v_x_818_ = v_tail_821_;
                        state = 0;
                        continue;
                    } else {
                        lean_dec(v_tail_821_);
                        lean_dec(v_a_817_);
                        lean_dec_ref(v_inst_816_);
                        v___x_825_ = (lean_unbox(v___x_822_) as u8);
                        return v___x_825_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_AssocList_contains___redArg___boxed(
    mut v_inst_826_: *mut LeanObject,
    mut v_a_827_: *mut LeanObject,
    mut v_x_828_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_829_: u8 = 0;
    let mut v_r_830_: *mut LeanObject = core::ptr::null_mut();
    v_res_829_ = l_Lean_AssocList_contains___redArg(v_inst_826_, v_a_827_, v_x_828_);
    v_r_830_ = lean_box((v_res_829_) as usize);
    return v_r_830_;
}
pub unsafe fn l_Lean_AssocList_contains(
    mut v_00_u03b1_831_: *mut LeanObject,
    mut v_00_u03b2_832_: *mut LeanObject,
    mut v_inst_833_: *mut LeanObject,
    mut v_a_834_: *mut LeanObject,
    mut v_x_835_: *mut LeanObject,
) -> u8 {
    let mut v___x_836_: u8 = 0;
    v___x_836_ = l_Lean_AssocList_contains___redArg(v_inst_833_, v_a_834_, v_x_835_);
    return v___x_836_;
}
pub unsafe fn l_Lean_AssocList_contains___boxed(
    mut v_00_u03b1_837_: *mut LeanObject,
    mut v_00_u03b2_838_: *mut LeanObject,
    mut v_inst_839_: *mut LeanObject,
    mut v_a_840_: *mut LeanObject,
    mut v_x_841_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_842_: u8 = 0;
    let mut v_r_843_: *mut LeanObject = core::ptr::null_mut();
    v_res_842_ = l_Lean_AssocList_contains(
        v_00_u03b1_837_,
        v_00_u03b2_838_,
        v_inst_839_,
        v_a_840_,
        v_x_841_,
    );
    v_r_843_ = lean_box((v_res_842_) as usize);
    return v_r_843_;
}
pub unsafe fn l_Lean_AssocList_replace___redArg(
    mut v_inst_844_: *mut LeanObject,
    mut v_a_845_: *mut LeanObject,
    mut v_b_846_: *mut LeanObject,
    mut v_x_847_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_key_848_: *mut LeanObject = core::ptr::null_mut();
    let mut v_value_849_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_850_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_852_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_853_: u8 = 0;
    let mut v___x_854_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_855_: u8 = 0;
    let mut v___x_856_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_858_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_859_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_861_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_862_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_863_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_847_) == 0 {
                    lean_dec(v_b_846_);
                    lean_dec(v_a_845_);
                    lean_dec_ref(v_inst_844_);
                    return v_x_847_;
                } else {
                    v_key_848_ = lean_ctor_get(v_x_847_, 0);
                    v_value_849_ = lean_ctor_get(v_x_847_, 1);
                    v_tail_850_ = lean_ctor_get(v_x_847_, 2);
                    v_isSharedCheck_863_ = (!lean_is_exclusive(v_x_847_)) as u8;
                    if v_isSharedCheck_863_ == 0 {
                        v___x_852_ = v_x_847_;
                        v_isShared_853_ = v_isSharedCheck_863_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_tail_850_);
                        lean_inc(v_value_849_);
                        lean_inc(v_key_848_);
                        lean_dec(v_x_847_);
                        v___x_852_ = lean_box(0);
                        v_isShared_853_ = v_isSharedCheck_863_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                lean_inc_ref(v_inst_844_);
                lean_inc(v_a_845_);
                lean_inc(v_key_848_);
                v___x_854_ = lean_apply_2(v_inst_844_, v_key_848_, v_a_845_);
                v___x_855_ = (lean_unbox(v___x_854_) as u8);
                if v___x_855_ == 0 {
                    v___x_856_ = l_Lean_AssocList_replace___redArg(
                        v_inst_844_,
                        v_a_845_,
                        v_b_846_,
                        v_tail_850_,
                    );
                    if v_isShared_853_ == 0 {
                        lean_ctor_set(v___x_852_, 2, v___x_856_);
                        v___x_858_ = v___x_852_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_859_ = lean_alloc_ctor(1, 3, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_859_, 0, v_key_848_);
                        lean_ctor_set(v_reuseFailAlloc_859_, 1, v_value_849_);
                        lean_ctor_set(v_reuseFailAlloc_859_, 2, v___x_856_);
                        v___x_858_ = v_reuseFailAlloc_859_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_dec(v_value_849_);
                    lean_dec(v_key_848_);
                    lean_dec_ref(v_inst_844_);
                    if v_isShared_853_ == 0 {
                        lean_ctor_set(v___x_852_, 1, v_b_846_);
                        lean_ctor_set(v___x_852_, 0, v_a_845_);
                        v___x_861_ = v___x_852_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_862_ = lean_alloc_ctor(1, 3, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_862_, 0, v_a_845_);
                        lean_ctor_set(v_reuseFailAlloc_862_, 1, v_b_846_);
                        lean_ctor_set(v_reuseFailAlloc_862_, 2, v_tail_850_);
                        v___x_861_ = v_reuseFailAlloc_862_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_858_;
            }
            3 => {
                return v___x_861_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_AssocList_replace(
    mut v_00_u03b1_864_: *mut LeanObject,
    mut v_00_u03b2_865_: *mut LeanObject,
    mut v_inst_866_: *mut LeanObject,
    mut v_a_867_: *mut LeanObject,
    mut v_b_868_: *mut LeanObject,
    mut v_x_869_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_870_: *mut LeanObject = core::ptr::null_mut();
    v___x_870_ = l_Lean_AssocList_replace___redArg(v_inst_866_, v_a_867_, v_b_868_, v_x_869_);
    return v___x_870_;
}
pub unsafe fn l_Lean_AssocList_insert___redArg(
    mut v_inst_871_: *mut LeanObject,
    mut v_m_872_: *mut LeanObject,
    mut v_k_873_: *mut LeanObject,
    mut v_v_874_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_875_: u8 = 0;
    lean_inc(v_m_872_);
    lean_inc(v_k_873_);
    lean_inc_ref(v_inst_871_);
    v___x_875_ = l_Lean_AssocList_contains___redArg(v_inst_871_, v_k_873_, v_m_872_);
    if v___x_875_ == 0 {
        let mut v___x_876_: *mut LeanObject = core::ptr::null_mut();
        lean_dec_ref(v_inst_871_);
        v___x_876_ = lean_alloc_ctor(1, 3, (0) as u32);
        lean_ctor_set(v___x_876_, 0, v_k_873_);
        lean_ctor_set(v___x_876_, 1, v_v_874_);
        lean_ctor_set(v___x_876_, 2, v_m_872_);
        return v___x_876_;
    } else {
        let mut v___x_877_: *mut LeanObject = core::ptr::null_mut();
        v___x_877_ = l_Lean_AssocList_replace___redArg(v_inst_871_, v_k_873_, v_v_874_, v_m_872_);
        return v___x_877_;
    }
}
pub unsafe fn l_Lean_AssocList_insert(
    mut v_00_u03b1_878_: *mut LeanObject,
    mut v_00_u03b2_879_: *mut LeanObject,
    mut v_inst_880_: *mut LeanObject,
    mut v_m_881_: *mut LeanObject,
    mut v_k_882_: *mut LeanObject,
    mut v_v_883_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_884_: *mut LeanObject = core::ptr::null_mut();
    v___x_884_ = l_Lean_AssocList_insert___redArg(v_inst_880_, v_m_881_, v_k_882_, v_v_883_);
    return v___x_884_;
}
pub unsafe fn l_Lean_AssocList_erase___redArg(
    mut v_inst_885_: *mut LeanObject,
    mut v_a_886_: *mut LeanObject,
    mut v_x_887_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_key_888_: *mut LeanObject = core::ptr::null_mut();
    let mut v_value_889_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_890_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_892_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_893_: u8 = 0;
    let mut v___x_894_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_895_: u8 = 0;
    let mut v___x_896_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_898_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_899_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_900_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_887_) == 0 {
                    lean_dec(v_a_886_);
                    lean_dec_ref(v_inst_885_);
                    return v_x_887_;
                } else {
                    v_key_888_ = lean_ctor_get(v_x_887_, 0);
                    v_value_889_ = lean_ctor_get(v_x_887_, 1);
                    v_tail_890_ = lean_ctor_get(v_x_887_, 2);
                    v_isSharedCheck_900_ = (!lean_is_exclusive(v_x_887_)) as u8;
                    if v_isSharedCheck_900_ == 0 {
                        v___x_892_ = v_x_887_;
                        v_isShared_893_ = v_isSharedCheck_900_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_tail_890_);
                        lean_inc(v_value_889_);
                        lean_inc(v_key_888_);
                        lean_dec(v_x_887_);
                        v___x_892_ = lean_box(0);
                        v_isShared_893_ = v_isSharedCheck_900_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                lean_inc_ref(v_inst_885_);
                lean_inc(v_a_886_);
                lean_inc(v_key_888_);
                v___x_894_ = lean_apply_2(v_inst_885_, v_key_888_, v_a_886_);
                v___x_895_ = (lean_unbox(v___x_894_) as u8);
                if v___x_895_ == 0 {
                    v___x_896_ =
                        l_Lean_AssocList_erase___redArg(v_inst_885_, v_a_886_, v_tail_890_);
                    if v_isShared_893_ == 0 {
                        lean_ctor_set(v___x_892_, 2, v___x_896_);
                        v___x_898_ = v___x_892_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_899_ = lean_alloc_ctor(1, 3, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_899_, 0, v_key_888_);
                        lean_ctor_set(v_reuseFailAlloc_899_, 1, v_value_889_);
                        lean_ctor_set(v_reuseFailAlloc_899_, 2, v___x_896_);
                        v___x_898_ = v_reuseFailAlloc_899_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_892_);
                    lean_dec(v_value_889_);
                    lean_dec(v_key_888_);
                    lean_dec(v_a_886_);
                    lean_dec_ref(v_inst_885_);
                    return v_tail_890_;
                }
            }
            2 => {
                return v___x_898_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_AssocList_erase(
    mut v_00_u03b1_901_: *mut LeanObject,
    mut v_00_u03b2_902_: *mut LeanObject,
    mut v_inst_903_: *mut LeanObject,
    mut v_a_904_: *mut LeanObject,
    mut v_x_905_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_906_: *mut LeanObject = core::ptr::null_mut();
    v___x_906_ = l_Lean_AssocList_erase___redArg(v_inst_903_, v_a_904_, v_x_905_);
    return v___x_906_;
}
pub unsafe fn l_Lean_AssocList_any___redArg(
    mut v_p_907_: *mut LeanObject,
    mut v_x_908_: *mut LeanObject,
) -> u8 {
    let mut v___x_909_: u8 = 0;
    let mut v_key_910_: *mut LeanObject = core::ptr::null_mut();
    let mut v_value_911_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_912_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_913_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_914_: u8 = 0;
    let mut v___x_916_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_908_) == 0 {
                    lean_dec_ref(v_p_907_);
                    v___x_909_ = 0;
                    return v___x_909_;
                } else {
                    v_key_910_ = lean_ctor_get(v_x_908_, 0);
                    lean_inc(v_key_910_);
                    v_value_911_ = lean_ctor_get(v_x_908_, 1);
                    lean_inc(v_value_911_);
                    v_tail_912_ = lean_ctor_get(v_x_908_, 2);
                    lean_inc(v_tail_912_);
                    lean_dec_ref_known(v_x_908_, 3);
                    lean_inc_ref(v_p_907_);
                    v___x_913_ = lean_apply_2(v_p_907_, v_key_910_, v_value_911_);
                    v___x_914_ = (lean_unbox(v___x_913_) as u8);
                    if v___x_914_ == 0 {
                        v_x_908_ = v_tail_912_;
                        state = 0;
                        continue;
                    } else {
                        lean_dec(v_tail_912_);
                        lean_dec_ref(v_p_907_);
                        v___x_916_ = (lean_unbox(v___x_913_) as u8);
                        return v___x_916_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_AssocList_any___redArg___boxed(
    mut v_p_917_: *mut LeanObject,
    mut v_x_918_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_919_: u8 = 0;
    let mut v_r_920_: *mut LeanObject = core::ptr::null_mut();
    v_res_919_ = l_Lean_AssocList_any___redArg(v_p_917_, v_x_918_);
    v_r_920_ = lean_box((v_res_919_) as usize);
    return v_r_920_;
}
pub unsafe fn l_Lean_AssocList_any(
    mut v_00_u03b1_921_: *mut LeanObject,
    mut v_00_u03b2_922_: *mut LeanObject,
    mut v_p_923_: *mut LeanObject,
    mut v_x_924_: *mut LeanObject,
) -> u8 {
    let mut v___x_925_: u8 = 0;
    v___x_925_ = l_Lean_AssocList_any___redArg(v_p_923_, v_x_924_);
    return v___x_925_;
}
pub unsafe fn l_Lean_AssocList_any___boxed(
    mut v_00_u03b1_926_: *mut LeanObject,
    mut v_00_u03b2_927_: *mut LeanObject,
    mut v_p_928_: *mut LeanObject,
    mut v_x_929_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_930_: u8 = 0;
    let mut v_r_931_: *mut LeanObject = core::ptr::null_mut();
    v_res_930_ = l_Lean_AssocList_any(v_00_u03b1_926_, v_00_u03b2_927_, v_p_928_, v_x_929_);
    v_r_931_ = lean_box((v_res_930_) as usize);
    return v_r_931_;
}
pub unsafe fn l_Lean_AssocList_all___redArg(
    mut v_p_932_: *mut LeanObject,
    mut v_x_933_: *mut LeanObject,
) -> u8 {
    let mut v___x_934_: u8 = 0;
    let mut v_key_935_: *mut LeanObject = core::ptr::null_mut();
    let mut v_value_936_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_937_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_938_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_939_: u8 = 0;
    let mut v___x_940_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_933_) == 0 {
                    lean_dec_ref(v_p_932_);
                    v___x_934_ = 1;
                    return v___x_934_;
                } else {
                    v_key_935_ = lean_ctor_get(v_x_933_, 0);
                    lean_inc(v_key_935_);
                    v_value_936_ = lean_ctor_get(v_x_933_, 1);
                    lean_inc(v_value_936_);
                    v_tail_937_ = lean_ctor_get(v_x_933_, 2);
                    lean_inc(v_tail_937_);
                    lean_dec_ref_known(v_x_933_, 3);
                    lean_inc_ref(v_p_932_);
                    v___x_938_ = lean_apply_2(v_p_932_, v_key_935_, v_value_936_);
                    v___x_939_ = (lean_unbox(v___x_938_) as u8);
                    if v___x_939_ == 0 {
                        lean_dec(v_tail_937_);
                        lean_dec_ref(v_p_932_);
                        v___x_940_ = (lean_unbox(v___x_938_) as u8);
                        return v___x_940_;
                    } else {
                        v_x_933_ = v_tail_937_;
                        state = 0;
                        continue;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_AssocList_all___redArg___boxed(
    mut v_p_942_: *mut LeanObject,
    mut v_x_943_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_944_: u8 = 0;
    let mut v_r_945_: *mut LeanObject = core::ptr::null_mut();
    v_res_944_ = l_Lean_AssocList_all___redArg(v_p_942_, v_x_943_);
    v_r_945_ = lean_box((v_res_944_) as usize);
    return v_r_945_;
}
pub unsafe fn l_Lean_AssocList_all(
    mut v_00_u03b1_946_: *mut LeanObject,
    mut v_00_u03b2_947_: *mut LeanObject,
    mut v_p_948_: *mut LeanObject,
    mut v_x_949_: *mut LeanObject,
) -> u8 {
    let mut v___x_950_: u8 = 0;
    v___x_950_ = l_Lean_AssocList_all___redArg(v_p_948_, v_x_949_);
    return v___x_950_;
}
pub unsafe fn l_Lean_AssocList_all___boxed(
    mut v_00_u03b1_951_: *mut LeanObject,
    mut v_00_u03b2_952_: *mut LeanObject,
    mut v_p_953_: *mut LeanObject,
    mut v_x_954_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_955_: u8 = 0;
    let mut v_r_956_: *mut LeanObject = core::ptr::null_mut();
    v_res_955_ = l_Lean_AssocList_all(v_00_u03b1_951_, v_00_u03b2_952_, v_p_953_, v_x_954_);
    v_r_956_ = lean_box((v_res_955_) as usize);
    return v_r_956_;
}
pub unsafe fn l___private_Lean_Data_AssocList_0__Lean_AssocList_forIn_loop___redArg(
    mut v_inst_957_: *mut LeanObject,
    mut v_f_958_: *mut LeanObject,
    mut v_x_959_: *mut LeanObject,
    mut v_x_960_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_960_) == 0 {
        let mut v_toApplicative_961_: *mut LeanObject = core::ptr::null_mut();
        let mut v_toPure_962_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_963_: *mut LeanObject = core::ptr::null_mut();
        v_toApplicative_961_ = lean_ctor_get(v_inst_957_, 0);
        lean_inc_ref(v_toApplicative_961_);
        lean_dec(v_f_958_);
        lean_dec_ref(v_inst_957_);
        v_toPure_962_ = lean_ctor_get(v_toApplicative_961_, 1);
        lean_inc(v_toPure_962_);
        lean_dec_ref(v_toApplicative_961_);
        v___x_963_ = lean_apply_2(v_toPure_962_, lean_box(0), v_x_959_);
        return v___x_963_;
    } else {
        let mut v_toApplicative_964_: *mut LeanObject = core::ptr::null_mut();
        let mut v_toBind_965_: *mut LeanObject = core::ptr::null_mut();
        let mut v_toPure_966_: *mut LeanObject = core::ptr::null_mut();
        let mut v_key_967_: *mut LeanObject = core::ptr::null_mut();
        let mut v_value_968_: *mut LeanObject = core::ptr::null_mut();
        let mut v_tail_969_: *mut LeanObject = core::ptr::null_mut();
        let mut v___f_970_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_971_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_972_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_973_: *mut LeanObject = core::ptr::null_mut();
        v_toApplicative_964_ = lean_ctor_get(v_inst_957_, 0);
        v_toBind_965_ = lean_ctor_get(v_inst_957_, 1);
        lean_inc(v_toBind_965_);
        v_toPure_966_ = lean_ctor_get(v_toApplicative_964_, 1);
        lean_inc(v_toPure_966_);
        v_key_967_ = lean_ctor_get(v_x_960_, 0);
        lean_inc(v_key_967_);
        v_value_968_ = lean_ctor_get(v_x_960_, 1);
        lean_inc(v_value_968_);
        v_tail_969_ = lean_ctor_get(v_x_960_, 2);
        lean_inc(v_tail_969_);
        lean_dec_ref_known(v_x_960_, 3);
        lean_inc(v_f_958_);
        v___f_970_ = lean_alloc_closure(
            l___private_Lean_Data_AssocList_0__Lean_AssocList_forIn_loop___redArg___lam__0
                as *mut core::ffi::c_void,
            5,
            4,
        );
        lean_closure_set(v___f_970_, 0, v_toPure_966_);
        lean_closure_set(v___f_970_, 1, v_inst_957_);
        lean_closure_set(v___f_970_, 2, v_f_958_);
        lean_closure_set(v___f_970_, 3, v_tail_969_);
        v___x_971_ = lean_alloc_ctor(0, 2, (0) as u32);
        lean_ctor_set(v___x_971_, 0, v_key_967_);
        lean_ctor_set(v___x_971_, 1, v_value_968_);
        v___x_972_ = lean_apply_2(v_f_958_, v___x_971_, v_x_959_);
        v___x_973_ = lean_apply_4(
            v_toBind_965_,
            lean_box(0),
            lean_box(0),
            v___x_972_,
            v___f_970_,
        );
        return v___x_973_;
    }
}
pub unsafe fn l___private_Lean_Data_AssocList_0__Lean_AssocList_forIn_loop___redArg___lam__0(
    mut v_toPure_974_: *mut LeanObject,
    mut v_inst_975_: *mut LeanObject,
    mut v_f_976_: *mut LeanObject,
    mut v_tail_977_: *mut LeanObject,
    mut v_____do__lift_978_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_____do__lift_978_) == 0 {
        let mut v_a_979_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_980_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_tail_977_);
        lean_dec(v_f_976_);
        lean_dec_ref(v_inst_975_);
        v_a_979_ = lean_ctor_get(v_____do__lift_978_, 0);
        lean_inc(v_a_979_);
        lean_dec_ref_known(v_____do__lift_978_, 1);
        v___x_980_ = lean_apply_2(v_toPure_974_, lean_box(0), v_a_979_);
        return v___x_980_;
    } else {
        let mut v_a_981_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_982_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_toPure_974_);
        v_a_981_ = lean_ctor_get(v_____do__lift_978_, 0);
        lean_inc(v_a_981_);
        lean_dec_ref_known(v_____do__lift_978_, 1);
        v___x_982_ = l___private_Lean_Data_AssocList_0__Lean_AssocList_forIn_loop___redArg(
            v_inst_975_,
            v_f_976_,
            v_a_981_,
            v_tail_977_,
        );
        return v___x_982_;
    }
}
pub unsafe fn l___private_Lean_Data_AssocList_0__Lean_AssocList_forIn_loop(
    mut v_00_u03b1_983_: *mut LeanObject,
    mut v_00_u03b2_984_: *mut LeanObject,
    mut v_00_u03b4_985_: *mut LeanObject,
    mut v_m_986_: *mut LeanObject,
    mut v_inst_987_: *mut LeanObject,
    mut v_f_988_: *mut LeanObject,
    mut v_x_989_: *mut LeanObject,
    mut v_x_990_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_991_: *mut LeanObject = core::ptr::null_mut();
    v___x_991_ = l___private_Lean_Data_AssocList_0__Lean_AssocList_forIn_loop___redArg(
        v_inst_987_,
        v_f_988_,
        v_x_989_,
        v_x_990_,
    );
    return v___x_991_;
}
pub unsafe fn l_Lean_AssocList_forIn___redArg(
    mut v_inst_992_: *mut LeanObject,
    mut v_as_993_: *mut LeanObject,
    mut v_init_994_: *mut LeanObject,
    mut v_f_995_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_996_: *mut LeanObject = core::ptr::null_mut();
    v___x_996_ = l___private_Lean_Data_AssocList_0__Lean_AssocList_forIn_loop___redArg(
        v_inst_992_,
        v_f_995_,
        v_init_994_,
        v_as_993_,
    );
    return v___x_996_;
}
pub unsafe fn l_Lean_AssocList_forIn(
    mut v_00_u03b1_997_: *mut LeanObject,
    mut v_00_u03b2_998_: *mut LeanObject,
    mut v_00_u03b4_999_: *mut LeanObject,
    mut v_m_1000_: *mut LeanObject,
    mut v_inst_1001_: *mut LeanObject,
    mut v_as_1002_: *mut LeanObject,
    mut v_init_1003_: *mut LeanObject,
    mut v_f_1004_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1005_: *mut LeanObject = core::ptr::null_mut();
    v___x_1005_ = l___private_Lean_Data_AssocList_0__Lean_AssocList_forIn_loop___redArg(
        v_inst_1001_,
        v_f_1004_,
        v_init_1003_,
        v_as_1002_,
    );
    return v___x_1005_;
}
pub unsafe fn l_Lean_AssocList_instForInProdOfMonad___redArg___lam__0(
    mut v_inst_1006_: *mut LeanObject,
    mut v_00_u03b2_1007_: *mut LeanObject,
    mut v___y_1008_: *mut LeanObject,
    mut v___y_1009_: *mut LeanObject,
    mut v___y_1010_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1011_: *mut LeanObject = core::ptr::null_mut();
    v___x_1011_ = l___private_Lean_Data_AssocList_0__Lean_AssocList_forIn_loop___redArg(
        v_inst_1006_,
        v___y_1010_,
        v___y_1009_,
        v___y_1008_,
    );
    return v___x_1011_;
}
pub unsafe fn l_Lean_AssocList_instForInProdOfMonad___redArg(
    mut v_inst_1012_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_1013_: *mut LeanObject = core::ptr::null_mut();
    v___f_1013_ = lean_alloc_closure(
        l_Lean_AssocList_instForInProdOfMonad___redArg___lam__0 as *mut core::ffi::c_void,
        5,
        1,
    );
    lean_closure_set(v___f_1013_, 0, v_inst_1012_);
    return v___f_1013_;
}
pub unsafe fn l_Lean_AssocList_instForInProdOfMonad(
    mut v_00_u03b1_1014_: *mut LeanObject,
    mut v_00_u03b2_1015_: *mut LeanObject,
    mut v_m_1016_: *mut LeanObject,
    mut v_inst_1017_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_1018_: *mut LeanObject = core::ptr::null_mut();
    v___f_1018_ = lean_alloc_closure(
        l_Lean_AssocList_instForInProdOfMonad___redArg___lam__0 as *mut core::ffi::c_void,
        5,
        1,
    );
    lean_closure_set(v___f_1018_, 0, v_inst_1017_);
    return v___f_1018_;
}
pub unsafe fn l_List_toAssocList_x27___redArg(mut v_x_1019_: *mut LeanObject) -> *mut LeanObject {
    if lean_obj_tag(v_x_1019_) == 0 {
        let mut v___x_1020_: *mut LeanObject = core::ptr::null_mut();
        v___x_1020_ = lean_box(0);
        return v___x_1020_;
    } else {
        let mut v_head_1021_: *mut LeanObject = core::ptr::null_mut();
        let mut v_tail_1022_: *mut LeanObject = core::ptr::null_mut();
        let mut v_fst_1023_: *mut LeanObject = core::ptr::null_mut();
        let mut v_snd_1024_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1025_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1026_: *mut LeanObject = core::ptr::null_mut();
        v_head_1021_ = lean_ctor_get(v_x_1019_, 0);
        v_tail_1022_ = lean_ctor_get(v_x_1019_, 1);
        v_fst_1023_ = lean_ctor_get(v_head_1021_, 0);
        v_snd_1024_ = lean_ctor_get(v_head_1021_, 1);
        v___x_1025_ = l_List_toAssocList_x27___redArg(v_tail_1022_);
        lean_inc(v_snd_1024_);
        lean_inc(v_fst_1023_);
        v___x_1026_ = lean_alloc_ctor(1, 3, (0) as u32);
        lean_ctor_set(v___x_1026_, 0, v_fst_1023_);
        lean_ctor_set(v___x_1026_, 1, v_snd_1024_);
        lean_ctor_set(v___x_1026_, 2, v___x_1025_);
        return v___x_1026_;
    }
}
pub unsafe fn l_List_toAssocList_x27___redArg___boxed(
    mut v_x_1027_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1028_: *mut LeanObject = core::ptr::null_mut();
    v_res_1028_ = l_List_toAssocList_x27___redArg(v_x_1027_);
    lean_dec(v_x_1027_);
    return v_res_1028_;
}
pub unsafe fn l_List_toAssocList_x27(
    mut v_00_u03b1_1029_: *mut LeanObject,
    mut v_00_u03b2_1030_: *mut LeanObject,
    mut v_x_1031_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1032_: *mut LeanObject = core::ptr::null_mut();
    v___x_1032_ = l_List_toAssocList_x27___redArg(v_x_1031_);
    return v___x_1032_;
}
pub unsafe fn l_List_toAssocList_x27___boxed(
    mut v_00_u03b1_1033_: *mut LeanObject,
    mut v_00_u03b2_1034_: *mut LeanObject,
    mut v_x_1035_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1036_: *mut LeanObject = core::ptr::null_mut();
    v_res_1036_ = l_List_toAssocList_x27(v_00_u03b1_1033_, v_00_u03b2_1034_, v_x_1035_);
    lean_dec(v_x_1035_);
    return v_res_1036_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Data_AssocList(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Init_Data_List_Impl(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Data_AssocList(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_meta_initialized = true;
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lean_Data_AssocList(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Init_Data_List_Impl(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Data_AssocList(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Lean_Data_AssocList(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Lean_Data_AssocList(builtin);
}
