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
pub static l_Lean_AssocList_foldl___redArg___closed__0_value: crate::leanh::LeanClosureObject<0> =
    crate::leanh::LeanClosureObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0)
                as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Id_instMonad___lam__0 as *const core::ffi::c_void,
        m_arity: 4,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_AssocList_foldl___redArg___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_AssocList_foldl___redArg___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_AssocList_foldl___redArg___closed__1_value: crate::leanh::LeanClosureObject<0> =
    crate::leanh::LeanClosureObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0)
                as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Id_instMonad___lam__1___boxed as *const core::ffi::c_void,
        m_arity: 4,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_AssocList_foldl___redArg___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_AssocList_foldl___redArg___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_AssocList_foldl___redArg___closed__2_value: crate::leanh::LeanClosureObject<0> =
    crate::leanh::LeanClosureObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0)
                as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Id_instMonad___lam__2___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_AssocList_foldl___redArg___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_AssocList_foldl___redArg___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_AssocList_foldl___redArg___closed__3_value: crate::leanh::LeanClosureObject<0> =
    crate::leanh::LeanClosureObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0)
                as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Id_instMonad___lam__3 as *const core::ffi::c_void,
        m_arity: 4,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_AssocList_foldl___redArg___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_AssocList_foldl___redArg___closed__3_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_AssocList_foldl___redArg___closed__4_value: crate::leanh::LeanClosureObject<0> =
    crate::leanh::LeanClosureObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0)
                as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Id_instMonad___lam__4___boxed as *const core::ffi::c_void,
        m_arity: 4,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_AssocList_foldl___redArg___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_AssocList_foldl___redArg___closed__4_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_AssocList_foldl___redArg___closed__5_value: crate::leanh::LeanClosureObject<0> =
    crate::leanh::LeanClosureObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0)
                as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Id_instMonad___lam__5___boxed as *const core::ffi::c_void,
        m_arity: 4,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_AssocList_foldl___redArg___closed__5: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_AssocList_foldl___redArg___closed__5_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_AssocList_foldl___redArg___closed__6_value: crate::leanh::LeanClosureObject<0> =
    crate::leanh::LeanClosureObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0)
                as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Id_instMonad___lam__6 as *const core::ffi::c_void,
        m_arity: 4,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_AssocList_foldl___redArg___closed__6: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_AssocList_foldl___redArg___closed__6_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_AssocList_foldl___redArg___closed__7_value: crate::leanh::LeanCtorObject<2> =
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
            core::ptr::addr_of!(l_Lean_AssocList_foldl___redArg___closed__0_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_AssocList_foldl___redArg___closed__1_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_AssocList_foldl___redArg___closed__7: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_AssocList_foldl___redArg___closed__7_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_AssocList_foldl___redArg___closed__8_value: crate::leanh::LeanCtorObject<5> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 5
                + 0) as u16,
            other: 5,
            tag: 0,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_AssocList_foldl___redArg___closed__7_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_AssocList_foldl___redArg___closed__2_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_AssocList_foldl___redArg___closed__3_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_AssocList_foldl___redArg___closed__4_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_AssocList_foldl___redArg___closed__5_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_AssocList_foldl___redArg___closed__8: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_AssocList_foldl___redArg___closed__8_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_AssocList_foldl___redArg___closed__9_value: crate::leanh::LeanCtorObject<2> =
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
            core::ptr::addr_of!(l_Lean_AssocList_foldl___redArg___closed__8_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_AssocList_foldl___redArg___closed__6_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_AssocList_foldl___redArg___closed__9: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_AssocList_foldl___redArg___closed__9_value)
        as *mut crate::leanh::LeanObject;
pub unsafe fn l_Lean_AssocList_ctorIdx___redArg(
    mut v_x_519_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_519_) == 0 {
        let mut v___x_520_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_520_ = crate::leanh::lean_unsigned_to_nat(0);
        return v___x_520_;
    } else {
        let mut v___x_521_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_521_ = crate::leanh::lean_unsigned_to_nat(1);
        return v___x_521_;
    }
}
pub unsafe fn l_Lean_AssocList_ctorIdx___redArg___boxed(
    mut v_x_522_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_523_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_523_ = l_Lean_AssocList_ctorIdx___redArg(v_x_522_);
    crate::leanh::lean_dec(v_x_522_);
    return v_res_523_;
}
pub unsafe fn l_Lean_AssocList_ctorIdx(
    mut v_00_u03b1_524_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_525_: *mut crate::leanh::LeanObject,
    mut v_x_526_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_527_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_527_ = l_Lean_AssocList_ctorIdx___redArg(v_x_526_);
    return v___x_527_;
}
pub unsafe fn l_Lean_AssocList_ctorIdx___boxed(
    mut v_00_u03b1_528_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_529_: *mut crate::leanh::LeanObject,
    mut v_x_530_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_531_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_531_ = l_Lean_AssocList_ctorIdx(v_00_u03b1_528_, v_00_u03b2_529_, v_x_530_);
    crate::leanh::lean_dec(v_x_530_);
    return v_res_531_;
}
pub unsafe fn l_Lean_AssocList_ctorElim___redArg(
    mut v_t_532_: *mut crate::leanh::LeanObject,
    mut v_k_533_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_t_532_) == 0 {
        return v_k_533_;
    } else {
        let mut v_key_534_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_value_535_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_tail_536_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_537_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_key_534_ = crate::leanh::lean_ctor_get(v_t_532_, 0);
        crate::leanh::lean_inc(v_key_534_);
        v_value_535_ = crate::leanh::lean_ctor_get(v_t_532_, 1);
        crate::leanh::lean_inc(v_value_535_);
        v_tail_536_ = crate::leanh::lean_ctor_get(v_t_532_, 2);
        crate::leanh::lean_inc(v_tail_536_);
        crate::leanh::lean_dec_ref_known(v_t_532_, 3);
        v___x_537_ = crate::leanh::lean_apply_3(v_k_533_, v_key_534_, v_value_535_, v_tail_536_);
        return v___x_537_;
    }
}
pub unsafe fn l_Lean_AssocList_ctorElim(
    mut v_00_u03b1_538_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_539_: *mut crate::leanh::LeanObject,
    mut v_motive_540_: *mut crate::leanh::LeanObject,
    mut v_ctorIdx_541_: *mut crate::leanh::LeanObject,
    mut v_t_542_: *mut crate::leanh::LeanObject,
    mut v_h_543_: *mut crate::leanh::LeanObject,
    mut v_k_544_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_545_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_545_ = l_Lean_AssocList_ctorElim___redArg(v_t_542_, v_k_544_);
    return v___x_545_;
}
pub unsafe fn l_Lean_AssocList_ctorElim___boxed(
    mut v_00_u03b1_546_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_547_: *mut crate::leanh::LeanObject,
    mut v_motive_548_: *mut crate::leanh::LeanObject,
    mut v_ctorIdx_549_: *mut crate::leanh::LeanObject,
    mut v_t_550_: *mut crate::leanh::LeanObject,
    mut v_h_551_: *mut crate::leanh::LeanObject,
    mut v_k_552_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_553_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_553_ = l_Lean_AssocList_ctorElim(
        v_00_u03b1_546_,
        v_00_u03b2_547_,
        v_motive_548_,
        v_ctorIdx_549_,
        v_t_550_,
        v_h_551_,
        v_k_552_,
    );
    crate::leanh::lean_dec(v_ctorIdx_549_);
    return v_res_553_;
}
pub unsafe fn l_Lean_AssocList_nil_elim___redArg(
    mut v_t_554_: *mut crate::leanh::LeanObject,
    mut v_nil_555_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_556_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_556_ = l_Lean_AssocList_ctorElim___redArg(v_t_554_, v_nil_555_);
    return v___x_556_;
}
pub unsafe fn l_Lean_AssocList_nil_elim(
    mut v_00_u03b1_557_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_558_: *mut crate::leanh::LeanObject,
    mut v_motive_559_: *mut crate::leanh::LeanObject,
    mut v_t_560_: *mut crate::leanh::LeanObject,
    mut v_h_561_: *mut crate::leanh::LeanObject,
    mut v_nil_562_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_563_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_563_ = l_Lean_AssocList_ctorElim___redArg(v_t_560_, v_nil_562_);
    return v___x_563_;
}
pub unsafe fn l_Lean_AssocList_cons_elim___redArg(
    mut v_t_564_: *mut crate::leanh::LeanObject,
    mut v_cons_565_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_566_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_566_ = l_Lean_AssocList_ctorElim___redArg(v_t_564_, v_cons_565_);
    return v___x_566_;
}
pub unsafe fn l_Lean_AssocList_cons_elim(
    mut v_00_u03b1_567_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_568_: *mut crate::leanh::LeanObject,
    mut v_motive_569_: *mut crate::leanh::LeanObject,
    mut v_t_570_: *mut crate::leanh::LeanObject,
    mut v_h_571_: *mut crate::leanh::LeanObject,
    mut v_cons_572_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_573_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_573_ = l_Lean_AssocList_ctorElim___redArg(v_t_570_, v_cons_572_);
    return v___x_573_;
}
pub unsafe fn l_Lean_instInhabitedAssocList_default(
    mut v_00_u03b1_574_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_575_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_576_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_576_ = crate::leanh::lean_box(0);
    return v___x_576_;
}
pub unsafe fn l_Lean_instInhabitedAssocList(
    mut v_a_577_: *mut crate::leanh::LeanObject,
    mut v_a_578_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_579_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_579_ = crate::leanh::lean_box(0);
    return v___x_579_;
}
pub unsafe fn l_Lean_AssocList_empty(
    mut v_00_u03b1_580_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_581_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_582_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_582_ = crate::leanh::lean_box(0);
    return v___x_582_;
}
pub unsafe fn l_Lean_AssocList_instEmptyCollection(
    mut v_00_u03b1_583_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_584_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_585_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_585_ = crate::leanh::lean_box(0);
    return v___x_585_;
}
pub unsafe fn l_Lean_AssocList_insertNew___redArg(
    mut v_m_586_: *mut crate::leanh::LeanObject,
    mut v_k_587_: *mut crate::leanh::LeanObject,
    mut v_v_588_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_589_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_589_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_589_, 0, v_k_587_);
    crate::leanh::lean_ctor_set(v___x_589_, 1, v_v_588_);
    crate::leanh::lean_ctor_set(v___x_589_, 2, v_m_586_);
    return v___x_589_;
}
pub unsafe fn l_Lean_AssocList_insertNew(
    mut v_00_u03b1_590_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_591_: *mut crate::leanh::LeanObject,
    mut v_m_592_: *mut crate::leanh::LeanObject,
    mut v_k_593_: *mut crate::leanh::LeanObject,
    mut v_v_594_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_595_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_595_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_595_, 0, v_k_593_);
    crate::leanh::lean_ctor_set(v___x_595_, 1, v_v_594_);
    crate::leanh::lean_ctor_set(v___x_595_, 2, v_m_592_);
    return v___x_595_;
}
pub unsafe fn l_Lean_AssocList_isEmpty___redArg(mut v_x_596_: *mut crate::leanh::LeanObject) -> u8 {
    if crate::leanh::lean_obj_tag(v_x_596_) == 0 {
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
    mut v_x_599_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_600_: u8 = 0;
    let mut v_r_601_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_600_ = l_Lean_AssocList_isEmpty___redArg(v_x_599_);
    crate::leanh::lean_dec(v_x_599_);
    v_r_601_ = crate::leanh::lean_box((v_res_600_) as usize);
    return v_r_601_;
}
pub unsafe fn l_Lean_AssocList_isEmpty(
    mut v_00_u03b1_602_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_603_: *mut crate::leanh::LeanObject,
    mut v_x_604_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_605_: u8 = 0;
    v___x_605_ = l_Lean_AssocList_isEmpty___redArg(v_x_604_);
    return v___x_605_;
}
pub unsafe fn l_Lean_AssocList_isEmpty___boxed(
    mut v_00_u03b1_606_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_607_: *mut crate::leanh::LeanObject,
    mut v_x_608_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_609_: u8 = 0;
    let mut v_r_610_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_609_ = l_Lean_AssocList_isEmpty(v_00_u03b1_606_, v_00_u03b2_607_, v_x_608_);
    crate::leanh::lean_dec(v_x_608_);
    v_r_610_ = crate::leanh::lean_box((v_res_609_) as usize);
    return v_r_610_;
}
pub unsafe fn l_Lean_AssocList_foldlM___redArg(
    mut v_inst_611_: *mut crate::leanh::LeanObject,
    mut v_f_612_: *mut crate::leanh::LeanObject,
    mut v_x_613_: *mut crate::leanh::LeanObject,
    mut v_x_614_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_614_) == 0 {
        let mut v_toApplicative_615_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_toPure_616_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_617_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_toApplicative_615_ = crate::leanh::lean_ctor_get(v_inst_611_, 0);
        crate::leanh::lean_inc_ref(v_toApplicative_615_);
        crate::leanh::lean_dec(v_f_612_);
        crate::leanh::lean_dec_ref(v_inst_611_);
        v_toPure_616_ = crate::leanh::lean_ctor_get(v_toApplicative_615_, 1);
        crate::leanh::lean_inc(v_toPure_616_);
        crate::leanh::lean_dec_ref(v_toApplicative_615_);
        v___x_617_ = crate::leanh::lean_apply_2(v_toPure_616_, crate::leanh::lean_box(0), v_x_613_);
        return v___x_617_;
    } else {
        let mut v_toBind_618_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_key_619_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_value_620_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_tail_621_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___f_622_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_623_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_624_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_toBind_618_ = crate::leanh::lean_ctor_get(v_inst_611_, 1);
        crate::leanh::lean_inc(v_toBind_618_);
        v_key_619_ = crate::leanh::lean_ctor_get(v_x_614_, 0);
        crate::leanh::lean_inc(v_key_619_);
        v_value_620_ = crate::leanh::lean_ctor_get(v_x_614_, 1);
        crate::leanh::lean_inc(v_value_620_);
        v_tail_621_ = crate::leanh::lean_ctor_get(v_x_614_, 2);
        crate::leanh::lean_inc(v_tail_621_);
        crate::leanh::lean_dec_ref_known(v_x_614_, 3);
        crate::leanh::lean_inc(v_f_612_);
        v___f_622_ = crate::leanh::lean_alloc_closure(
            l_Lean_AssocList_foldlM___redArg___lam__0 as *mut core::ffi::c_void,
            4,
            3,
        );
        crate::leanh::lean_closure_set(v___f_622_, 0, v_inst_611_);
        crate::leanh::lean_closure_set(v___f_622_, 1, v_f_612_);
        crate::leanh::lean_closure_set(v___f_622_, 2, v_tail_621_);
        v___x_623_ = crate::leanh::lean_apply_3(v_f_612_, v_x_613_, v_key_619_, v_value_620_);
        v___x_624_ = crate::leanh::lean_apply_4(
            v_toBind_618_,
            crate::leanh::lean_box(0),
            crate::leanh::lean_box(0),
            v___x_623_,
            v___f_622_,
        );
        return v___x_624_;
    }
}
pub unsafe fn l_Lean_AssocList_foldlM___redArg___lam__0(
    mut v_inst_625_: *mut crate::leanh::LeanObject,
    mut v_f_626_: *mut crate::leanh::LeanObject,
    mut v_tail_627_: *mut crate::leanh::LeanObject,
    mut v_d_628_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_629_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_629_ = l_Lean_AssocList_foldlM___redArg(v_inst_625_, v_f_626_, v_d_628_, v_tail_627_);
    return v___x_629_;
}
pub unsafe fn l_Lean_AssocList_foldlM(
    mut v_00_u03b1_630_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_631_: *mut crate::leanh::LeanObject,
    mut v_00_u03b4_632_: *mut crate::leanh::LeanObject,
    mut v_m_633_: *mut crate::leanh::LeanObject,
    mut v_inst_634_: *mut crate::leanh::LeanObject,
    mut v_f_635_: *mut crate::leanh::LeanObject,
    mut v_x_636_: *mut crate::leanh::LeanObject,
    mut v_x_637_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_638_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_638_ = l_Lean_AssocList_foldlM___redArg(v_inst_634_, v_f_635_, v_x_636_, v_x_637_);
    return v___x_638_;
}
pub unsafe fn l_Lean_AssocList_foldl___redArg___lam__0(
    mut v_f_639_: *mut crate::leanh::LeanObject,
    mut v_x1_640_: *mut crate::leanh::LeanObject,
    mut v_x2_641_: *mut crate::leanh::LeanObject,
    mut v_x3_642_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_643_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_643_ = crate::leanh::lean_apply_3(v_f_639_, v_x1_640_, v_x2_641_, v_x3_642_);
    return v___x_643_;
}
pub unsafe fn l_Lean_AssocList_foldl___redArg(
    mut v_f_663_: *mut crate::leanh::LeanObject,
    mut v_init_664_: *mut crate::leanh::LeanObject,
    mut v_as_665_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_666_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_667_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_668_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_666_ = crate::leanh::lean_alloc_closure(
        l_Lean_AssocList_foldl___redArg___lam__0 as *mut core::ffi::c_void,
        4,
        1,
    );
    crate::leanh::lean_closure_set(v___f_666_, 0, v_f_663_);
    v___x_667_ = l_Lean_AssocList_foldl___redArg___closed__9;
    v___x_668_ = l_Lean_AssocList_foldlM___redArg(v___x_667_, v___f_666_, v_init_664_, v_as_665_);
    return v___x_668_;
}
pub unsafe fn l_Lean_AssocList_foldl(
    mut v_00_u03b1_669_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_670_: *mut crate::leanh::LeanObject,
    mut v_00_u03b4_671_: *mut crate::leanh::LeanObject,
    mut v_f_672_: *mut crate::leanh::LeanObject,
    mut v_init_673_: *mut crate::leanh::LeanObject,
    mut v_as_674_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_675_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_676_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_677_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_675_ = crate::leanh::lean_alloc_closure(
        l_Lean_AssocList_foldl___redArg___lam__0 as *mut core::ffi::c_void,
        4,
        1,
    );
    crate::leanh::lean_closure_set(v___f_675_, 0, v_f_672_);
    v___x_676_ = l_Lean_AssocList_foldl___redArg___closed__9;
    v___x_677_ = l_Lean_AssocList_foldlM___redArg(v___x_676_, v___f_675_, v_init_673_, v_as_674_);
    return v___x_677_;
}
pub unsafe fn l_Lean_AssocList_foldlM___at___00Lean_AssocList_toList_spec__0___redArg(
    mut v_x_678_: *mut crate::leanh::LeanObject,
    mut v_x_679_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_key_680_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_681_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_682_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_683_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_684_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_679_) == 0 {
                    return v_x_678_;
                } else {
                    v_key_680_ = crate::leanh::lean_ctor_get(v_x_679_, 0);
                    v_value_681_ = crate::leanh::lean_ctor_get(v_x_679_, 1);
                    v_tail_682_ = crate::leanh::lean_ctor_get(v_x_679_, 2);
                    crate::leanh::lean_inc(v_value_681_);
                    crate::leanh::lean_inc(v_key_680_);
                    v___x_683_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_683_, 0, v_key_680_);
                    crate::leanh::lean_ctor_set(v___x_683_, 1, v_value_681_);
                    v___x_684_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_684_, 0, v___x_683_);
                    crate::leanh::lean_ctor_set(v___x_684_, 1, v_x_678_);
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
    mut v_x_686_: *mut crate::leanh::LeanObject,
    mut v_x_687_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_688_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_688_ =
        l_Lean_AssocList_foldlM___at___00Lean_AssocList_toList_spec__0___redArg(v_x_686_, v_x_687_);
    crate::leanh::lean_dec(v_x_687_);
    return v_res_688_;
}
pub unsafe fn l_Lean_AssocList_toList___redArg(
    mut v_as_689_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_690_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_691_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_692_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_690_ = crate::leanh::lean_box(0);
    v___x_691_ = l_Lean_AssocList_foldlM___at___00Lean_AssocList_toList_spec__0___redArg(
        v___x_690_, v_as_689_,
    );
    v___x_692_ = l_List_reverse___redArg(v___x_691_);
    return v___x_692_;
}
pub unsafe fn l_Lean_AssocList_toList___redArg___boxed(
    mut v_as_693_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_694_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_694_ = l_Lean_AssocList_toList___redArg(v_as_693_);
    crate::leanh::lean_dec(v_as_693_);
    return v_res_694_;
}
pub unsafe fn l_Lean_AssocList_toList(
    mut v_00_u03b1_695_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_696_: *mut crate::leanh::LeanObject,
    mut v_as_697_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_698_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_698_ = l_Lean_AssocList_toList___redArg(v_as_697_);
    return v___x_698_;
}
pub unsafe fn l_Lean_AssocList_toList___boxed(
    mut v_00_u03b1_699_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_700_: *mut crate::leanh::LeanObject,
    mut v_as_701_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_702_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_702_ = l_Lean_AssocList_toList(v_00_u03b1_699_, v_00_u03b2_700_, v_as_701_);
    crate::leanh::lean_dec(v_as_701_);
    return v_res_702_;
}
pub unsafe fn l_Lean_AssocList_foldlM___at___00Lean_AssocList_toList_spec__0(
    mut v_00_u03b1_703_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_704_: *mut crate::leanh::LeanObject,
    mut v_x_705_: *mut crate::leanh::LeanObject,
    mut v_x_706_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_707_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_707_ =
        l_Lean_AssocList_foldlM___at___00Lean_AssocList_toList_spec__0___redArg(v_x_705_, v_x_706_);
    return v___x_707_;
}
pub unsafe fn l_Lean_AssocList_foldlM___at___00Lean_AssocList_toList_spec__0___boxed(
    mut v_00_u03b1_708_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_709_: *mut crate::leanh::LeanObject,
    mut v_x_710_: *mut crate::leanh::LeanObject,
    mut v_x_711_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_712_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_712_ = l_Lean_AssocList_foldlM___at___00Lean_AssocList_toList_spec__0(
        v_00_u03b1_708_,
        v_00_u03b2_709_,
        v_x_710_,
        v_x_711_,
    );
    crate::leanh::lean_dec(v_x_711_);
    return v_res_712_;
}
pub unsafe fn l_Lean_AssocList_forM___redArg(
    mut v_inst_713_: *mut crate::leanh::LeanObject,
    mut v_f_714_: *mut crate::leanh::LeanObject,
    mut v_x_715_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_715_) == 0 {
        let mut v_toApplicative_716_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_toPure_717_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_718_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_719_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_toApplicative_716_ = crate::leanh::lean_ctor_get(v_inst_713_, 0);
        crate::leanh::lean_inc_ref(v_toApplicative_716_);
        crate::leanh::lean_dec(v_f_714_);
        crate::leanh::lean_dec_ref(v_inst_713_);
        v_toPure_717_ = crate::leanh::lean_ctor_get(v_toApplicative_716_, 1);
        crate::leanh::lean_inc(v_toPure_717_);
        crate::leanh::lean_dec_ref(v_toApplicative_716_);
        v___x_718_ = crate::leanh::lean_box(0);
        v___x_719_ =
            crate::leanh::lean_apply_2(v_toPure_717_, crate::leanh::lean_box(0), v___x_718_);
        return v___x_719_;
    } else {
        let mut v_toBind_720_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_key_721_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_value_722_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_tail_723_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___f_724_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_725_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_726_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_toBind_720_ = crate::leanh::lean_ctor_get(v_inst_713_, 1);
        crate::leanh::lean_inc(v_toBind_720_);
        v_key_721_ = crate::leanh::lean_ctor_get(v_x_715_, 0);
        crate::leanh::lean_inc(v_key_721_);
        v_value_722_ = crate::leanh::lean_ctor_get(v_x_715_, 1);
        crate::leanh::lean_inc(v_value_722_);
        v_tail_723_ = crate::leanh::lean_ctor_get(v_x_715_, 2);
        crate::leanh::lean_inc(v_tail_723_);
        crate::leanh::lean_dec_ref_known(v_x_715_, 3);
        crate::leanh::lean_inc(v_f_714_);
        v___f_724_ = crate::leanh::lean_alloc_closure(
            l_Lean_AssocList_forM___redArg___lam__0 as *mut core::ffi::c_void,
            4,
            3,
        );
        crate::leanh::lean_closure_set(v___f_724_, 0, v_inst_713_);
        crate::leanh::lean_closure_set(v___f_724_, 1, v_f_714_);
        crate::leanh::lean_closure_set(v___f_724_, 2, v_tail_723_);
        v___x_725_ = crate::leanh::lean_apply_2(v_f_714_, v_key_721_, v_value_722_);
        v___x_726_ = crate::leanh::lean_apply_4(
            v_toBind_720_,
            crate::leanh::lean_box(0),
            crate::leanh::lean_box(0),
            v___x_725_,
            v___f_724_,
        );
        return v___x_726_;
    }
}
pub unsafe fn l_Lean_AssocList_forM___redArg___lam__0(
    mut v_inst_727_: *mut crate::leanh::LeanObject,
    mut v_f_728_: *mut crate::leanh::LeanObject,
    mut v_tail_729_: *mut crate::leanh::LeanObject,
    mut v_____r_730_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_731_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_731_ = l_Lean_AssocList_forM___redArg(v_inst_727_, v_f_728_, v_tail_729_);
    return v___x_731_;
}
pub unsafe fn l_Lean_AssocList_forM(
    mut v_00_u03b1_732_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_733_: *mut crate::leanh::LeanObject,
    mut v_m_734_: *mut crate::leanh::LeanObject,
    mut v_inst_735_: *mut crate::leanh::LeanObject,
    mut v_f_736_: *mut crate::leanh::LeanObject,
    mut v_x_737_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_738_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_738_ = l_Lean_AssocList_forM___redArg(v_inst_735_, v_f_736_, v_x_737_);
    return v___x_738_;
}
pub unsafe fn l_Lean_AssocList_mapKey___redArg(
    mut v_f_739_: *mut crate::leanh::LeanObject,
    mut v_x_740_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_741_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_key_742_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_743_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_744_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_746_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_747_: u8 = 0;
    let mut v___x_748_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_749_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_751_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_752_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_753_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_740_) == 0 {
                    crate::leanh::lean_dec(v_f_739_);
                    v___x_741_ = crate::leanh::lean_box(0);
                    return v___x_741_;
                } else {
                    v_key_742_ = crate::leanh::lean_ctor_get(v_x_740_, 0);
                    v_value_743_ = crate::leanh::lean_ctor_get(v_x_740_, 1);
                    v_tail_744_ = crate::leanh::lean_ctor_get(v_x_740_, 2);
                    v_isSharedCheck_753_ = (!crate::leanh::lean_is_exclusive(v_x_740_)) as u8;
                    if v_isSharedCheck_753_ == 0 {
                        v___x_746_ = v_x_740_;
                        v_isShared_747_ = v_isSharedCheck_753_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_tail_744_);
                        crate::leanh::lean_inc(v_value_743_);
                        crate::leanh::lean_inc(v_key_742_);
                        crate::leanh::lean_dec(v_x_740_);
                        v___x_746_ = crate::leanh::lean_box(0);
                        v_isShared_747_ = v_isSharedCheck_753_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                crate::leanh::lean_inc(v_f_739_);
                v___x_748_ = crate::leanh::lean_apply_1(v_f_739_, v_key_742_);
                v___x_749_ = l_Lean_AssocList_mapKey___redArg(v_f_739_, v_tail_744_);
                if v_isShared_747_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_746_, 2, v___x_749_);
                    crate::leanh::lean_ctor_set(v___x_746_, 0, v___x_748_);
                    v___x_751_ = v___x_746_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_752_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_752_, 0, v___x_748_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_752_, 1, v_value_743_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_752_, 2, v___x_749_);
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
    mut v_00_u03b1_754_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_755_: *mut crate::leanh::LeanObject,
    mut v_00_u03b4_756_: *mut crate::leanh::LeanObject,
    mut v_f_757_: *mut crate::leanh::LeanObject,
    mut v_x_758_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_759_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_759_ = l_Lean_AssocList_mapKey___redArg(v_f_757_, v_x_758_);
    return v___x_759_;
}
pub unsafe fn l_Lean_AssocList_mapVal___redArg(
    mut v_f_760_: *mut crate::leanh::LeanObject,
    mut v_x_761_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_762_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_key_763_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_764_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_765_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_767_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_768_: u8 = 0;
    let mut v___x_769_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_770_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_772_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_773_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_774_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_761_) == 0 {
                    crate::leanh::lean_dec(v_f_760_);
                    v___x_762_ = crate::leanh::lean_box(0);
                    return v___x_762_;
                } else {
                    v_key_763_ = crate::leanh::lean_ctor_get(v_x_761_, 0);
                    v_value_764_ = crate::leanh::lean_ctor_get(v_x_761_, 1);
                    v_tail_765_ = crate::leanh::lean_ctor_get(v_x_761_, 2);
                    v_isSharedCheck_774_ = (!crate::leanh::lean_is_exclusive(v_x_761_)) as u8;
                    if v_isSharedCheck_774_ == 0 {
                        v___x_767_ = v_x_761_;
                        v_isShared_768_ = v_isSharedCheck_774_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_tail_765_);
                        crate::leanh::lean_inc(v_value_764_);
                        crate::leanh::lean_inc(v_key_763_);
                        crate::leanh::lean_dec(v_x_761_);
                        v___x_767_ = crate::leanh::lean_box(0);
                        v_isShared_768_ = v_isSharedCheck_774_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                crate::leanh::lean_inc(v_f_760_);
                v___x_769_ = crate::leanh::lean_apply_1(v_f_760_, v_value_764_);
                v___x_770_ = l_Lean_AssocList_mapVal___redArg(v_f_760_, v_tail_765_);
                if v_isShared_768_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_767_, 2, v___x_770_);
                    crate::leanh::lean_ctor_set(v___x_767_, 1, v___x_769_);
                    v___x_772_ = v___x_767_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_773_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_773_, 0, v_key_763_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_773_, 1, v___x_769_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_773_, 2, v___x_770_);
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
    mut v_00_u03b1_775_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_776_: *mut crate::leanh::LeanObject,
    mut v_00_u03b4_777_: *mut crate::leanh::LeanObject,
    mut v_f_778_: *mut crate::leanh::LeanObject,
    mut v_x_779_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_780_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_780_ = l_Lean_AssocList_mapVal___redArg(v_f_778_, v_x_779_);
    return v___x_780_;
}
pub unsafe fn l_Lean_AssocList_findEntry_x3f___redArg(
    mut v_inst_781_: *mut crate::leanh::LeanObject,
    mut v_a_782_: *mut crate::leanh::LeanObject,
    mut v_x_783_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_784_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_key_785_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_786_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_787_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_788_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_789_: u8 = 0;
    let mut v___x_791_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_792_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_783_) == 0 {
                    crate::leanh::lean_dec(v_a_782_);
                    crate::leanh::lean_dec_ref(v_inst_781_);
                    v___x_784_ = crate::leanh::lean_box(0);
                    return v___x_784_;
                } else {
                    v_key_785_ = crate::leanh::lean_ctor_get(v_x_783_, 0);
                    crate::leanh::lean_inc_n(v_key_785_, 2);
                    v_value_786_ = crate::leanh::lean_ctor_get(v_x_783_, 1);
                    crate::leanh::lean_inc(v_value_786_);
                    v_tail_787_ = crate::leanh::lean_ctor_get(v_x_783_, 2);
                    crate::leanh::lean_inc(v_tail_787_);
                    crate::leanh::lean_dec_ref_known(v_x_783_, 3);
                    crate::leanh::lean_inc_ref(v_inst_781_);
                    crate::leanh::lean_inc(v_a_782_);
                    v___x_788_ = crate::leanh::lean_apply_2(v_inst_781_, v_key_785_, v_a_782_);
                    v___x_789_ = (crate::leanh::lean_unbox(v___x_788_) as u8);
                    if v___x_789_ == 0 {
                        crate::leanh::lean_dec(v_value_786_);
                        crate::leanh::lean_dec(v_key_785_);
                        v_x_783_ = v_tail_787_;
                        state = 0;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v_tail_787_);
                        crate::leanh::lean_dec(v_a_782_);
                        crate::leanh::lean_dec_ref(v_inst_781_);
                        v___x_791_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_791_, 0, v_key_785_);
                        crate::leanh::lean_ctor_set(v___x_791_, 1, v_value_786_);
                        v___x_792_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_792_, 0, v___x_791_);
                        return v___x_792_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_AssocList_findEntry_x3f(
    mut v_00_u03b1_793_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_794_: *mut crate::leanh::LeanObject,
    mut v_inst_795_: *mut crate::leanh::LeanObject,
    mut v_a_796_: *mut crate::leanh::LeanObject,
    mut v_x_797_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_798_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_798_ = l_Lean_AssocList_findEntry_x3f___redArg(v_inst_795_, v_a_796_, v_x_797_);
    return v___x_798_;
}
pub unsafe fn l_Lean_AssocList_find_x3f___redArg(
    mut v_inst_799_: *mut crate::leanh::LeanObject,
    mut v_a_800_: *mut crate::leanh::LeanObject,
    mut v_x_801_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_802_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_key_803_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_804_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_805_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_806_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_807_: u8 = 0;
    let mut v___x_809_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_801_) == 0 {
                    crate::leanh::lean_dec(v_a_800_);
                    crate::leanh::lean_dec_ref(v_inst_799_);
                    v___x_802_ = crate::leanh::lean_box(0);
                    return v___x_802_;
                } else {
                    v_key_803_ = crate::leanh::lean_ctor_get(v_x_801_, 0);
                    crate::leanh::lean_inc(v_key_803_);
                    v_value_804_ = crate::leanh::lean_ctor_get(v_x_801_, 1);
                    crate::leanh::lean_inc(v_value_804_);
                    v_tail_805_ = crate::leanh::lean_ctor_get(v_x_801_, 2);
                    crate::leanh::lean_inc(v_tail_805_);
                    crate::leanh::lean_dec_ref_known(v_x_801_, 3);
                    crate::leanh::lean_inc_ref(v_inst_799_);
                    crate::leanh::lean_inc(v_a_800_);
                    v___x_806_ = crate::leanh::lean_apply_2(v_inst_799_, v_key_803_, v_a_800_);
                    v___x_807_ = (crate::leanh::lean_unbox(v___x_806_) as u8);
                    if v___x_807_ == 0 {
                        crate::leanh::lean_dec(v_value_804_);
                        v_x_801_ = v_tail_805_;
                        state = 0;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v_tail_805_);
                        crate::leanh::lean_dec(v_a_800_);
                        crate::leanh::lean_dec_ref(v_inst_799_);
                        v___x_809_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_809_, 0, v_value_804_);
                        return v___x_809_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_AssocList_find_x3f(
    mut v_00_u03b1_810_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_811_: *mut crate::leanh::LeanObject,
    mut v_inst_812_: *mut crate::leanh::LeanObject,
    mut v_a_813_: *mut crate::leanh::LeanObject,
    mut v_x_814_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_815_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_815_ = l_Lean_AssocList_find_x3f___redArg(v_inst_812_, v_a_813_, v_x_814_);
    return v___x_815_;
}
pub unsafe fn l_Lean_AssocList_contains___redArg(
    mut v_inst_816_: *mut crate::leanh::LeanObject,
    mut v_a_817_: *mut crate::leanh::LeanObject,
    mut v_x_818_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_819_: u8 = 0;
    let mut v_key_820_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_821_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_822_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_823_: u8 = 0;
    let mut v___x_825_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_818_) == 0 {
                    crate::leanh::lean_dec(v_a_817_);
                    crate::leanh::lean_dec_ref(v_inst_816_);
                    v___x_819_ = 0;
                    return v___x_819_;
                } else {
                    v_key_820_ = crate::leanh::lean_ctor_get(v_x_818_, 0);
                    crate::leanh::lean_inc(v_key_820_);
                    v_tail_821_ = crate::leanh::lean_ctor_get(v_x_818_, 2);
                    crate::leanh::lean_inc(v_tail_821_);
                    crate::leanh::lean_dec_ref_known(v_x_818_, 3);
                    crate::leanh::lean_inc_ref(v_inst_816_);
                    crate::leanh::lean_inc(v_a_817_);
                    v___x_822_ = crate::leanh::lean_apply_2(v_inst_816_, v_key_820_, v_a_817_);
                    v___x_823_ = (crate::leanh::lean_unbox(v___x_822_) as u8);
                    if v___x_823_ == 0 {
                        v_x_818_ = v_tail_821_;
                        state = 0;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v_tail_821_);
                        crate::leanh::lean_dec(v_a_817_);
                        crate::leanh::lean_dec_ref(v_inst_816_);
                        v___x_825_ = (crate::leanh::lean_unbox(v___x_822_) as u8);
                        return v___x_825_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_AssocList_contains___redArg___boxed(
    mut v_inst_826_: *mut crate::leanh::LeanObject,
    mut v_a_827_: *mut crate::leanh::LeanObject,
    mut v_x_828_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_829_: u8 = 0;
    let mut v_r_830_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_829_ = l_Lean_AssocList_contains___redArg(v_inst_826_, v_a_827_, v_x_828_);
    v_r_830_ = crate::leanh::lean_box((v_res_829_) as usize);
    return v_r_830_;
}
pub unsafe fn l_Lean_AssocList_contains(
    mut v_00_u03b1_831_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_832_: *mut crate::leanh::LeanObject,
    mut v_inst_833_: *mut crate::leanh::LeanObject,
    mut v_a_834_: *mut crate::leanh::LeanObject,
    mut v_x_835_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_836_: u8 = 0;
    v___x_836_ = l_Lean_AssocList_contains___redArg(v_inst_833_, v_a_834_, v_x_835_);
    return v___x_836_;
}
pub unsafe fn l_Lean_AssocList_contains___boxed(
    mut v_00_u03b1_837_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_838_: *mut crate::leanh::LeanObject,
    mut v_inst_839_: *mut crate::leanh::LeanObject,
    mut v_a_840_: *mut crate::leanh::LeanObject,
    mut v_x_841_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_842_: u8 = 0;
    let mut v_r_843_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_842_ = l_Lean_AssocList_contains(
        v_00_u03b1_837_,
        v_00_u03b2_838_,
        v_inst_839_,
        v_a_840_,
        v_x_841_,
    );
    v_r_843_ = crate::leanh::lean_box((v_res_842_) as usize);
    return v_r_843_;
}
pub unsafe fn l_Lean_AssocList_replace___redArg(
    mut v_inst_844_: *mut crate::leanh::LeanObject,
    mut v_a_845_: *mut crate::leanh::LeanObject,
    mut v_b_846_: *mut crate::leanh::LeanObject,
    mut v_x_847_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_key_848_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_849_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_850_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_852_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_853_: u8 = 0;
    let mut v___x_854_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_855_: u8 = 0;
    let mut v___x_856_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_858_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_859_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_861_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_862_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_863_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_847_) == 0 {
                    crate::leanh::lean_dec(v_b_846_);
                    crate::leanh::lean_dec(v_a_845_);
                    crate::leanh::lean_dec_ref(v_inst_844_);
                    return v_x_847_;
                } else {
                    v_key_848_ = crate::leanh::lean_ctor_get(v_x_847_, 0);
                    v_value_849_ = crate::leanh::lean_ctor_get(v_x_847_, 1);
                    v_tail_850_ = crate::leanh::lean_ctor_get(v_x_847_, 2);
                    v_isSharedCheck_863_ = (!crate::leanh::lean_is_exclusive(v_x_847_)) as u8;
                    if v_isSharedCheck_863_ == 0 {
                        v___x_852_ = v_x_847_;
                        v_isShared_853_ = v_isSharedCheck_863_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_tail_850_);
                        crate::leanh::lean_inc(v_value_849_);
                        crate::leanh::lean_inc(v_key_848_);
                        crate::leanh::lean_dec(v_x_847_);
                        v___x_852_ = crate::leanh::lean_box(0);
                        v_isShared_853_ = v_isSharedCheck_863_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                crate::leanh::lean_inc_ref(v_inst_844_);
                crate::leanh::lean_inc(v_a_845_);
                crate::leanh::lean_inc(v_key_848_);
                v___x_854_ = crate::leanh::lean_apply_2(v_inst_844_, v_key_848_, v_a_845_);
                v___x_855_ = (crate::leanh::lean_unbox(v___x_854_) as u8);
                if v___x_855_ == 0 {
                    v___x_856_ = l_Lean_AssocList_replace___redArg(
                        v_inst_844_,
                        v_a_845_,
                        v_b_846_,
                        v_tail_850_,
                    );
                    if v_isShared_853_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_852_, 2, v___x_856_);
                        v___x_858_ = v___x_852_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_859_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_859_, 0, v_key_848_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_859_, 1, v_value_849_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_859_, 2, v___x_856_);
                        v___x_858_ = v_reuseFailAlloc_859_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_value_849_);
                    crate::leanh::lean_dec(v_key_848_);
                    crate::leanh::lean_dec_ref(v_inst_844_);
                    if v_isShared_853_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_852_, 1, v_b_846_);
                        crate::leanh::lean_ctor_set(v___x_852_, 0, v_a_845_);
                        v___x_861_ = v___x_852_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_862_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_862_, 0, v_a_845_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_862_, 1, v_b_846_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_862_, 2, v_tail_850_);
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
    mut v_00_u03b1_864_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_865_: *mut crate::leanh::LeanObject,
    mut v_inst_866_: *mut crate::leanh::LeanObject,
    mut v_a_867_: *mut crate::leanh::LeanObject,
    mut v_b_868_: *mut crate::leanh::LeanObject,
    mut v_x_869_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_870_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_870_ = l_Lean_AssocList_replace___redArg(v_inst_866_, v_a_867_, v_b_868_, v_x_869_);
    return v___x_870_;
}
pub unsafe fn l_Lean_AssocList_insert___redArg(
    mut v_inst_871_: *mut crate::leanh::LeanObject,
    mut v_m_872_: *mut crate::leanh::LeanObject,
    mut v_k_873_: *mut crate::leanh::LeanObject,
    mut v_v_874_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_875_: u8 = 0;
    crate::leanh::lean_inc(v_m_872_);
    crate::leanh::lean_inc(v_k_873_);
    crate::leanh::lean_inc_ref(v_inst_871_);
    v___x_875_ = l_Lean_AssocList_contains___redArg(v_inst_871_, v_k_873_, v_m_872_);
    if v___x_875_ == 0 {
        let mut v___x_876_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec_ref(v_inst_871_);
        v___x_876_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_876_, 0, v_k_873_);
        crate::leanh::lean_ctor_set(v___x_876_, 1, v_v_874_);
        crate::leanh::lean_ctor_set(v___x_876_, 2, v_m_872_);
        return v___x_876_;
    } else {
        let mut v___x_877_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_877_ = l_Lean_AssocList_replace___redArg(v_inst_871_, v_k_873_, v_v_874_, v_m_872_);
        return v___x_877_;
    }
}
pub unsafe fn l_Lean_AssocList_insert(
    mut v_00_u03b1_878_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_879_: *mut crate::leanh::LeanObject,
    mut v_inst_880_: *mut crate::leanh::LeanObject,
    mut v_m_881_: *mut crate::leanh::LeanObject,
    mut v_k_882_: *mut crate::leanh::LeanObject,
    mut v_v_883_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_884_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_884_ = l_Lean_AssocList_insert___redArg(v_inst_880_, v_m_881_, v_k_882_, v_v_883_);
    return v___x_884_;
}
pub unsafe fn l_Lean_AssocList_erase___redArg(
    mut v_inst_885_: *mut crate::leanh::LeanObject,
    mut v_a_886_: *mut crate::leanh::LeanObject,
    mut v_x_887_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_key_888_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_889_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_890_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_892_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_893_: u8 = 0;
    let mut v___x_894_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_895_: u8 = 0;
    let mut v___x_896_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_898_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_899_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_900_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_887_) == 0 {
                    crate::leanh::lean_dec(v_a_886_);
                    crate::leanh::lean_dec_ref(v_inst_885_);
                    return v_x_887_;
                } else {
                    v_key_888_ = crate::leanh::lean_ctor_get(v_x_887_, 0);
                    v_value_889_ = crate::leanh::lean_ctor_get(v_x_887_, 1);
                    v_tail_890_ = crate::leanh::lean_ctor_get(v_x_887_, 2);
                    v_isSharedCheck_900_ = (!crate::leanh::lean_is_exclusive(v_x_887_)) as u8;
                    if v_isSharedCheck_900_ == 0 {
                        v___x_892_ = v_x_887_;
                        v_isShared_893_ = v_isSharedCheck_900_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_tail_890_);
                        crate::leanh::lean_inc(v_value_889_);
                        crate::leanh::lean_inc(v_key_888_);
                        crate::leanh::lean_dec(v_x_887_);
                        v___x_892_ = crate::leanh::lean_box(0);
                        v_isShared_893_ = v_isSharedCheck_900_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                crate::leanh::lean_inc_ref(v_inst_885_);
                crate::leanh::lean_inc(v_a_886_);
                crate::leanh::lean_inc(v_key_888_);
                v___x_894_ = crate::leanh::lean_apply_2(v_inst_885_, v_key_888_, v_a_886_);
                v___x_895_ = (crate::leanh::lean_unbox(v___x_894_) as u8);
                if v___x_895_ == 0 {
                    v___x_896_ =
                        l_Lean_AssocList_erase___redArg(v_inst_885_, v_a_886_, v_tail_890_);
                    if v_isShared_893_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_892_, 2, v___x_896_);
                        v___x_898_ = v___x_892_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_899_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_899_, 0, v_key_888_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_899_, 1, v_value_889_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_899_, 2, v___x_896_);
                        v___x_898_ = v_reuseFailAlloc_899_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_892_);
                    crate::leanh::lean_dec(v_value_889_);
                    crate::leanh::lean_dec(v_key_888_);
                    crate::leanh::lean_dec(v_a_886_);
                    crate::leanh::lean_dec_ref(v_inst_885_);
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
    mut v_00_u03b1_901_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_902_: *mut crate::leanh::LeanObject,
    mut v_inst_903_: *mut crate::leanh::LeanObject,
    mut v_a_904_: *mut crate::leanh::LeanObject,
    mut v_x_905_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_906_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_906_ = l_Lean_AssocList_erase___redArg(v_inst_903_, v_a_904_, v_x_905_);
    return v___x_906_;
}
pub unsafe fn l_Lean_AssocList_any___redArg(
    mut v_p_907_: *mut crate::leanh::LeanObject,
    mut v_x_908_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_909_: u8 = 0;
    let mut v_key_910_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_911_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_912_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_913_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_914_: u8 = 0;
    let mut v___x_916_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_908_) == 0 {
                    crate::leanh::lean_dec_ref(v_p_907_);
                    v___x_909_ = 0;
                    return v___x_909_;
                } else {
                    v_key_910_ = crate::leanh::lean_ctor_get(v_x_908_, 0);
                    crate::leanh::lean_inc(v_key_910_);
                    v_value_911_ = crate::leanh::lean_ctor_get(v_x_908_, 1);
                    crate::leanh::lean_inc(v_value_911_);
                    v_tail_912_ = crate::leanh::lean_ctor_get(v_x_908_, 2);
                    crate::leanh::lean_inc(v_tail_912_);
                    crate::leanh::lean_dec_ref_known(v_x_908_, 3);
                    crate::leanh::lean_inc_ref(v_p_907_);
                    v___x_913_ = crate::leanh::lean_apply_2(v_p_907_, v_key_910_, v_value_911_);
                    v___x_914_ = (crate::leanh::lean_unbox(v___x_913_) as u8);
                    if v___x_914_ == 0 {
                        v_x_908_ = v_tail_912_;
                        state = 0;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v_tail_912_);
                        crate::leanh::lean_dec_ref(v_p_907_);
                        v___x_916_ = (crate::leanh::lean_unbox(v___x_913_) as u8);
                        return v___x_916_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_AssocList_any___redArg___boxed(
    mut v_p_917_: *mut crate::leanh::LeanObject,
    mut v_x_918_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_919_: u8 = 0;
    let mut v_r_920_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_919_ = l_Lean_AssocList_any___redArg(v_p_917_, v_x_918_);
    v_r_920_ = crate::leanh::lean_box((v_res_919_) as usize);
    return v_r_920_;
}
pub unsafe fn l_Lean_AssocList_any(
    mut v_00_u03b1_921_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_922_: *mut crate::leanh::LeanObject,
    mut v_p_923_: *mut crate::leanh::LeanObject,
    mut v_x_924_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_925_: u8 = 0;
    v___x_925_ = l_Lean_AssocList_any___redArg(v_p_923_, v_x_924_);
    return v___x_925_;
}
pub unsafe fn l_Lean_AssocList_any___boxed(
    mut v_00_u03b1_926_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_927_: *mut crate::leanh::LeanObject,
    mut v_p_928_: *mut crate::leanh::LeanObject,
    mut v_x_929_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_930_: u8 = 0;
    let mut v_r_931_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_930_ = l_Lean_AssocList_any(v_00_u03b1_926_, v_00_u03b2_927_, v_p_928_, v_x_929_);
    v_r_931_ = crate::leanh::lean_box((v_res_930_) as usize);
    return v_r_931_;
}
pub unsafe fn l_Lean_AssocList_all___redArg(
    mut v_p_932_: *mut crate::leanh::LeanObject,
    mut v_x_933_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_934_: u8 = 0;
    let mut v_key_935_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_936_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_937_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_938_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_939_: u8 = 0;
    let mut v___x_940_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_933_) == 0 {
                    crate::leanh::lean_dec_ref(v_p_932_);
                    v___x_934_ = 1;
                    return v___x_934_;
                } else {
                    v_key_935_ = crate::leanh::lean_ctor_get(v_x_933_, 0);
                    crate::leanh::lean_inc(v_key_935_);
                    v_value_936_ = crate::leanh::lean_ctor_get(v_x_933_, 1);
                    crate::leanh::lean_inc(v_value_936_);
                    v_tail_937_ = crate::leanh::lean_ctor_get(v_x_933_, 2);
                    crate::leanh::lean_inc(v_tail_937_);
                    crate::leanh::lean_dec_ref_known(v_x_933_, 3);
                    crate::leanh::lean_inc_ref(v_p_932_);
                    v___x_938_ = crate::leanh::lean_apply_2(v_p_932_, v_key_935_, v_value_936_);
                    v___x_939_ = (crate::leanh::lean_unbox(v___x_938_) as u8);
                    if v___x_939_ == 0 {
                        crate::leanh::lean_dec(v_tail_937_);
                        crate::leanh::lean_dec_ref(v_p_932_);
                        v___x_940_ = (crate::leanh::lean_unbox(v___x_938_) as u8);
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
    mut v_p_942_: *mut crate::leanh::LeanObject,
    mut v_x_943_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_944_: u8 = 0;
    let mut v_r_945_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_944_ = l_Lean_AssocList_all___redArg(v_p_942_, v_x_943_);
    v_r_945_ = crate::leanh::lean_box((v_res_944_) as usize);
    return v_r_945_;
}
pub unsafe fn l_Lean_AssocList_all(
    mut v_00_u03b1_946_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_947_: *mut crate::leanh::LeanObject,
    mut v_p_948_: *mut crate::leanh::LeanObject,
    mut v_x_949_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_950_: u8 = 0;
    v___x_950_ = l_Lean_AssocList_all___redArg(v_p_948_, v_x_949_);
    return v___x_950_;
}
pub unsafe fn l_Lean_AssocList_all___boxed(
    mut v_00_u03b1_951_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_952_: *mut crate::leanh::LeanObject,
    mut v_p_953_: *mut crate::leanh::LeanObject,
    mut v_x_954_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_955_: u8 = 0;
    let mut v_r_956_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_955_ = l_Lean_AssocList_all(v_00_u03b1_951_, v_00_u03b2_952_, v_p_953_, v_x_954_);
    v_r_956_ = crate::leanh::lean_box((v_res_955_) as usize);
    return v_r_956_;
}
pub unsafe fn l___private_Lean_Data_AssocList_0__Lean_AssocList_forIn_loop___redArg(
    mut v_inst_957_: *mut crate::leanh::LeanObject,
    mut v_f_958_: *mut crate::leanh::LeanObject,
    mut v_x_959_: *mut crate::leanh::LeanObject,
    mut v_x_960_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_960_) == 0 {
        let mut v_toApplicative_961_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_toPure_962_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_963_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_toApplicative_961_ = crate::leanh::lean_ctor_get(v_inst_957_, 0);
        crate::leanh::lean_inc_ref(v_toApplicative_961_);
        crate::leanh::lean_dec(v_f_958_);
        crate::leanh::lean_dec_ref(v_inst_957_);
        v_toPure_962_ = crate::leanh::lean_ctor_get(v_toApplicative_961_, 1);
        crate::leanh::lean_inc(v_toPure_962_);
        crate::leanh::lean_dec_ref(v_toApplicative_961_);
        v___x_963_ = crate::leanh::lean_apply_2(v_toPure_962_, crate::leanh::lean_box(0), v_x_959_);
        return v___x_963_;
    } else {
        let mut v_toApplicative_964_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_toBind_965_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_toPure_966_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_key_967_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_value_968_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_tail_969_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___f_970_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_971_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_972_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_973_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_toApplicative_964_ = crate::leanh::lean_ctor_get(v_inst_957_, 0);
        v_toBind_965_ = crate::leanh::lean_ctor_get(v_inst_957_, 1);
        crate::leanh::lean_inc(v_toBind_965_);
        v_toPure_966_ = crate::leanh::lean_ctor_get(v_toApplicative_964_, 1);
        crate::leanh::lean_inc(v_toPure_966_);
        v_key_967_ = crate::leanh::lean_ctor_get(v_x_960_, 0);
        crate::leanh::lean_inc(v_key_967_);
        v_value_968_ = crate::leanh::lean_ctor_get(v_x_960_, 1);
        crate::leanh::lean_inc(v_value_968_);
        v_tail_969_ = crate::leanh::lean_ctor_get(v_x_960_, 2);
        crate::leanh::lean_inc(v_tail_969_);
        crate::leanh::lean_dec_ref_known(v_x_960_, 3);
        crate::leanh::lean_inc(v_f_958_);
        v___f_970_ = crate::leanh::lean_alloc_closure(
            l___private_Lean_Data_AssocList_0__Lean_AssocList_forIn_loop___redArg___lam__0
                as *mut core::ffi::c_void,
            5,
            4,
        );
        crate::leanh::lean_closure_set(v___f_970_, 0, v_toPure_966_);
        crate::leanh::lean_closure_set(v___f_970_, 1, v_inst_957_);
        crate::leanh::lean_closure_set(v___f_970_, 2, v_f_958_);
        crate::leanh::lean_closure_set(v___f_970_, 3, v_tail_969_);
        v___x_971_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_971_, 0, v_key_967_);
        crate::leanh::lean_ctor_set(v___x_971_, 1, v_value_968_);
        v___x_972_ = crate::leanh::lean_apply_2(v_f_958_, v___x_971_, v_x_959_);
        v___x_973_ = crate::leanh::lean_apply_4(
            v_toBind_965_,
            crate::leanh::lean_box(0),
            crate::leanh::lean_box(0),
            v___x_972_,
            v___f_970_,
        );
        return v___x_973_;
    }
}
pub unsafe fn l___private_Lean_Data_AssocList_0__Lean_AssocList_forIn_loop___redArg___lam__0(
    mut v_toPure_974_: *mut crate::leanh::LeanObject,
    mut v_inst_975_: *mut crate::leanh::LeanObject,
    mut v_f_976_: *mut crate::leanh::LeanObject,
    mut v_tail_977_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_978_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_____do__lift_978_) == 0 {
        let mut v_a_979_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_980_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_tail_977_);
        crate::leanh::lean_dec(v_f_976_);
        crate::leanh::lean_dec_ref(v_inst_975_);
        v_a_979_ = crate::leanh::lean_ctor_get(v_____do__lift_978_, 0);
        crate::leanh::lean_inc(v_a_979_);
        crate::leanh::lean_dec_ref_known(v_____do__lift_978_, 1);
        v___x_980_ = crate::leanh::lean_apply_2(v_toPure_974_, crate::leanh::lean_box(0), v_a_979_);
        return v___x_980_;
    } else {
        let mut v_a_981_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_982_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_toPure_974_);
        v_a_981_ = crate::leanh::lean_ctor_get(v_____do__lift_978_, 0);
        crate::leanh::lean_inc(v_a_981_);
        crate::leanh::lean_dec_ref_known(v_____do__lift_978_, 1);
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
    mut v_00_u03b1_983_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_984_: *mut crate::leanh::LeanObject,
    mut v_00_u03b4_985_: *mut crate::leanh::LeanObject,
    mut v_m_986_: *mut crate::leanh::LeanObject,
    mut v_inst_987_: *mut crate::leanh::LeanObject,
    mut v_f_988_: *mut crate::leanh::LeanObject,
    mut v_x_989_: *mut crate::leanh::LeanObject,
    mut v_x_990_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_991_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_991_ = l___private_Lean_Data_AssocList_0__Lean_AssocList_forIn_loop___redArg(
        v_inst_987_,
        v_f_988_,
        v_x_989_,
        v_x_990_,
    );
    return v___x_991_;
}
pub unsafe fn l_Lean_AssocList_forIn___redArg(
    mut v_inst_992_: *mut crate::leanh::LeanObject,
    mut v_as_993_: *mut crate::leanh::LeanObject,
    mut v_init_994_: *mut crate::leanh::LeanObject,
    mut v_f_995_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_996_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_996_ = l___private_Lean_Data_AssocList_0__Lean_AssocList_forIn_loop___redArg(
        v_inst_992_,
        v_f_995_,
        v_init_994_,
        v_as_993_,
    );
    return v___x_996_;
}
pub unsafe fn l_Lean_AssocList_forIn(
    mut v_00_u03b1_997_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_998_: *mut crate::leanh::LeanObject,
    mut v_00_u03b4_999_: *mut crate::leanh::LeanObject,
    mut v_m_1000_: *mut crate::leanh::LeanObject,
    mut v_inst_1001_: *mut crate::leanh::LeanObject,
    mut v_as_1002_: *mut crate::leanh::LeanObject,
    mut v_init_1003_: *mut crate::leanh::LeanObject,
    mut v_f_1004_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1005_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1005_ = l___private_Lean_Data_AssocList_0__Lean_AssocList_forIn_loop___redArg(
        v_inst_1001_,
        v_f_1004_,
        v_init_1003_,
        v_as_1002_,
    );
    return v___x_1005_;
}
pub unsafe fn l_Lean_AssocList_instForInProdOfMonad___redArg___lam__0(
    mut v_inst_1006_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_1007_: *mut crate::leanh::LeanObject,
    mut v___y_1008_: *mut crate::leanh::LeanObject,
    mut v___y_1009_: *mut crate::leanh::LeanObject,
    mut v___y_1010_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1011_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1011_ = l___private_Lean_Data_AssocList_0__Lean_AssocList_forIn_loop___redArg(
        v_inst_1006_,
        v___y_1010_,
        v___y_1009_,
        v___y_1008_,
    );
    return v___x_1011_;
}
pub unsafe fn l_Lean_AssocList_instForInProdOfMonad___redArg(
    mut v_inst_1012_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_1013_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_1013_ = crate::leanh::lean_alloc_closure(
        l_Lean_AssocList_instForInProdOfMonad___redArg___lam__0 as *mut core::ffi::c_void,
        5,
        1,
    );
    crate::leanh::lean_closure_set(v___f_1013_, 0, v_inst_1012_);
    return v___f_1013_;
}
pub unsafe fn l_Lean_AssocList_instForInProdOfMonad(
    mut v_00_u03b1_1014_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_1015_: *mut crate::leanh::LeanObject,
    mut v_m_1016_: *mut crate::leanh::LeanObject,
    mut v_inst_1017_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_1018_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_1018_ = crate::leanh::lean_alloc_closure(
        l_Lean_AssocList_instForInProdOfMonad___redArg___lam__0 as *mut core::ffi::c_void,
        5,
        1,
    );
    crate::leanh::lean_closure_set(v___f_1018_, 0, v_inst_1017_);
    return v___f_1018_;
}
pub unsafe fn l_List_toAssocList_x27___redArg(
    mut v_x_1019_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_1019_) == 0 {
        let mut v___x_1020_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_1020_ = crate::leanh::lean_box(0);
        return v___x_1020_;
    } else {
        let mut v_head_1021_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_tail_1022_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_fst_1023_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_snd_1024_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1025_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1026_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_head_1021_ = crate::leanh::lean_ctor_get(v_x_1019_, 0);
        v_tail_1022_ = crate::leanh::lean_ctor_get(v_x_1019_, 1);
        v_fst_1023_ = crate::leanh::lean_ctor_get(v_head_1021_, 0);
        v_snd_1024_ = crate::leanh::lean_ctor_get(v_head_1021_, 1);
        v___x_1025_ = l_List_toAssocList_x27___redArg(v_tail_1022_);
        crate::leanh::lean_inc(v_snd_1024_);
        crate::leanh::lean_inc(v_fst_1023_);
        v___x_1026_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_1026_, 0, v_fst_1023_);
        crate::leanh::lean_ctor_set(v___x_1026_, 1, v_snd_1024_);
        crate::leanh::lean_ctor_set(v___x_1026_, 2, v___x_1025_);
        return v___x_1026_;
    }
}
pub unsafe fn l_List_toAssocList_x27___redArg___boxed(
    mut v_x_1027_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1028_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1028_ = l_List_toAssocList_x27___redArg(v_x_1027_);
    crate::leanh::lean_dec(v_x_1027_);
    return v_res_1028_;
}
pub unsafe fn l_List_toAssocList_x27(
    mut v_00_u03b1_1029_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_1030_: *mut crate::leanh::LeanObject,
    mut v_x_1031_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1032_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1032_ = l_List_toAssocList_x27___redArg(v_x_1031_);
    return v___x_1032_;
}
pub unsafe fn l_List_toAssocList_x27___boxed(
    mut v_00_u03b1_1033_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_1034_: *mut crate::leanh::LeanObject,
    mut v_x_1035_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1036_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1036_ = l_List_toAssocList_x27(v_00_u03b1_1033_, v_00_u03b2_1034_, v_x_1035_);
    crate::leanh::lean_dec(v_x_1035_);
    return v_res_1036_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Data_AssocList(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Init_Data_List_Impl(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Data_AssocList(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_meta_initialized = true;
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lean_Data_AssocList(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Init_Data_List_Impl(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Data_AssocList(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_Data_AssocList(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Lean_Data_AssocList(builtin);
}
