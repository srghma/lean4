// Lean compiler output
// Module: Lake.Util.EquipT
// Imports: Init.Control.Except
use crate::r#gen::Init::Control::Except::{
    initialize_Init_Control_Except, runtime_initialize_Init_Control_Except,
};
use crate::r#gen::Init::Prelude::{l_Function_const___boxed, l_id___boxed};
pub static l_Lake_EquipT_instApplicative___redArg___lam__1___closed__0_value:
    leanh::LeanClosureObject<2> = leanh::LeanClosureObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut leanh::LeanObject>() * 2) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Function_const___boxed as *const core::ffi::c_void,
    m_arity: 4,
    m_num_fixed: 2,
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut leanh::LeanObject,
        (((0 as usize) << 1) | 1) as *mut leanh::LeanObject,
    ],
};
static mut l_Lake_EquipT_instApplicative___redArg___lam__1___closed__0:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_EquipT_instApplicative___redArg___lam__1___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lake_EquipT_instApplicative___redArg___lam__3___closed__0_value:
    leanh::LeanClosureObject<1> = leanh::LeanClosureObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_id___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 1,
    m_objs: [(((0 as usize) << 1) | 1) as *mut leanh::LeanObject],
};
static mut l_Lake_EquipT_instApplicative___redArg___lam__3___closed__0:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_EquipT_instApplicative___redArg___lam__3___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lake_EquipT_instApplicative___redArg___lam__3___closed__1_value:
    leanh::LeanClosureObject<3> = leanh::LeanClosureObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut leanh::LeanObject>() * 3) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Function_const___boxed as *const core::ffi::c_void,
    m_arity: 4,
    m_num_fixed: 3,
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut leanh::LeanObject,
        (((0 as usize) << 1) | 1) as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lake_EquipT_instApplicative___redArg___lam__3___closed__0_value)
            as *mut leanh::LeanObject,
    ],
};
static mut l_Lake_EquipT_instApplicative___redArg___lam__3___closed__1:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_EquipT_instApplicative___redArg___lam__3___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Lake_EquipT_instMonadLift___closed__0_value: leanh::LeanClosureObject<2> =
    leanh::LeanClosureObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut leanh::LeanObject>() * 2)
                as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Lake_EquipT_lift___boxed as *const core::ffi::c_void,
        m_arity: 5,
        m_num_fixed: 2,
        m_objs: [
            (((0 as usize) << 1) | 1) as *mut leanh::LeanObject,
            (((0 as usize) << 1) | 1) as *mut leanh::LeanObject,
        ],
    };
static mut l_Lake_EquipT_instMonadLift___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_EquipT_instMonadLift___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lake_EquipT_instMonadFunctor___closed__0_value: leanh::LeanClosureObject<0> =
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
        m_fun: l_Lake_EquipT_instMonadFunctor___lam__0 as *const core::ffi::c_void,
        m_arity: 4,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lake_EquipT_instMonadFunctor___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_EquipT_instMonadFunctor___closed__0_value)
        as *mut leanh::LeanObject;
pub unsafe fn l_Lake_EquipT_mk___redArg(
    mut v_x_522_: *mut leanh::LeanObject,
    mut v_a_523_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_524_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_524_ = leanh::lean_apply_1(v_x_522_, v_a_523_);
    return v___x_524_;
}
pub unsafe fn l_Lake_EquipT_mk(
    mut v_00_u03c1_525_: *mut leanh::LeanObject,
    mut v_m_526_: *mut leanh::LeanObject,
    mut v_00_u03b1_527_: *mut leanh::LeanObject,
    mut v_x_528_: *mut leanh::LeanObject,
    mut v_a_529_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_530_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_530_ = leanh::lean_apply_1(v_x_528_, v_a_529_);
    return v___x_530_;
}
pub unsafe fn l_Lake_EquipT_instInhabited___redArg___lam__0(
    mut v_inst_531_: *mut leanh::LeanObject,
    mut v_x_532_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    leanh::lean_inc(v_inst_531_);
    return v_inst_531_;
}
pub unsafe fn l_Lake_EquipT_instInhabited___redArg___lam__0___boxed(
    mut v_inst_533_: *mut leanh::LeanObject,
    mut v_x_534_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_535_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_535_ = l_Lake_EquipT_instInhabited___redArg___lam__0(v_inst_533_, v_x_534_);
    leanh::lean_dec(v_x_534_);
    leanh::lean_dec(v_inst_533_);
    return v_res_535_;
}
pub unsafe fn l_Lake_EquipT_instInhabited___redArg(
    mut v_inst_536_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_537_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_538_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_537_ = leanh::lean_alloc_closure(
        l_Lake_EquipT_instInhabited___redArg___lam__0___boxed as *mut core::ffi::c_void,
        2,
        1,
    );
    leanh::lean_closure_set(v___f_537_, 0, v_inst_536_);
    v___x_538_ = leanh::lean_alloc_closure(l_Lake_EquipT_mk as *mut core::ffi::c_void, 5, 4);
    leanh::lean_closure_set(v___x_538_, 0, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_538_, 1, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_538_, 2, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_538_, 3, v___f_537_);
    return v___x_538_;
}
pub unsafe fn l_Lake_EquipT_instInhabited(
    mut v_m_539_: *mut leanh::LeanObject,
    mut v_00_u03c1_540_: *mut leanh::LeanObject,
    mut v_00_u03b1_541_: *mut leanh::LeanObject,
    mut v_inst_542_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_543_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_543_ = l_Lake_EquipT_instInhabited___redArg(v_inst_542_);
    return v___x_543_;
}
pub unsafe fn l_Lake_EquipT_run___redArg(
    mut v_self_544_: *mut leanh::LeanObject,
    mut v_r_545_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_546_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_546_ = leanh::lean_apply_1(v_self_544_, v_r_545_);
    return v___x_546_;
}
pub unsafe fn l_Lake_EquipT_run(
    mut v_00_u03c1_547_: *mut leanh::LeanObject,
    mut v_m_548_: *mut leanh::LeanObject,
    mut v_00_u03b1_549_: *mut leanh::LeanObject,
    mut v_self_550_: *mut leanh::LeanObject,
    mut v_r_551_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_552_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_552_ = leanh::lean_apply_1(v_self_550_, v_r_551_);
    return v___x_552_;
}
pub unsafe fn l_Lake_EquipT_map___redArg(
    mut v_inst_553_: *mut leanh::LeanObject,
    mut v_f_554_: *mut leanh::LeanObject,
    mut v_self_555_: *mut leanh::LeanObject,
    mut v_r_556_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_map_557_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_558_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_559_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_map_557_ = leanh::lean_ctor_get(v_inst_553_, 0);
    leanh::lean_inc(v_map_557_);
    leanh::lean_dec_ref(v_inst_553_);
    v___x_558_ = leanh::lean_apply_1(v_self_555_, v_r_556_);
    v___x_559_ = leanh::lean_apply_4(
        v_map_557_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v_f_554_,
        v___x_558_,
    );
    return v___x_559_;
}
pub unsafe fn l_Lake_EquipT_map(
    mut v_m_560_: *mut leanh::LeanObject,
    mut v_00_u03b1_561_: *mut leanh::LeanObject,
    mut v_00_u03b2_562_: *mut leanh::LeanObject,
    mut v_00_u03c1_563_: *mut leanh::LeanObject,
    mut v_inst_564_: *mut leanh::LeanObject,
    mut v_f_565_: *mut leanh::LeanObject,
    mut v_self_566_: *mut leanh::LeanObject,
    mut v_r_567_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_map_568_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_569_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_570_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_map_568_ = leanh::lean_ctor_get(v_inst_564_, 0);
    leanh::lean_inc(v_map_568_);
    leanh::lean_dec_ref(v_inst_564_);
    v___x_569_ = leanh::lean_apply_1(v_self_566_, v_r_567_);
    v___x_570_ = leanh::lean_apply_4(
        v_map_568_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v_f_565_,
        v___x_569_,
    );
    return v___x_570_;
}
pub unsafe fn l_Lake_EquipT_instFunctor___redArg___lam__0(
    mut v_inst_571_: *mut leanh::LeanObject,
    mut v_00_u03b1_572_: *mut leanh::LeanObject,
    mut v_00_u03b2_573_: *mut leanh::LeanObject,
    mut v___y_574_: *mut leanh::LeanObject,
    mut v___y_575_: *mut leanh::LeanObject,
    mut v___y_576_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_map_577_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_578_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_579_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_map_577_ = leanh::lean_ctor_get(v_inst_571_, 0);
    leanh::lean_inc(v_map_577_);
    leanh::lean_dec_ref(v_inst_571_);
    v___x_578_ = leanh::lean_apply_1(v___y_575_, v___y_576_);
    v___x_579_ = leanh::lean_apply_4(
        v_map_577_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v___y_574_,
        v___x_578_,
    );
    return v___x_579_;
}
pub unsafe fn l_Lake_EquipT_instFunctor___redArg___lam__1(
    mut v___f_580_: *mut leanh::LeanObject,
    mut v_00_u03b1_581_: *mut leanh::LeanObject,
    mut v_00_u03b2_582_: *mut leanh::LeanObject,
    mut v___y_583_: *mut leanh::LeanObject,
    mut v___y_584_: *mut leanh::LeanObject,
    mut v___y_585_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_586_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_587_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_586_ =
        leanh::lean_alloc_closure(l_Function_const___boxed as *mut core::ffi::c_void, 4, 3);
    leanh::lean_closure_set(v___x_586_, 0, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_586_, 1, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_586_, 2, v___y_583_);
    v___x_587_ = leanh::lean_apply_5(
        v___f_580_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v___x_586_,
        v___y_584_,
        v___y_585_,
    );
    return v___x_587_;
}
pub unsafe fn l_Lake_EquipT_instFunctor___redArg(
    mut v_inst_588_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_589_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_590_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_591_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_589_ = leanh::lean_alloc_closure(
        l_Lake_EquipT_instFunctor___redArg___lam__0 as *mut core::ffi::c_void,
        6,
        1,
    );
    leanh::lean_closure_set(v___f_589_, 0, v_inst_588_);
    leanh::lean_inc_ref(v___f_589_);
    v___f_590_ = leanh::lean_alloc_closure(
        l_Lake_EquipT_instFunctor___redArg___lam__1 as *mut core::ffi::c_void,
        6,
        1,
    );
    leanh::lean_closure_set(v___f_590_, 0, v___f_589_);
    v___x_591_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_591_, 0, v___f_589_);
    leanh::lean_ctor_set(v___x_591_, 1, v___f_590_);
    return v___x_591_;
}
pub unsafe fn l_Lake_EquipT_instFunctor(
    mut v_m_592_: *mut leanh::LeanObject,
    mut v_00_u03c1_593_: *mut leanh::LeanObject,
    mut v_inst_594_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_595_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_595_ = l_Lake_EquipT_instFunctor___redArg(v_inst_594_);
    return v___x_595_;
}
pub unsafe fn l_Lake_EquipT_pure___redArg(
    mut v_inst_596_: *mut leanh::LeanObject,
    mut v_a_597_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_598_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_598_ = leanh::lean_apply_2(v_inst_596_, leanh::lean_box(0), v_a_597_);
    return v___x_598_;
}
pub unsafe fn l_Lake_EquipT_pure(
    mut v_m_599_: *mut leanh::LeanObject,
    mut v_00_u03b1_600_: *mut leanh::LeanObject,
    mut v_00_u03c1_601_: *mut leanh::LeanObject,
    mut v_inst_602_: *mut leanh::LeanObject,
    mut v_a_603_: *mut leanh::LeanObject,
    mut v_x_604_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_605_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_605_ = leanh::lean_apply_2(v_inst_602_, leanh::lean_box(0), v_a_603_);
    return v___x_605_;
}
pub unsafe fn l_Lake_EquipT_pure___boxed(
    mut v_m_606_: *mut leanh::LeanObject,
    mut v_00_u03b1_607_: *mut leanh::LeanObject,
    mut v_00_u03c1_608_: *mut leanh::LeanObject,
    mut v_inst_609_: *mut leanh::LeanObject,
    mut v_a_610_: *mut leanh::LeanObject,
    mut v_x_611_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_612_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_612_ = l_Lake_EquipT_pure(
        v_m_606_,
        v_00_u03b1_607_,
        v_00_u03c1_608_,
        v_inst_609_,
        v_a_610_,
        v_x_611_,
    );
    leanh::lean_dec(v_x_611_);
    return v_res_612_;
}
pub unsafe fn l_Lake_EquipT_instPure___redArg___lam__0(
    mut v_inst_613_: *mut leanh::LeanObject,
    mut v_00_u03b1_614_: *mut leanh::LeanObject,
    mut v___y_615_: *mut leanh::LeanObject,
    mut v___y_616_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_617_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_617_ = leanh::lean_apply_2(v_inst_613_, leanh::lean_box(0), v___y_615_);
    return v___x_617_;
}
pub unsafe fn l_Lake_EquipT_instPure___redArg___lam__0___boxed(
    mut v_inst_618_: *mut leanh::LeanObject,
    mut v_00_u03b1_619_: *mut leanh::LeanObject,
    mut v___y_620_: *mut leanh::LeanObject,
    mut v___y_621_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_622_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_622_ = l_Lake_EquipT_instPure___redArg___lam__0(
        v_inst_618_,
        v_00_u03b1_619_,
        v___y_620_,
        v___y_621_,
    );
    leanh::lean_dec(v___y_621_);
    return v_res_622_;
}
pub unsafe fn l_Lake_EquipT_instPure___redArg(
    mut v_inst_623_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_624_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_624_ = leanh::lean_alloc_closure(
        l_Lake_EquipT_instPure___redArg___lam__0___boxed as *mut core::ffi::c_void,
        4,
        1,
    );
    leanh::lean_closure_set(v___f_624_, 0, v_inst_623_);
    return v___f_624_;
}
pub unsafe fn l_Lake_EquipT_instPure(
    mut v_m_625_: *mut leanh::LeanObject,
    mut v_00_u03c1_626_: *mut leanh::LeanObject,
    mut v_inst_627_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_628_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_628_ = leanh::lean_alloc_closure(
        l_Lake_EquipT_instPure___redArg___lam__0___boxed as *mut core::ffi::c_void,
        4,
        1,
    );
    leanh::lean_closure_set(v___f_628_, 0, v_inst_627_);
    return v___f_628_;
}
pub unsafe fn l_Lake_EquipT_compose___redArg___lam__0(
    mut v_x_u2082_629_: *mut leanh::LeanObject,
    mut v_r_630_: *mut leanh::LeanObject,
    mut v_x_631_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_632_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_633_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_632_ = leanh::lean_box(0);
    v___x_633_ = leanh::lean_apply_2(v_x_u2082_629_, v___x_632_, v_r_630_);
    return v___x_633_;
}
pub unsafe fn l_Lake_EquipT_compose___redArg(
    mut v_f_634_: *mut leanh::LeanObject,
    mut v_x_u2081_635_: *mut leanh::LeanObject,
    mut v_x_u2082_636_: *mut leanh::LeanObject,
    mut v_r_637_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_638_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_639_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_640_: *mut leanh::LeanObject = core::ptr::null_mut();
    leanh::lean_inc(v_r_637_);
    v___f_638_ = leanh::lean_alloc_closure(
        l_Lake_EquipT_compose___redArg___lam__0 as *mut core::ffi::c_void,
        3,
        2,
    );
    leanh::lean_closure_set(v___f_638_, 0, v_x_u2082_636_);
    leanh::lean_closure_set(v___f_638_, 1, v_r_637_);
    v___x_639_ = leanh::lean_apply_1(v_x_u2081_635_, v_r_637_);
    v___x_640_ = leanh::lean_apply_2(v_f_634_, v___x_639_, v___f_638_);
    return v___x_640_;
}
pub unsafe fn l_Lake_EquipT_compose(
    mut v_m_641_: *mut leanh::LeanObject,
    mut v_00_u03c1_642_: *mut leanh::LeanObject,
    mut v_00_u03b1_u2081_643_: *mut leanh::LeanObject,
    mut v_00_u03b1_u2082_644_: *mut leanh::LeanObject,
    mut v_00_u03b2_645_: *mut leanh::LeanObject,
    mut v_f_646_: *mut leanh::LeanObject,
    mut v_x_u2081_647_: *mut leanh::LeanObject,
    mut v_x_u2082_648_: *mut leanh::LeanObject,
    mut v_r_649_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_650_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_651_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_652_: *mut leanh::LeanObject = core::ptr::null_mut();
    leanh::lean_inc(v_r_649_);
    v___f_650_ = leanh::lean_alloc_closure(
        l_Lake_EquipT_compose___redArg___lam__0 as *mut core::ffi::c_void,
        3,
        2,
    );
    leanh::lean_closure_set(v___f_650_, 0, v_x_u2082_648_);
    leanh::lean_closure_set(v___f_650_, 1, v_r_649_);
    v___x_651_ = leanh::lean_apply_1(v_x_u2081_647_, v_r_649_);
    v___x_652_ = leanh::lean_apply_2(v_f_646_, v___x_651_, v___f_650_);
    return v___x_652_;
}
pub unsafe fn l_Lake_EquipT_seq___redArg___lam__0(
    mut v_x_u2082_653_: *mut leanh::LeanObject,
    mut v_a_654_: *mut leanh::LeanObject,
    mut v_x_655_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_656_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_657_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_656_ = leanh::lean_box(0);
    v___x_657_ = leanh::lean_apply_2(v_x_u2082_653_, v___x_656_, v_a_654_);
    return v___x_657_;
}
pub unsafe fn l_Lake_EquipT_seq___redArg(
    mut v_inst_658_: *mut leanh::LeanObject,
    mut v_x_u2081_659_: *mut leanh::LeanObject,
    mut v_x_u2082_660_: *mut leanh::LeanObject,
    mut v_a_661_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_662_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_663_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_664_: *mut leanh::LeanObject = core::ptr::null_mut();
    leanh::lean_inc(v_a_661_);
    v___f_662_ = leanh::lean_alloc_closure(
        l_Lake_EquipT_seq___redArg___lam__0 as *mut core::ffi::c_void,
        3,
        2,
    );
    leanh::lean_closure_set(v___f_662_, 0, v_x_u2082_660_);
    leanh::lean_closure_set(v___f_662_, 1, v_a_661_);
    v___x_663_ = leanh::lean_apply_1(v_x_u2081_659_, v_a_661_);
    v___x_664_ = leanh::lean_apply_4(
        v_inst_658_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v___x_663_,
        v___f_662_,
    );
    return v___x_664_;
}
pub unsafe fn l_Lake_EquipT_seq(
    mut v_m_665_: *mut leanh::LeanObject,
    mut v_00_u03c1_666_: *mut leanh::LeanObject,
    mut v_00_u03b1_667_: *mut leanh::LeanObject,
    mut v_00_u03b2_668_: *mut leanh::LeanObject,
    mut v_inst_669_: *mut leanh::LeanObject,
    mut v_x_u2081_670_: *mut leanh::LeanObject,
    mut v_x_u2082_671_: *mut leanh::LeanObject,
    mut v_a_672_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_673_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_674_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_675_: *mut leanh::LeanObject = core::ptr::null_mut();
    leanh::lean_inc(v_a_672_);
    v___f_673_ = leanh::lean_alloc_closure(
        l_Lake_EquipT_seq___redArg___lam__0 as *mut core::ffi::c_void,
        3,
        2,
    );
    leanh::lean_closure_set(v___f_673_, 0, v_x_u2082_671_);
    leanh::lean_closure_set(v___f_673_, 1, v_a_672_);
    v___x_674_ = leanh::lean_apply_1(v_x_u2081_670_, v_a_672_);
    v___x_675_ = leanh::lean_apply_4(
        v_inst_669_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v___x_674_,
        v___f_673_,
    );
    return v___x_675_;
}
pub unsafe fn l_Lake_EquipT_instSeq___redArg___lam__0(
    mut v___y_676_: *mut leanh::LeanObject,
    mut v___y_677_: *mut leanh::LeanObject,
    mut v_x_678_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_679_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_680_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_679_ = leanh::lean_box(0);
    v___x_680_ = leanh::lean_apply_2(v___y_676_, v___x_679_, v___y_677_);
    return v___x_680_;
}
pub unsafe fn l_Lake_EquipT_instSeq___redArg___lam__1(
    mut v_inst_681_: *mut leanh::LeanObject,
    mut v_00_u03b1_682_: *mut leanh::LeanObject,
    mut v_00_u03b2_683_: *mut leanh::LeanObject,
    mut v___y_684_: *mut leanh::LeanObject,
    mut v___y_685_: *mut leanh::LeanObject,
    mut v___y_686_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_687_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_688_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_689_: *mut leanh::LeanObject = core::ptr::null_mut();
    leanh::lean_inc(v___y_686_);
    v___f_687_ = leanh::lean_alloc_closure(
        l_Lake_EquipT_instSeq___redArg___lam__0 as *mut core::ffi::c_void,
        3,
        2,
    );
    leanh::lean_closure_set(v___f_687_, 0, v___y_685_);
    leanh::lean_closure_set(v___f_687_, 1, v___y_686_);
    v___x_688_ = leanh::lean_apply_1(v___y_684_, v___y_686_);
    v___x_689_ = leanh::lean_apply_4(
        v_inst_681_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v___x_688_,
        v___f_687_,
    );
    return v___x_689_;
}
pub unsafe fn l_Lake_EquipT_instSeq___redArg(
    mut v_inst_690_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_691_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_691_ = leanh::lean_alloc_closure(
        l_Lake_EquipT_instSeq___redArg___lam__1 as *mut core::ffi::c_void,
        6,
        1,
    );
    leanh::lean_closure_set(v___f_691_, 0, v_inst_690_);
    return v___f_691_;
}
pub unsafe fn l_Lake_EquipT_instSeq(
    mut v_m_692_: *mut leanh::LeanObject,
    mut v_00_u03c1_693_: *mut leanh::LeanObject,
    mut v_inst_694_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_695_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_695_ = leanh::lean_alloc_closure(
        l_Lake_EquipT_instSeq___redArg___lam__1 as *mut core::ffi::c_void,
        6,
        1,
    );
    leanh::lean_closure_set(v___f_695_, 0, v_inst_694_);
    return v___f_695_;
}
pub unsafe fn l_Lake_EquipT_instApplicative___redArg___lam__0(
    mut v_b_696_: *mut leanh::LeanObject,
    mut v___y_697_: *mut leanh::LeanObject,
    mut v_x_698_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_699_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_700_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_699_ = leanh::lean_box(0);
    v___x_700_ = leanh::lean_apply_2(v_b_696_, v___x_699_, v___y_697_);
    return v___x_700_;
}
pub unsafe fn l_Lake_EquipT_instApplicative___redArg___lam__1(
    mut v_toFunctor_702_: *mut leanh::LeanObject,
    mut v_toSeq_703_: *mut leanh::LeanObject,
    mut v_00_u03b1_704_: *mut leanh::LeanObject,
    mut v_00_u03b2_705_: *mut leanh::LeanObject,
    mut v_a_706_: *mut leanh::LeanObject,
    mut v_b_707_: *mut leanh::LeanObject,
    mut v___y_708_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_map_709_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_710_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_711_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_712_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_713_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_714_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_map_709_ = leanh::lean_ctor_get(v_toFunctor_702_, 0);
    leanh::lean_inc(v_map_709_);
    leanh::lean_dec_ref(v_toFunctor_702_);
    leanh::lean_inc(v___y_708_);
    v___f_710_ = leanh::lean_alloc_closure(
        l_Lake_EquipT_instApplicative___redArg___lam__0 as *mut core::ffi::c_void,
        3,
        2,
    );
    leanh::lean_closure_set(v___f_710_, 0, v_b_707_);
    leanh::lean_closure_set(v___f_710_, 1, v___y_708_);
    v___x_711_ = l_Lake_EquipT_instApplicative___redArg___lam__1___closed__0;
    v___x_712_ = leanh::lean_apply_1(v_a_706_, v___y_708_);
    v___x_713_ = leanh::lean_apply_4(
        v_map_709_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v___x_711_,
        v___x_712_,
    );
    v___x_714_ = leanh::lean_apply_4(
        v_toSeq_703_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v___x_713_,
        v___f_710_,
    );
    return v___x_714_;
}
pub unsafe fn l_Lake_EquipT_instApplicative___redArg___lam__3(
    mut v_toFunctor_718_: *mut leanh::LeanObject,
    mut v_toSeq_719_: *mut leanh::LeanObject,
    mut v_00_u03b1_720_: *mut leanh::LeanObject,
    mut v_00_u03b2_721_: *mut leanh::LeanObject,
    mut v_a_722_: *mut leanh::LeanObject,
    mut v_b_723_: *mut leanh::LeanObject,
    mut v___y_724_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_map_725_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_726_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_727_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_728_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_729_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_730_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_map_725_ = leanh::lean_ctor_get(v_toFunctor_718_, 0);
    leanh::lean_inc(v_map_725_);
    leanh::lean_dec_ref(v_toFunctor_718_);
    leanh::lean_inc(v___y_724_);
    v___f_726_ = leanh::lean_alloc_closure(
        l_Lake_EquipT_instApplicative___redArg___lam__0 as *mut core::ffi::c_void,
        3,
        2,
    );
    leanh::lean_closure_set(v___f_726_, 0, v_b_723_);
    leanh::lean_closure_set(v___f_726_, 1, v___y_724_);
    v___x_727_ = l_Lake_EquipT_instApplicative___redArg___lam__3___closed__1;
    v___x_728_ = leanh::lean_apply_1(v_a_722_, v___y_724_);
    v___x_729_ = leanh::lean_apply_4(
        v_map_725_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v___x_727_,
        v___x_728_,
    );
    v___x_730_ = leanh::lean_apply_4(
        v_toSeq_719_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v___x_729_,
        v___f_726_,
    );
    return v___x_730_;
}
pub unsafe fn l_Lake_EquipT_instApplicative___redArg(
    mut v_inst_731_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_toFunctor_732_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_733_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeq_734_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_736_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_737_: u8 = 0;
    let mut v___f_738_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_739_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_740_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_741_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_742_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_744_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_745_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_746_: u8 = 0;
    let mut v_unused_747_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_748_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_toFunctor_732_ = leanh::lean_ctor_get(v_inst_731_, 0);
                v_toPure_733_ = leanh::lean_ctor_get(v_inst_731_, 1);
                v_toSeq_734_ = leanh::lean_ctor_get(v_inst_731_, 2);
                v_isSharedCheck_746_ = (!leanh::lean_is_exclusive(v_inst_731_)) as u8;
                if v_isSharedCheck_746_ == 0 {
                    v_unused_747_ = leanh::lean_ctor_get(v_inst_731_, 4);
                    leanh::lean_dec(v_unused_747_);
                    v_unused_748_ = leanh::lean_ctor_get(v_inst_731_, 3);
                    leanh::lean_dec(v_unused_748_);
                    v___x_736_ = v_inst_731_;
                    v_isShared_737_ = v_isSharedCheck_746_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_toSeq_734_);
                    leanh::lean_inc(v_toPure_733_);
                    leanh::lean_inc(v_toFunctor_732_);
                    leanh::lean_dec(v_inst_731_);
                    v___x_736_ = leanh::lean_box(0);
                    v_isShared_737_ = v_isSharedCheck_746_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                leanh::lean_inc_n(v_toSeq_734_, 2);
                leanh::lean_inc_ref_n(v_toFunctor_732_, 2);
                v___f_738_ = leanh::lean_alloc_closure(
                    l_Lake_EquipT_instApplicative___redArg___lam__1 as *mut core::ffi::c_void,
                    7,
                    2,
                );
                leanh::lean_closure_set(v___f_738_, 0, v_toFunctor_732_);
                leanh::lean_closure_set(v___f_738_, 1, v_toSeq_734_);
                v___f_739_ = leanh::lean_alloc_closure(
                    l_Lake_EquipT_instApplicative___redArg___lam__3 as *mut core::ffi::c_void,
                    7,
                    2,
                );
                leanh::lean_closure_set(v___f_739_, 0, v_toFunctor_732_);
                leanh::lean_closure_set(v___f_739_, 1, v_toSeq_734_);
                v___x_740_ = l_Lake_EquipT_instFunctor___redArg(v_toFunctor_732_);
                v___f_741_ = leanh::lean_alloc_closure(
                    l_Lake_EquipT_instPure___redArg___lam__0___boxed as *mut core::ffi::c_void,
                    4,
                    1,
                );
                leanh::lean_closure_set(v___f_741_, 0, v_toPure_733_);
                v___f_742_ = leanh::lean_alloc_closure(
                    l_Lake_EquipT_instSeq___redArg___lam__1 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                leanh::lean_closure_set(v___f_742_, 0, v_toSeq_734_);
                if v_isShared_737_ == 0 {
                    leanh::lean_ctor_set(v___x_736_, 4, v___f_739_);
                    leanh::lean_ctor_set(v___x_736_, 3, v___f_738_);
                    leanh::lean_ctor_set(v___x_736_, 2, v___f_742_);
                    leanh::lean_ctor_set(v___x_736_, 1, v___f_741_);
                    leanh::lean_ctor_set(v___x_736_, 0, v___x_740_);
                    v___x_744_ = v___x_736_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_745_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_745_, 0, v___x_740_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_745_, 1, v___f_741_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_745_, 2, v___f_742_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_745_, 3, v___f_738_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_745_, 4, v___f_739_);
                    v___x_744_ = v_reuseFailAlloc_745_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_744_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lake_EquipT_instApplicative(
    mut v_m_749_: *mut leanh::LeanObject,
    mut v_00_u03c1_750_: *mut leanh::LeanObject,
    mut v_inst_751_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_752_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_752_ = l_Lake_EquipT_instApplicative___redArg(v_inst_751_);
    return v___x_752_;
}
pub unsafe fn l_Lake_EquipT_bind___redArg___lam__0(
    mut v_f_753_: *mut leanh::LeanObject,
    mut v_r_754_: *mut leanh::LeanObject,
    mut v_a_755_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_756_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_756_ = leanh::lean_apply_2(v_f_753_, v_a_755_, v_r_754_);
    return v___x_756_;
}
pub unsafe fn l_Lake_EquipT_bind___redArg(
    mut v_inst_757_: *mut leanh::LeanObject,
    mut v_self_758_: *mut leanh::LeanObject,
    mut v_f_759_: *mut leanh::LeanObject,
    mut v_r_760_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_761_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_762_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_763_: *mut leanh::LeanObject = core::ptr::null_mut();
    leanh::lean_inc(v_r_760_);
    v___f_761_ = leanh::lean_alloc_closure(
        l_Lake_EquipT_bind___redArg___lam__0 as *mut core::ffi::c_void,
        3,
        2,
    );
    leanh::lean_closure_set(v___f_761_, 0, v_f_759_);
    leanh::lean_closure_set(v___f_761_, 1, v_r_760_);
    v___x_762_ = leanh::lean_apply_1(v_self_758_, v_r_760_);
    v___x_763_ = leanh::lean_apply_4(
        v_inst_757_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v___x_762_,
        v___f_761_,
    );
    return v___x_763_;
}
pub unsafe fn l_Lake_EquipT_bind(
    mut v_m_764_: *mut leanh::LeanObject,
    mut v_00_u03c1_765_: *mut leanh::LeanObject,
    mut v_00_u03b1_766_: *mut leanh::LeanObject,
    mut v_00_u03b2_767_: *mut leanh::LeanObject,
    mut v_inst_768_: *mut leanh::LeanObject,
    mut v_self_769_: *mut leanh::LeanObject,
    mut v_f_770_: *mut leanh::LeanObject,
    mut v_r_771_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_772_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_773_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_774_: *mut leanh::LeanObject = core::ptr::null_mut();
    leanh::lean_inc(v_r_771_);
    v___f_772_ = leanh::lean_alloc_closure(
        l_Lake_EquipT_bind___redArg___lam__0 as *mut core::ffi::c_void,
        3,
        2,
    );
    leanh::lean_closure_set(v___f_772_, 0, v_f_770_);
    leanh::lean_closure_set(v___f_772_, 1, v_r_771_);
    v___x_773_ = leanh::lean_apply_1(v_self_769_, v_r_771_);
    v___x_774_ = leanh::lean_apply_4(
        v_inst_768_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v___x_773_,
        v___f_772_,
    );
    return v___x_774_;
}
pub unsafe fn l_Lake_EquipT_instBind___redArg___lam__0(
    mut v___y_775_: *mut leanh::LeanObject,
    mut v___y_776_: *mut leanh::LeanObject,
    mut v_a_777_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_778_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_778_ = leanh::lean_apply_2(v___y_775_, v_a_777_, v___y_776_);
    return v___x_778_;
}
pub unsafe fn l_Lake_EquipT_instBind___redArg___lam__1(
    mut v_inst_779_: *mut leanh::LeanObject,
    mut v_00_u03b1_780_: *mut leanh::LeanObject,
    mut v_00_u03b2_781_: *mut leanh::LeanObject,
    mut v___y_782_: *mut leanh::LeanObject,
    mut v___y_783_: *mut leanh::LeanObject,
    mut v___y_784_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_785_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_786_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_787_: *mut leanh::LeanObject = core::ptr::null_mut();
    leanh::lean_inc(v___y_784_);
    v___f_785_ = leanh::lean_alloc_closure(
        l_Lake_EquipT_instBind___redArg___lam__0 as *mut core::ffi::c_void,
        3,
        2,
    );
    leanh::lean_closure_set(v___f_785_, 0, v___y_783_);
    leanh::lean_closure_set(v___f_785_, 1, v___y_784_);
    v___x_786_ = leanh::lean_apply_1(v___y_782_, v___y_784_);
    v___x_787_ = leanh::lean_apply_4(
        v_inst_779_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v___x_786_,
        v___f_785_,
    );
    return v___x_787_;
}
pub unsafe fn l_Lake_EquipT_instBind___redArg(
    mut v_inst_788_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_789_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_789_ = leanh::lean_alloc_closure(
        l_Lake_EquipT_instBind___redArg___lam__1 as *mut core::ffi::c_void,
        6,
        1,
    );
    leanh::lean_closure_set(v___f_789_, 0, v_inst_788_);
    return v___f_789_;
}
pub unsafe fn l_Lake_EquipT_instBind(
    mut v_m_790_: *mut leanh::LeanObject,
    mut v_00_u03c1_791_: *mut leanh::LeanObject,
    mut v_inst_792_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_793_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_793_ = leanh::lean_alloc_closure(
        l_Lake_EquipT_instBind___redArg___lam__1 as *mut core::ffi::c_void,
        6,
        1,
    );
    leanh::lean_closure_set(v___f_793_, 0, v_inst_792_);
    return v___f_793_;
}
pub unsafe fn l_Lake_EquipT_instMonad___redArg(
    mut v_inst_794_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_toApplicative_795_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_796_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_798_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_799_: u8 = 0;
    let mut v___x_800_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_801_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_803_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_804_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_805_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_toApplicative_795_ = leanh::lean_ctor_get(v_inst_794_, 0);
                v_toBind_796_ = leanh::lean_ctor_get(v_inst_794_, 1);
                v_isSharedCheck_805_ = (!leanh::lean_is_exclusive(v_inst_794_)) as u8;
                if v_isSharedCheck_805_ == 0 {
                    v___x_798_ = v_inst_794_;
                    v_isShared_799_ = v_isSharedCheck_805_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_toBind_796_);
                    leanh::lean_inc(v_toApplicative_795_);
                    leanh::lean_dec(v_inst_794_);
                    v___x_798_ = leanh::lean_box(0);
                    v_isShared_799_ = v_isSharedCheck_805_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_800_ = l_Lake_EquipT_instApplicative___redArg(v_toApplicative_795_);
                v___f_801_ = leanh::lean_alloc_closure(
                    l_Lake_EquipT_instBind___redArg___lam__1 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                leanh::lean_closure_set(v___f_801_, 0, v_toBind_796_);
                if v_isShared_799_ == 0 {
                    leanh::lean_ctor_set(v___x_798_, 1, v___f_801_);
                    leanh::lean_ctor_set(v___x_798_, 0, v___x_800_);
                    v___x_803_ = v___x_798_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_804_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_804_, 0, v___x_800_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_804_, 1, v___f_801_);
                    v___x_803_ = v_reuseFailAlloc_804_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_803_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lake_EquipT_instMonad(
    mut v_m_806_: *mut leanh::LeanObject,
    mut v_00_u03c1_807_: *mut leanh::LeanObject,
    mut v_inst_808_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_809_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_809_ = l_Lake_EquipT_instMonad___redArg(v_inst_808_);
    return v___x_809_;
}
pub unsafe fn l_Lake_EquipT_lift___redArg(
    mut v_t_810_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    leanh::lean_inc(v_t_810_);
    return v_t_810_;
}
pub unsafe fn l_Lake_EquipT_lift___redArg___boxed(
    mut v_t_811_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_812_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_812_ = l_Lake_EquipT_lift___redArg(v_t_811_);
    leanh::lean_dec(v_t_811_);
    return v_res_812_;
}
pub unsafe fn l_Lake_EquipT_lift(
    mut v_m_813_: *mut leanh::LeanObject,
    mut v_00_u03c1_814_: *mut leanh::LeanObject,
    mut v_00_u03b1_815_: *mut leanh::LeanObject,
    mut v_t_816_: *mut leanh::LeanObject,
    mut v_x_817_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    leanh::lean_inc(v_t_816_);
    return v_t_816_;
}
pub unsafe fn l_Lake_EquipT_lift___boxed(
    mut v_m_818_: *mut leanh::LeanObject,
    mut v_00_u03c1_819_: *mut leanh::LeanObject,
    mut v_00_u03b1_820_: *mut leanh::LeanObject,
    mut v_t_821_: *mut leanh::LeanObject,
    mut v_x_822_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_823_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_823_ = l_Lake_EquipT_lift(
        v_m_818_,
        v_00_u03c1_819_,
        v_00_u03b1_820_,
        v_t_821_,
        v_x_822_,
    );
    leanh::lean_dec(v_x_822_);
    leanh::lean_dec(v_t_821_);
    return v_res_823_;
}
pub unsafe fn l_Lake_EquipT_instMonadLift(
    mut v_m_825_: *mut leanh::LeanObject,
    mut v_00_u03c1_826_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_827_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_827_ = l_Lake_EquipT_instMonadLift___closed__0;
    return v___x_827_;
}
pub unsafe fn l_Lake_EquipT_instMonadFunctor___lam__0(
    mut v_00_u03b1_828_: *mut leanh::LeanObject,
    mut v_f_829_: *mut leanh::LeanObject,
    mut v_x_830_: *mut leanh::LeanObject,
    mut v___y_831_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_832_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_833_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_832_ = leanh::lean_apply_1(v_x_830_, v___y_831_);
    v___x_833_ = leanh::lean_apply_2(v_f_829_, leanh::lean_box(0), v___x_832_);
    return v___x_833_;
}
pub unsafe fn l_Lake_EquipT_instMonadFunctor(
    mut v_m_835_: *mut leanh::LeanObject,
    mut v_00_u03c1_836_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_837_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_837_ = l_Lake_EquipT_instMonadFunctor___closed__0;
    return v___f_837_;
}
pub unsafe fn l_Lake_EquipT_failure___redArg(
    mut v_inst_838_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_failure_839_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_840_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_failure_839_ = leanh::lean_ctor_get(v_inst_838_, 1);
    leanh::lean_inc(v_failure_839_);
    leanh::lean_dec_ref(v_inst_838_);
    v___x_840_ = leanh::lean_apply_1(v_failure_839_, leanh::lean_box(0));
    return v___x_840_;
}
pub unsafe fn l_Lake_EquipT_failure(
    mut v_m_841_: *mut leanh::LeanObject,
    mut v_00_u03c1_842_: *mut leanh::LeanObject,
    mut v_00_u03b1_843_: *mut leanh::LeanObject,
    mut v_inst_844_: *mut leanh::LeanObject,
    mut v_x_845_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_failure_846_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_847_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_failure_846_ = leanh::lean_ctor_get(v_inst_844_, 1);
    leanh::lean_inc(v_failure_846_);
    leanh::lean_dec_ref(v_inst_844_);
    v___x_847_ = leanh::lean_apply_1(v_failure_846_, leanh::lean_box(0));
    return v___x_847_;
}
pub unsafe fn l_Lake_EquipT_failure___boxed(
    mut v_m_848_: *mut leanh::LeanObject,
    mut v_00_u03c1_849_: *mut leanh::LeanObject,
    mut v_00_u03b1_850_: *mut leanh::LeanObject,
    mut v_inst_851_: *mut leanh::LeanObject,
    mut v_x_852_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_853_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_853_ = l_Lake_EquipT_failure(
        v_m_848_,
        v_00_u03c1_849_,
        v_00_u03b1_850_,
        v_inst_851_,
        v_x_852_,
    );
    leanh::lean_dec(v_x_852_);
    return v_res_853_;
}
pub unsafe fn l_Lake_EquipT_orElse___redArg(
    mut v_inst_854_: *mut leanh::LeanObject,
    mut v_x_u2081_855_: *mut leanh::LeanObject,
    mut v_x_u2082_856_: *mut leanh::LeanObject,
    mut v_a_857_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_orElse_858_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_859_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_860_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_861_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_orElse_858_ = leanh::lean_ctor_get(v_inst_854_, 2);
    leanh::lean_inc(v_orElse_858_);
    leanh::lean_dec_ref(v_inst_854_);
    leanh::lean_inc(v_a_857_);
    v___f_859_ = leanh::lean_alloc_closure(
        l_Lake_EquipT_seq___redArg___lam__0 as *mut core::ffi::c_void,
        3,
        2,
    );
    leanh::lean_closure_set(v___f_859_, 0, v_x_u2082_856_);
    leanh::lean_closure_set(v___f_859_, 1, v_a_857_);
    v___x_860_ = leanh::lean_apply_1(v_x_u2081_855_, v_a_857_);
    v___x_861_ = leanh::lean_apply_3(
        v_orElse_858_,
        leanh::lean_box(0),
        v___x_860_,
        v___f_859_,
    );
    return v___x_861_;
}
pub unsafe fn l_Lake_EquipT_orElse(
    mut v_m_862_: *mut leanh::LeanObject,
    mut v_00_u03c1_863_: *mut leanh::LeanObject,
    mut v_00_u03b1_864_: *mut leanh::LeanObject,
    mut v_inst_865_: *mut leanh::LeanObject,
    mut v_x_u2081_866_: *mut leanh::LeanObject,
    mut v_x_u2082_867_: *mut leanh::LeanObject,
    mut v_a_868_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_orElse_869_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_870_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_871_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_872_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_orElse_869_ = leanh::lean_ctor_get(v_inst_865_, 2);
    leanh::lean_inc(v_orElse_869_);
    leanh::lean_dec_ref(v_inst_865_);
    leanh::lean_inc(v_a_868_);
    v___f_870_ = leanh::lean_alloc_closure(
        l_Lake_EquipT_seq___redArg___lam__0 as *mut core::ffi::c_void,
        3,
        2,
    );
    leanh::lean_closure_set(v___f_870_, 0, v_x_u2082_867_);
    leanh::lean_closure_set(v___f_870_, 1, v_a_868_);
    v___x_871_ = leanh::lean_apply_1(v_x_u2081_866_, v_a_868_);
    v___x_872_ = leanh::lean_apply_3(
        v_orElse_869_,
        leanh::lean_box(0),
        v___x_871_,
        v___f_870_,
    );
    return v___x_872_;
}
pub unsafe fn l_Lake_EquipT_instAlternative___redArg___lam__0(
    mut v_failure_873_: *mut leanh::LeanObject,
    mut v_00_u03b1_874_: *mut leanh::LeanObject,
    mut v___y_875_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_876_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_876_ = leanh::lean_apply_1(v_failure_873_, leanh::lean_box(0));
    return v___x_876_;
}
pub unsafe fn l_Lake_EquipT_instAlternative___redArg___lam__0___boxed(
    mut v_failure_877_: *mut leanh::LeanObject,
    mut v_00_u03b1_878_: *mut leanh::LeanObject,
    mut v___y_879_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_880_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_880_ = l_Lake_EquipT_instAlternative___redArg___lam__0(
        v_failure_877_,
        v_00_u03b1_878_,
        v___y_879_,
    );
    leanh::lean_dec(v___y_879_);
    return v_res_880_;
}
pub unsafe fn l_Lake_EquipT_instAlternative___redArg___lam__2(
    mut v_orElse_881_: *mut leanh::LeanObject,
    mut v_00_u03b1_882_: *mut leanh::LeanObject,
    mut v___y_883_: *mut leanh::LeanObject,
    mut v___y_884_: *mut leanh::LeanObject,
    mut v___y_885_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_886_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_887_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_888_: *mut leanh::LeanObject = core::ptr::null_mut();
    leanh::lean_inc(v___y_885_);
    v___f_886_ = leanh::lean_alloc_closure(
        l_Lake_EquipT_instSeq___redArg___lam__0 as *mut core::ffi::c_void,
        3,
        2,
    );
    leanh::lean_closure_set(v___f_886_, 0, v___y_884_);
    leanh::lean_closure_set(v___f_886_, 1, v___y_885_);
    v___x_887_ = leanh::lean_apply_1(v___y_883_, v___y_885_);
    v___x_888_ = leanh::lean_apply_3(
        v_orElse_881_,
        leanh::lean_box(0),
        v___x_887_,
        v___f_886_,
    );
    return v___x_888_;
}
pub unsafe fn l_Lake_EquipT_instAlternative___redArg(
    mut v_inst_889_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_toApplicative_890_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_failure_891_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_orElse_892_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_894_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_895_: u8 = 0;
    let mut v___f_896_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_897_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_898_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_900_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_901_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_902_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_toApplicative_890_ = leanh::lean_ctor_get(v_inst_889_, 0);
                v_failure_891_ = leanh::lean_ctor_get(v_inst_889_, 1);
                v_orElse_892_ = leanh::lean_ctor_get(v_inst_889_, 2);
                v_isSharedCheck_902_ = (!leanh::lean_is_exclusive(v_inst_889_)) as u8;
                if v_isSharedCheck_902_ == 0 {
                    v___x_894_ = v_inst_889_;
                    v_isShared_895_ = v_isSharedCheck_902_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_orElse_892_);
                    leanh::lean_inc(v_failure_891_);
                    leanh::lean_inc(v_toApplicative_890_);
                    leanh::lean_dec(v_inst_889_);
                    v___x_894_ = leanh::lean_box(0);
                    v_isShared_895_ = v_isSharedCheck_902_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___f_896_ = leanh::lean_alloc_closure(
                    l_Lake_EquipT_instAlternative___redArg___lam__0___boxed
                        as *mut core::ffi::c_void,
                    3,
                    1,
                );
                leanh::lean_closure_set(v___f_896_, 0, v_failure_891_);
                v___f_897_ = leanh::lean_alloc_closure(
                    l_Lake_EquipT_instAlternative___redArg___lam__2 as *mut core::ffi::c_void,
                    5,
                    1,
                );
                leanh::lean_closure_set(v___f_897_, 0, v_orElse_892_);
                v___x_898_ = l_Lake_EquipT_instApplicative___redArg(v_toApplicative_890_);
                if v_isShared_895_ == 0 {
                    leanh::lean_ctor_set(v___x_894_, 2, v___f_897_);
                    leanh::lean_ctor_set(v___x_894_, 1, v___f_896_);
                    leanh::lean_ctor_set(v___x_894_, 0, v___x_898_);
                    v___x_900_ = v___x_894_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_901_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_901_, 0, v___x_898_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_901_, 1, v___f_896_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_901_, 2, v___f_897_);
                    v___x_900_ = v_reuseFailAlloc_901_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_900_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lake_EquipT_instAlternative(
    mut v_m_903_: *mut leanh::LeanObject,
    mut v_00_u03c1_904_: *mut leanh::LeanObject,
    mut v_inst_905_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_906_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_906_ = l_Lake_EquipT_instAlternative___redArg(v_inst_905_);
    return v___x_906_;
}
pub unsafe fn l_Lake_EquipT_throw___redArg(
    mut v_inst_907_: *mut leanh::LeanObject,
    mut v_e_908_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_throw_909_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_910_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_throw_909_ = leanh::lean_ctor_get(v_inst_907_, 0);
    leanh::lean_inc(v_throw_909_);
    leanh::lean_dec_ref(v_inst_907_);
    v___x_910_ = leanh::lean_apply_2(v_throw_909_, leanh::lean_box(0), v_e_908_);
    return v___x_910_;
}
pub unsafe fn l_Lake_EquipT_throw(
    mut v_00_u03b5_911_: *mut leanh::LeanObject,
    mut v_m_912_: *mut leanh::LeanObject,
    mut v_00_u03c1_913_: *mut leanh::LeanObject,
    mut v_00_u03b1_914_: *mut leanh::LeanObject,
    mut v_inst_915_: *mut leanh::LeanObject,
    mut v_e_916_: *mut leanh::LeanObject,
    mut v_x_917_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_throw_918_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_919_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_throw_918_ = leanh::lean_ctor_get(v_inst_915_, 0);
    leanh::lean_inc(v_throw_918_);
    leanh::lean_dec_ref(v_inst_915_);
    v___x_919_ = leanh::lean_apply_2(v_throw_918_, leanh::lean_box(0), v_e_916_);
    return v___x_919_;
}
pub unsafe fn l_Lake_EquipT_throw___boxed(
    mut v_00_u03b5_920_: *mut leanh::LeanObject,
    mut v_m_921_: *mut leanh::LeanObject,
    mut v_00_u03c1_922_: *mut leanh::LeanObject,
    mut v_00_u03b1_923_: *mut leanh::LeanObject,
    mut v_inst_924_: *mut leanh::LeanObject,
    mut v_e_925_: *mut leanh::LeanObject,
    mut v_x_926_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_927_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_927_ = l_Lake_EquipT_throw(
        v_00_u03b5_920_,
        v_m_921_,
        v_00_u03c1_922_,
        v_00_u03b1_923_,
        v_inst_924_,
        v_e_925_,
        v_x_926_,
    );
    leanh::lean_dec(v_x_926_);
    return v_res_927_;
}
pub unsafe fn l_Lake_EquipT_tryCatch___redArg___lam__0(
    mut v_c_928_: *mut leanh::LeanObject,
    mut v_f_929_: *mut leanh::LeanObject,
    mut v_e_930_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_931_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_931_ = leanh::lean_apply_2(v_c_928_, v_e_930_, v_f_929_);
    return v___x_931_;
}
pub unsafe fn l_Lake_EquipT_tryCatch___redArg(
    mut v_inst_932_: *mut leanh::LeanObject,
    mut v_self_933_: *mut leanh::LeanObject,
    mut v_c_934_: *mut leanh::LeanObject,
    mut v_f_935_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_tryCatch_936_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_937_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_938_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_939_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_tryCatch_936_ = leanh::lean_ctor_get(v_inst_932_, 1);
    leanh::lean_inc(v_tryCatch_936_);
    leanh::lean_dec_ref(v_inst_932_);
    leanh::lean_inc(v_f_935_);
    v___f_937_ = leanh::lean_alloc_closure(
        l_Lake_EquipT_tryCatch___redArg___lam__0 as *mut core::ffi::c_void,
        3,
        2,
    );
    leanh::lean_closure_set(v___f_937_, 0, v_c_934_);
    leanh::lean_closure_set(v___f_937_, 1, v_f_935_);
    v___x_938_ = leanh::lean_apply_1(v_self_933_, v_f_935_);
    v___x_939_ = leanh::lean_apply_3(
        v_tryCatch_936_,
        leanh::lean_box(0),
        v___x_938_,
        v___f_937_,
    );
    return v___x_939_;
}
pub unsafe fn l_Lake_EquipT_tryCatch(
    mut v_00_u03b5_940_: *mut leanh::LeanObject,
    mut v_m_941_: *mut leanh::LeanObject,
    mut v_00_u03c1_942_: *mut leanh::LeanObject,
    mut v_00_u03b1_943_: *mut leanh::LeanObject,
    mut v_inst_944_: *mut leanh::LeanObject,
    mut v_self_945_: *mut leanh::LeanObject,
    mut v_c_946_: *mut leanh::LeanObject,
    mut v_f_947_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_tryCatch_948_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_949_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_950_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_951_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_tryCatch_948_ = leanh::lean_ctor_get(v_inst_944_, 1);
    leanh::lean_inc(v_tryCatch_948_);
    leanh::lean_dec_ref(v_inst_944_);
    leanh::lean_inc(v_f_947_);
    v___f_949_ = leanh::lean_alloc_closure(
        l_Lake_EquipT_tryCatch___redArg___lam__0 as *mut core::ffi::c_void,
        3,
        2,
    );
    leanh::lean_closure_set(v___f_949_, 0, v_c_946_);
    leanh::lean_closure_set(v___f_949_, 1, v_f_947_);
    v___x_950_ = leanh::lean_apply_1(v_self_945_, v_f_947_);
    v___x_951_ = leanh::lean_apply_3(
        v_tryCatch_948_,
        leanh::lean_box(0),
        v___x_950_,
        v___f_949_,
    );
    return v___x_951_;
}
pub unsafe fn l_Lake_EquipT_instMonadExceptOf___redArg___lam__0(
    mut v_inst_952_: *mut leanh::LeanObject,
    mut v_00_u03b1_953_: *mut leanh::LeanObject,
    mut v___y_954_: *mut leanh::LeanObject,
    mut v___y_955_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_throw_956_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_957_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_throw_956_ = leanh::lean_ctor_get(v_inst_952_, 0);
    leanh::lean_inc(v_throw_956_);
    leanh::lean_dec_ref(v_inst_952_);
    v___x_957_ = leanh::lean_apply_2(v_throw_956_, leanh::lean_box(0), v___y_954_);
    return v___x_957_;
}
pub unsafe fn l_Lake_EquipT_instMonadExceptOf___redArg___lam__0___boxed(
    mut v_inst_958_: *mut leanh::LeanObject,
    mut v_00_u03b1_959_: *mut leanh::LeanObject,
    mut v___y_960_: *mut leanh::LeanObject,
    mut v___y_961_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_962_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_962_ = l_Lake_EquipT_instMonadExceptOf___redArg___lam__0(
        v_inst_958_,
        v_00_u03b1_959_,
        v___y_960_,
        v___y_961_,
    );
    leanh::lean_dec(v___y_961_);
    return v_res_962_;
}
pub unsafe fn l_Lake_EquipT_instMonadExceptOf___redArg___lam__1(
    mut v___y_963_: *mut leanh::LeanObject,
    mut v___y_964_: *mut leanh::LeanObject,
    mut v_e_965_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_966_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_966_ = leanh::lean_apply_2(v___y_963_, v_e_965_, v___y_964_);
    return v___x_966_;
}
pub unsafe fn l_Lake_EquipT_instMonadExceptOf___redArg___lam__2(
    mut v_inst_967_: *mut leanh::LeanObject,
    mut v_00_u03b1_968_: *mut leanh::LeanObject,
    mut v___y_969_: *mut leanh::LeanObject,
    mut v___y_970_: *mut leanh::LeanObject,
    mut v___y_971_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_tryCatch_972_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_973_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_974_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_975_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_tryCatch_972_ = leanh::lean_ctor_get(v_inst_967_, 1);
    leanh::lean_inc(v_tryCatch_972_);
    leanh::lean_dec_ref(v_inst_967_);
    leanh::lean_inc(v___y_971_);
    v___f_973_ = leanh::lean_alloc_closure(
        l_Lake_EquipT_instMonadExceptOf___redArg___lam__1 as *mut core::ffi::c_void,
        3,
        2,
    );
    leanh::lean_closure_set(v___f_973_, 0, v___y_970_);
    leanh::lean_closure_set(v___f_973_, 1, v___y_971_);
    v___x_974_ = leanh::lean_apply_1(v___y_969_, v___y_971_);
    v___x_975_ = leanh::lean_apply_3(
        v_tryCatch_972_,
        leanh::lean_box(0),
        v___x_974_,
        v___f_973_,
    );
    return v___x_975_;
}
pub unsafe fn l_Lake_EquipT_instMonadExceptOf___redArg(
    mut v_inst_976_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_977_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_978_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_979_: *mut leanh::LeanObject = core::ptr::null_mut();
    leanh::lean_inc_ref(v_inst_976_);
    v___f_977_ = leanh::lean_alloc_closure(
        l_Lake_EquipT_instMonadExceptOf___redArg___lam__0___boxed as *mut core::ffi::c_void,
        4,
        1,
    );
    leanh::lean_closure_set(v___f_977_, 0, v_inst_976_);
    v___f_978_ = leanh::lean_alloc_closure(
        l_Lake_EquipT_instMonadExceptOf___redArg___lam__2 as *mut core::ffi::c_void,
        5,
        1,
    );
    leanh::lean_closure_set(v___f_978_, 0, v_inst_976_);
    v___x_979_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_979_, 0, v___f_977_);
    leanh::lean_ctor_set(v___x_979_, 1, v___f_978_);
    return v___x_979_;
}
pub unsafe fn l_Lake_EquipT_instMonadExceptOf(
    mut v_m_980_: *mut leanh::LeanObject,
    mut v_00_u03c1_981_: *mut leanh::LeanObject,
    mut v_00_u03b5_982_: *mut leanh::LeanObject,
    mut v_inst_983_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_984_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_984_ = l_Lake_EquipT_instMonadExceptOf___redArg(v_inst_983_);
    return v___x_984_;
}
pub unsafe fn l_Lake_EquipT_tryFinally_x27___redArg___lam__0(
    mut v_f_985_: *mut leanh::LeanObject,
    mut v_ctx_986_: *mut leanh::LeanObject,
    mut v_a_x3f_987_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_988_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_988_ = leanh::lean_apply_2(v_f_985_, v_a_x3f_987_, v_ctx_986_);
    return v___x_988_;
}
pub unsafe fn l_Lake_EquipT_tryFinally_x27___redArg(
    mut v_inst_989_: *mut leanh::LeanObject,
    mut v_x_990_: *mut leanh::LeanObject,
    mut v_f_991_: *mut leanh::LeanObject,
    mut v_ctx_992_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_993_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_994_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_995_: *mut leanh::LeanObject = core::ptr::null_mut();
    leanh::lean_inc(v_ctx_992_);
    v___f_993_ = leanh::lean_alloc_closure(
        l_Lake_EquipT_tryFinally_x27___redArg___lam__0 as *mut core::ffi::c_void,
        3,
        2,
    );
    leanh::lean_closure_set(v___f_993_, 0, v_f_991_);
    leanh::lean_closure_set(v___f_993_, 1, v_ctx_992_);
    v___x_994_ = leanh::lean_apply_1(v_x_990_, v_ctx_992_);
    v___x_995_ = leanh::lean_apply_4(
        v_inst_989_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v___x_994_,
        v___f_993_,
    );
    return v___x_995_;
}
pub unsafe fn l_Lake_EquipT_tryFinally_x27(
    mut v_m_996_: *mut leanh::LeanObject,
    mut v_00_u03c1_997_: *mut leanh::LeanObject,
    mut v_00_u03b1_998_: *mut leanh::LeanObject,
    mut v_00_u03b2_999_: *mut leanh::LeanObject,
    mut v_inst_1000_: *mut leanh::LeanObject,
    mut v_inst_1001_: *mut leanh::LeanObject,
    mut v_x_1002_: *mut leanh::LeanObject,
    mut v_f_1003_: *mut leanh::LeanObject,
    mut v_ctx_1004_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_1005_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1006_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1007_: *mut leanh::LeanObject = core::ptr::null_mut();
    leanh::lean_inc(v_ctx_1004_);
    v___f_1005_ = leanh::lean_alloc_closure(
        l_Lake_EquipT_tryFinally_x27___redArg___lam__0 as *mut core::ffi::c_void,
        3,
        2,
    );
    leanh::lean_closure_set(v___f_1005_, 0, v_f_1003_);
    leanh::lean_closure_set(v___f_1005_, 1, v_ctx_1004_);
    v___x_1006_ = leanh::lean_apply_1(v_x_1002_, v_ctx_1004_);
    v___x_1007_ = leanh::lean_apply_4(
        v_inst_1000_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v___x_1006_,
        v___f_1005_,
    );
    return v___x_1007_;
}
pub unsafe fn l_Lake_EquipT_tryFinally_x27___boxed(
    mut v_m_1008_: *mut leanh::LeanObject,
    mut v_00_u03c1_1009_: *mut leanh::LeanObject,
    mut v_00_u03b1_1010_: *mut leanh::LeanObject,
    mut v_00_u03b2_1011_: *mut leanh::LeanObject,
    mut v_inst_1012_: *mut leanh::LeanObject,
    mut v_inst_1013_: *mut leanh::LeanObject,
    mut v_x_1014_: *mut leanh::LeanObject,
    mut v_f_1015_: *mut leanh::LeanObject,
    mut v_ctx_1016_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1017_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1017_ = l_Lake_EquipT_tryFinally_x27(
        v_m_1008_,
        v_00_u03c1_1009_,
        v_00_u03b1_1010_,
        v_00_u03b2_1011_,
        v_inst_1012_,
        v_inst_1013_,
        v_x_1014_,
        v_f_1015_,
        v_ctx_1016_,
    );
    leanh::lean_dec_ref(v_inst_1013_);
    return v_res_1017_;
}
pub unsafe fn l_Lake_EquipT_instMonadFinallyOfMonad___redArg___lam__0(
    mut v___y_1018_: *mut leanh::LeanObject,
    mut v___y_1019_: *mut leanh::LeanObject,
    mut v_a_x3f_1020_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1021_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1021_ = leanh::lean_apply_2(v___y_1018_, v_a_x3f_1020_, v___y_1019_);
    return v___x_1021_;
}
pub unsafe fn l_Lake_EquipT_instMonadFinallyOfMonad___redArg___lam__1(
    mut v_inst_1022_: *mut leanh::LeanObject,
    mut v_00_u03b1_1023_: *mut leanh::LeanObject,
    mut v_00_u03b2_1024_: *mut leanh::LeanObject,
    mut v___y_1025_: *mut leanh::LeanObject,
    mut v___y_1026_: *mut leanh::LeanObject,
    mut v___y_1027_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_1028_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1029_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1030_: *mut leanh::LeanObject = core::ptr::null_mut();
    leanh::lean_inc(v___y_1027_);
    v___f_1028_ = leanh::lean_alloc_closure(
        l_Lake_EquipT_instMonadFinallyOfMonad___redArg___lam__0 as *mut core::ffi::c_void,
        3,
        2,
    );
    leanh::lean_closure_set(v___f_1028_, 0, v___y_1026_);
    leanh::lean_closure_set(v___f_1028_, 1, v___y_1027_);
    v___x_1029_ = leanh::lean_apply_1(v___y_1025_, v___y_1027_);
    v___x_1030_ = leanh::lean_apply_4(
        v_inst_1022_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v___x_1029_,
        v___f_1028_,
    );
    return v___x_1030_;
}
pub unsafe fn l_Lake_EquipT_instMonadFinallyOfMonad___redArg(
    mut v_inst_1031_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_1032_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_1032_ = leanh::lean_alloc_closure(
        l_Lake_EquipT_instMonadFinallyOfMonad___redArg___lam__1 as *mut core::ffi::c_void,
        6,
        1,
    );
    leanh::lean_closure_set(v___f_1032_, 0, v_inst_1031_);
    return v___f_1032_;
}
pub unsafe fn l_Lake_EquipT_instMonadFinallyOfMonad(
    mut v_m_1033_: *mut leanh::LeanObject,
    mut v_00_u03c1_1034_: *mut leanh::LeanObject,
    mut v_inst_1035_: *mut leanh::LeanObject,
    mut v_inst_1036_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_1037_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_1037_ = leanh::lean_alloc_closure(
        l_Lake_EquipT_instMonadFinallyOfMonad___redArg___lam__1 as *mut core::ffi::c_void,
        6,
        1,
    );
    leanh::lean_closure_set(v___f_1037_, 0, v_inst_1035_);
    return v___f_1037_;
}
pub unsafe fn l_Lake_EquipT_instMonadFinallyOfMonad___boxed(
    mut v_m_1038_: *mut leanh::LeanObject,
    mut v_00_u03c1_1039_: *mut leanh::LeanObject,
    mut v_inst_1040_: *mut leanh::LeanObject,
    mut v_inst_1041_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1042_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1042_ = l_Lake_EquipT_instMonadFinallyOfMonad(
        v_m_1038_,
        v_00_u03c1_1039_,
        v_inst_1040_,
        v_inst_1041_,
    );
    leanh::lean_dec_ref(v_inst_1041_);
    return v_res_1042_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lake_Util_EquipT(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Init_Control_Except(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lake_Util_EquipT(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_meta_initialized = true;
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lake_Util_EquipT(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Init_Control_Except(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lake_Util_EquipT(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = meta_initialize_Lake_Util_EquipT(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return initialize_Lake_Util_EquipT(builtin);
}