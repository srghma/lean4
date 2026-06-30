// Lean compiler output
// Module: Lean.Server.AsyncList
// Imports: Lean.Server.ServerTask
use crate::ffi::{
    lean_io_mono_ms_now, lean_io_wait, lean_nat_sub, lean_task_pure, lean_uint32_dec_eq,
    lean_uint32_of_nat, lean_uint32_to_nat,
};
use crate::r#gen::Init::Data::List::Basic::{
    l_List_appendTR___redArg, l_List_isEmpty___redArg, l_List_reverse___redArg,
};
use crate::r#gen::Init::System::IO::{l_IO_sleep, l_IO_sleep___boxed};
use crate::r#gen::Lean::Server::ServerTask::{
    initialize_Lean_Server_ServerTask, l_Lean_Server_ServerTask_BaseIO_asTask___redArg,
    l_Lean_Server_ServerTask_bindCheap___redArg, l_Lean_Server_ServerTask_hasFinished___redArg,
    l_Lean_Server_ServerTask_mapCheap___redArg, l_Lean_Server_ServerTask_waitAny___redArg,
    runtime_initialize_Lean_Server_ServerTask,
};
pub static l_IO_AsyncList_instCoeList___closed__0_value: leanh::LeanClosureObject<2> =
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
        m_fun: l_IO_AsyncList_ofList as *const core::ffi::c_void,
        m_arity: 3,
        m_num_fixed: 2,
        m_objs: [
            (((0 as usize) << 1) | 1) as *mut leanh::LeanObject,
            (((0 as usize) << 1) | 1) as *mut leanh::LeanObject,
        ],
    };
static mut l_IO_AsyncList_instCoeList___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_IO_AsyncList_instCoeList___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_IO_AsyncList_waitUntil___redArg___closed__0_value: leanh::LeanCtorObject<2> =
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
            (((0 as usize) << 1) | 1) as *mut leanh::LeanObject,
        ],
    };
static mut l_IO_AsyncList_waitUntil___redArg___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_IO_AsyncList_waitUntil___redArg___closed__0_value)
        as *mut leanh::LeanObject;
static mut l_IO_AsyncList_waitUntil___redArg___closed__1_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_IO_AsyncList_waitUntil___redArg___closed__1: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_IO_AsyncList_waitAll___redArg___closed__0_value: leanh::LeanClosureObject<0> =
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
        m_fun: l_IO_AsyncList_waitAll___redArg___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_IO_AsyncList_waitAll___redArg___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_IO_AsyncList_waitAll___redArg___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_IO_AsyncList_waitFind_x3f___redArg___closed__0_value: leanh::LeanCtorObject<1> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 1,
        },
        m_objs: [(((0 as usize) << 1) | 1) as *mut leanh::LeanObject],
    };
static mut l_IO_AsyncList_waitFind_x3f___redArg___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_IO_AsyncList_waitFind_x3f___redArg___closed__0_value)
        as *mut leanh::LeanObject;
static mut l_IO_AsyncList_waitFind_x3f___redArg___closed__1_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_IO_AsyncList_waitFind_x3f___redArg___closed__1: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_IO_AsyncList_getFinishedPrefix___redArg___closed__0_value:
    leanh::LeanCtorObject<2> = leanh::LeanCtorObject {
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
        (((1 as usize) << 1) | 1) as *mut leanh::LeanObject,
    ],
};
static mut l_IO_AsyncList_getFinishedPrefix___redArg___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_IO_AsyncList_getFinishedPrefix___redArg___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_IO_AsyncList_getFinishedPrefix___redArg___closed__1_value:
    leanh::LeanCtorObject<2> = leanh::LeanCtorObject {
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
        core::ptr::addr_of!(l_IO_AsyncList_getFinishedPrefix___redArg___closed__0_value)
            as *mut leanh::LeanObject,
    ],
};
static mut l_IO_AsyncList_getFinishedPrefix___redArg___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_IO_AsyncList_getFinishedPrefix___redArg___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_List_mapTR_loop___at___00__private_Lean_Server_AsyncList_0__IO_AsyncList_getFinishedPrefixWithTimeout_go_spec__0___redArg___closed__0_value: leanh::LeanClosureObject<0> = leanh::LeanClosureObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_List_mapTR_loop___at___00__private_Lean_Server_AsyncList_0__IO_AsyncList_getFinishedPrefixWithTimeout_go_spec__0___redArg___lam__0 as *const core::ffi::c_void, m_arity: 1, m_num_fixed: 0, m_objs: [] };
static mut l_List_mapTR_loop___at___00__private_Lean_Server_AsyncList_0__IO_AsyncList_getFinishedPrefixWithTimeout_go_spec__0___redArg___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l_List_mapTR_loop___at___00__private_Lean_Server_AsyncList_0__IO_AsyncList_getFinishedPrefixWithTimeout_go_spec__0___redArg___closed__0_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Server_AsyncList_0__IO_AsyncList_getFinishedPrefixWithTimeout_go___redArg___closed__0_value: leanh::LeanClosureObject<0> = leanh::LeanClosureObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l___private_Lean_Server_AsyncList_0__IO_AsyncList_getFinishedPrefixWithTimeout_go___redArg___lam__0 as *const core::ffi::c_void, m_arity: 1, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_Server_AsyncList_0__IO_AsyncList_getFinishedPrefixWithTimeout_go___redArg___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Server_AsyncList_0__IO_AsyncList_getFinishedPrefixWithTimeout_go___redArg___closed__0_value) as *mut leanh::LeanObject;
pub static l_IO_AsyncList_getFinishedPrefixWithTimeout___redArg___lam__0___closed__0_value:
    leanh::LeanCtorObject<1> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 0,
    },
    m_objs: [(((0 as usize) << 1) | 1) as *mut leanh::LeanObject],
};
static mut l_IO_AsyncList_getFinishedPrefixWithTimeout___redArg___lam__0___closed__0:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_IO_AsyncList_getFinishedPrefixWithTimeout___redArg___lam__0___closed__0_value
) as *mut leanh::LeanObject;
static mut l_IO_AsyncList_getFinishedPrefixWithTimeout___redArg___closed__0_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_IO_AsyncList_getFinishedPrefixWithTimeout___redArg___closed__0:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub unsafe fn l_IO_AsyncList_ctorIdx___redArg(
    mut v_x_504_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    match leanh::lean_obj_tag(v_x_504_) {
        0 => {
            let mut v___x_505_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_505_ = leanh::lean_unsigned_to_nat(0);
            return v___x_505_;
        }
        1 => {
            let mut v___x_506_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_506_ = leanh::lean_unsigned_to_nat(1);
            return v___x_506_;
        }
        _ => {
            let mut v___x_507_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_507_ = leanh::lean_unsigned_to_nat(2);
            return v___x_507_;
        }
    }
}
pub unsafe fn l_IO_AsyncList_ctorIdx___redArg___boxed(
    mut v_x_508_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_509_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_509_ = l_IO_AsyncList_ctorIdx___redArg(v_x_508_);
    leanh::lean_dec(v_x_508_);
    return v_res_509_;
}
pub unsafe fn l_IO_AsyncList_ctorIdx(
    mut v_00_u03b5_510_: *mut leanh::LeanObject,
    mut v_00_u03b1_511_: *mut leanh::LeanObject,
    mut v_x_512_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_513_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_513_ = l_IO_AsyncList_ctorIdx___redArg(v_x_512_);
    return v___x_513_;
}
pub unsafe fn l_IO_AsyncList_ctorIdx___boxed(
    mut v_00_u03b5_514_: *mut leanh::LeanObject,
    mut v_00_u03b1_515_: *mut leanh::LeanObject,
    mut v_x_516_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_517_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_517_ = l_IO_AsyncList_ctorIdx(v_00_u03b5_514_, v_00_u03b1_515_, v_x_516_);
    leanh::lean_dec(v_x_516_);
    return v_res_517_;
}
pub unsafe fn l_IO_AsyncList_ctorElim___redArg(
    mut v_t_518_: *mut leanh::LeanObject,
    mut v_k_519_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    match leanh::lean_obj_tag(v_t_518_) {
        0 => {
            let mut v_hd_520_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_tl_521_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_522_: *mut leanh::LeanObject = core::ptr::null_mut();
            v_hd_520_ = leanh::lean_ctor_get(v_t_518_, 0);
            leanh::lean_inc(v_hd_520_);
            v_tl_521_ = leanh::lean_ctor_get(v_t_518_, 1);
            leanh::lean_inc(v_tl_521_);
            leanh::lean_dec_ref_known(v_t_518_, 2);
            v___x_522_ = leanh::lean_apply_2(v_k_519_, v_hd_520_, v_tl_521_);
            return v___x_522_;
        }
        1 => {
            let mut v_tl_523_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_524_: *mut leanh::LeanObject = core::ptr::null_mut();
            v_tl_523_ = leanh::lean_ctor_get(v_t_518_, 0);
            leanh::lean_inc_ref(v_tl_523_);
            leanh::lean_dec_ref_known(v_t_518_, 1);
            v___x_524_ = leanh::lean_apply_1(v_k_519_, v_tl_523_);
            return v___x_524_;
        }
        _ => {
            return v_k_519_;
        }
    }
}
pub unsafe fn l_IO_AsyncList_ctorElim(
    mut v_00_u03b5_525_: *mut leanh::LeanObject,
    mut v_00_u03b1_526_: *mut leanh::LeanObject,
    mut v_motive__1_527_: *mut leanh::LeanObject,
    mut v_ctorIdx_528_: *mut leanh::LeanObject,
    mut v_t_529_: *mut leanh::LeanObject,
    mut v_h_530_: *mut leanh::LeanObject,
    mut v_k_531_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_532_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_532_ = l_IO_AsyncList_ctorElim___redArg(v_t_529_, v_k_531_);
    return v___x_532_;
}
pub unsafe fn l_IO_AsyncList_ctorElim___boxed(
    mut v_00_u03b5_533_: *mut leanh::LeanObject,
    mut v_00_u03b1_534_: *mut leanh::LeanObject,
    mut v_motive__1_535_: *mut leanh::LeanObject,
    mut v_ctorIdx_536_: *mut leanh::LeanObject,
    mut v_t_537_: *mut leanh::LeanObject,
    mut v_h_538_: *mut leanh::LeanObject,
    mut v_k_539_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_540_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_540_ = l_IO_AsyncList_ctorElim(
        v_00_u03b5_533_,
        v_00_u03b1_534_,
        v_motive__1_535_,
        v_ctorIdx_536_,
        v_t_537_,
        v_h_538_,
        v_k_539_,
    );
    leanh::lean_dec(v_ctorIdx_536_);
    return v_res_540_;
}
pub unsafe fn l_IO_AsyncList_cons_elim___redArg(
    mut v_t_541_: *mut leanh::LeanObject,
    mut v_cons_542_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_543_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_543_ = l_IO_AsyncList_ctorElim___redArg(v_t_541_, v_cons_542_);
    return v___x_543_;
}
pub unsafe fn l_IO_AsyncList_cons_elim(
    mut v_00_u03b5_544_: *mut leanh::LeanObject,
    mut v_00_u03b1_545_: *mut leanh::LeanObject,
    mut v_motive__1_546_: *mut leanh::LeanObject,
    mut v_t_547_: *mut leanh::LeanObject,
    mut v_h_548_: *mut leanh::LeanObject,
    mut v_cons_549_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_550_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_550_ = l_IO_AsyncList_ctorElim___redArg(v_t_547_, v_cons_549_);
    return v___x_550_;
}
pub unsafe fn l_IO_AsyncList_delayed_elim___redArg(
    mut v_t_551_: *mut leanh::LeanObject,
    mut v_delayed_552_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_553_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_553_ = l_IO_AsyncList_ctorElim___redArg(v_t_551_, v_delayed_552_);
    return v___x_553_;
}
pub unsafe fn l_IO_AsyncList_delayed_elim(
    mut v_00_u03b5_554_: *mut leanh::LeanObject,
    mut v_00_u03b1_555_: *mut leanh::LeanObject,
    mut v_motive__1_556_: *mut leanh::LeanObject,
    mut v_t_557_: *mut leanh::LeanObject,
    mut v_h_558_: *mut leanh::LeanObject,
    mut v_delayed_559_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_560_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_560_ = l_IO_AsyncList_ctorElim___redArg(v_t_557_, v_delayed_559_);
    return v___x_560_;
}
pub unsafe fn l_IO_AsyncList_nil_elim___redArg(
    mut v_t_561_: *mut leanh::LeanObject,
    mut v_nil_562_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_563_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_563_ = l_IO_AsyncList_ctorElim___redArg(v_t_561_, v_nil_562_);
    return v___x_563_;
}
pub unsafe fn l_IO_AsyncList_nil_elim(
    mut v_00_u03b5_564_: *mut leanh::LeanObject,
    mut v_00_u03b1_565_: *mut leanh::LeanObject,
    mut v_motive__1_566_: *mut leanh::LeanObject,
    mut v_t_567_: *mut leanh::LeanObject,
    mut v_h_568_: *mut leanh::LeanObject,
    mut v_nil_569_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_570_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_570_ = l_IO_AsyncList_ctorElim___redArg(v_t_567_, v_nil_569_);
    return v___x_570_;
}
pub unsafe fn l_IO_AsyncList_instInhabited(
    mut v_00_u03b5_571_: *mut leanh::LeanObject,
    mut v_00_u03b1_572_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_573_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_573_ = leanh::lean_box(2);
    return v___x_573_;
}
pub unsafe fn l_List_foldr___at___00IO_AsyncList_ofList_spec__0___redArg(
    mut v_init_574_: *mut leanh::LeanObject,
    mut v_x_575_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_head_576_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_577_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_579_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_580_: u8 = 0;
    let mut v___x_581_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_583_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_584_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_585_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_575_) == 0 {
                    leanh::lean_inc(v_init_574_);
                    return v_init_574_;
                } else {
                    v_head_576_ = leanh::lean_ctor_get(v_x_575_, 0);
                    v_tail_577_ = leanh::lean_ctor_get(v_x_575_, 1);
                    v_isSharedCheck_585_ = (!leanh::lean_is_exclusive(v_x_575_)) as u8;
                    if v_isSharedCheck_585_ == 0 {
                        v___x_579_ = v_x_575_;
                        v_isShared_580_ = v_isSharedCheck_585_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_tail_577_);
                        leanh::lean_inc(v_head_576_);
                        leanh::lean_dec(v_x_575_);
                        v___x_579_ = leanh::lean_box(0);
                        v_isShared_580_ = v_isSharedCheck_585_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_581_ = l_List_foldr___at___00IO_AsyncList_ofList_spec__0___redArg(
                    v_init_574_,
                    v_tail_577_,
                );
                if v_isShared_580_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_579_, 0);
                    leanh::lean_ctor_set(v___x_579_, 1, v___x_581_);
                    v___x_583_ = v___x_579_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_584_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_584_, 0, v_head_576_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_584_, 1, v___x_581_);
                    v___x_583_ = v_reuseFailAlloc_584_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_583_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_foldr___at___00IO_AsyncList_ofList_spec__0___redArg___boxed(
    mut v_init_586_: *mut leanh::LeanObject,
    mut v_x_587_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_588_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_588_ = l_List_foldr___at___00IO_AsyncList_ofList_spec__0___redArg(v_init_586_, v_x_587_);
    leanh::lean_dec(v_init_586_);
    return v_res_588_;
}
pub unsafe fn l_IO_AsyncList_ofList___redArg(
    mut v_l_589_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_590_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_591_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_590_ = leanh::lean_box(2);
    v___x_591_ = l_List_foldr___at___00IO_AsyncList_ofList_spec__0___redArg(v___x_590_, v_l_589_);
    return v___x_591_;
}
pub unsafe fn l_IO_AsyncList_ofList(
    mut v_00_u03b1_592_: *mut leanh::LeanObject,
    mut v_00_u03b5_593_: *mut leanh::LeanObject,
    mut v_l_594_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_595_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_595_ = l_IO_AsyncList_ofList___redArg(v_l_594_);
    return v___x_595_;
}
pub unsafe fn l_List_foldr___at___00IO_AsyncList_ofList_spec__0(
    mut v_00_u03b1_596_: *mut leanh::LeanObject,
    mut v_00_u03b5_597_: *mut leanh::LeanObject,
    mut v_init_598_: *mut leanh::LeanObject,
    mut v_x_599_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_600_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_600_ = l_List_foldr___at___00IO_AsyncList_ofList_spec__0___redArg(v_init_598_, v_x_599_);
    return v___x_600_;
}
pub unsafe fn l_List_foldr___at___00IO_AsyncList_ofList_spec__0___boxed(
    mut v_00_u03b1_601_: *mut leanh::LeanObject,
    mut v_00_u03b5_602_: *mut leanh::LeanObject,
    mut v_init_603_: *mut leanh::LeanObject,
    mut v_x_604_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_605_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_605_ = l_List_foldr___at___00IO_AsyncList_ofList_spec__0(
        v_00_u03b1_601_,
        v_00_u03b5_602_,
        v_init_603_,
        v_x_604_,
    );
    leanh::lean_dec(v_init_603_);
    return v_res_605_;
}
pub unsafe fn l_IO_AsyncList_instCoeList(
    mut v_00_u03b1_607_: *mut leanh::LeanObject,
    mut v_00_u03b5_608_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_609_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_609_ = l_IO_AsyncList_instCoeList___closed__0;
    return v___x_609_;
}
pub unsafe fn l_IO_AsyncList_waitUntil___redArg___lam__0(
    mut v_hd_610_: *mut leanh::LeanObject,
    mut v_x_611_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_fst_612_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_613_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_615_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_616_: u8 = 0;
    let mut v___x_617_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_619_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_620_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_621_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_fst_612_ = leanh::lean_ctor_get(v_x_611_, 0);
                v_snd_613_ = leanh::lean_ctor_get(v_x_611_, 1);
                v_isSharedCheck_621_ = (!leanh::lean_is_exclusive(v_x_611_)) as u8;
                if v_isSharedCheck_621_ == 0 {
                    v___x_615_ = v_x_611_;
                    v_isShared_616_ = v_isSharedCheck_621_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_snd_613_);
                    leanh::lean_inc(v_fst_612_);
                    leanh::lean_dec(v_x_611_);
                    v___x_615_ = leanh::lean_box(0);
                    v_isShared_616_ = v_isSharedCheck_621_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_617_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_617_, 0, v_hd_610_);
                leanh::lean_ctor_set(v___x_617_, 1, v_fst_612_);
                if v_isShared_616_ == 0 {
                    leanh::lean_ctor_set(v___x_615_, 0, v___x_617_);
                    v___x_619_ = v___x_615_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_620_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_620_, 0, v___x_617_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_620_, 1, v_snd_613_);
                    v___x_619_ = v_reuseFailAlloc_620_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_619_;
            }
            _ => {}
        }
    }
}
pub unsafe fn _init_l_IO_AsyncList_waitUntil___redArg___closed__1() -> *mut leanh::LeanObject
{
    let mut v___x_625_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_626_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_625_ = l_IO_AsyncList_waitUntil___redArg___closed__0;
    v___x_626_ = lean_task_pure(v___x_625_);
    return v___x_626_;
}
pub unsafe fn l_IO_AsyncList_waitUntil___redArg(
    mut v_p_627_: *mut leanh::LeanObject,
    mut v_x_628_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_hd_629_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tl_630_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_632_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_633_: u8 = 0;
    let mut v___x_634_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_635_: u8 = 0;
    let mut v___f_636_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_637_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_638_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_639_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_641_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_642_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_643_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_644_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_645_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_646_: u8 = 0;
    let mut v_tl_647_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_648_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_649_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_650_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => match leanh::lean_obj_tag(v_x_628_) {
                0 => {
                    v_hd_629_ = leanh::lean_ctor_get(v_x_628_, 0);
                    v_tl_630_ = leanh::lean_ctor_get(v_x_628_, 1);
                    v_isSharedCheck_646_ = (!leanh::lean_is_exclusive(v_x_628_)) as u8;
                    if v_isSharedCheck_646_ == 0 {
                        v___x_632_ = v_x_628_;
                        v_isShared_633_ = v_isSharedCheck_646_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_tl_630_);
                        leanh::lean_inc(v_hd_629_);
                        leanh::lean_dec(v_x_628_);
                        v___x_632_ = leanh::lean_box(0);
                        v_isShared_633_ = v_isSharedCheck_646_;
                        state = 1;
                        continue;
                    }
                }
                1 => {
                    v_tl_647_ = leanh::lean_ctor_get(v_x_628_, 0);
                    leanh::lean_inc_ref(v_tl_647_);
                    leanh::lean_dec_ref_known(v_x_628_, 1);
                    v___f_648_ = leanh::lean_alloc_closure(
                        l_IO_AsyncList_waitUntil___redArg___lam__1 as *mut core::ffi::c_void,
                        2,
                        1,
                    );
                    leanh::lean_closure_set(v___f_648_, 0, v_p_627_);
                    v___x_649_ = l_Lean_Server_ServerTask_bindCheap___redArg(v_tl_647_, v___f_648_);
                    return v___x_649_;
                }
                _ => {
                    leanh::lean_dec_ref(v_p_627_);
                    v___x_650_ = leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(l_IO_AsyncList_waitUntil___redArg___closed__1),
                        core::ptr::addr_of_mut!(l_IO_AsyncList_waitUntil___redArg___closed__1_once),
                        _init_l_IO_AsyncList_waitUntil___redArg___closed__1,
                    );
                    return v___x_650_;
                }
            },
            1 => {
                leanh::lean_inc_ref(v_p_627_);
                leanh::lean_inc(v_hd_629_);
                v___x_634_ = leanh::lean_apply_1(v_p_627_, v_hd_629_);
                v___x_635_ = (leanh::lean_unbox(v___x_634_) as u8);
                if v___x_635_ == 0 {
                    leanh::lean_del_object(v___x_632_);
                    v___f_636_ = leanh::lean_alloc_closure(
                        l_IO_AsyncList_waitUntil___redArg___lam__0 as *mut core::ffi::c_void,
                        2,
                        1,
                    );
                    leanh::lean_closure_set(v___f_636_, 0, v_hd_629_);
                    v___x_637_ = l_IO_AsyncList_waitUntil___redArg(v_p_627_, v_tl_630_);
                    v___x_638_ = l_Lean_Server_ServerTask_mapCheap___redArg(v___f_636_, v___x_637_);
                    return v___x_638_;
                } else {
                    leanh::lean_dec(v_tl_630_);
                    leanh::lean_dec_ref(v_p_627_);
                    v___x_639_ = leanh::lean_box(0);
                    if v_isShared_633_ == 0 {
                        leanh::lean_ctor_set_tag(v___x_632_, 1);
                        leanh::lean_ctor_set(v___x_632_, 1, v___x_639_);
                        v___x_641_ = v___x_632_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_645_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_645_, 0, v_hd_629_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_645_, 1, v___x_639_);
                        v___x_641_ = v_reuseFailAlloc_645_;
                        state = 2;
                        continue;
                    }
                }
            }
            2 => {
                v___x_642_ = leanh::lean_box(0);
                v___x_643_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_643_, 0, v___x_641_);
                leanh::lean_ctor_set(v___x_643_, 1, v___x_642_);
                v___x_644_ = lean_task_pure(v___x_643_);
                return v___x_644_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_IO_AsyncList_waitUntil___redArg___lam__1(
    mut v_p_651_: *mut leanh::LeanObject,
    mut v_x_652_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_a_653_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_655_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_656_: u8 = 0;
    let mut v___x_657_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_659_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_660_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_661_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_662_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_663_: u8 = 0;
    let mut v_a_664_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_665_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_652_) == 0 {
                    leanh::lean_dec_ref(v_p_651_);
                    v_a_653_ = leanh::lean_ctor_get(v_x_652_, 0);
                    v_isSharedCheck_663_ = (!leanh::lean_is_exclusive(v_x_652_)) as u8;
                    if v_isSharedCheck_663_ == 0 {
                        v___x_655_ = v_x_652_;
                        v_isShared_656_ = v_isSharedCheck_663_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_653_);
                        leanh::lean_dec(v_x_652_);
                        v___x_655_ = leanh::lean_box(0);
                        v_isShared_656_ = v_isSharedCheck_663_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_664_ = leanh::lean_ctor_get(v_x_652_, 0);
                    leanh::lean_inc(v_a_664_);
                    leanh::lean_dec_ref_known(v_x_652_, 1);
                    v___x_665_ = l_IO_AsyncList_waitUntil___redArg(v_p_651_, v_a_664_);
                    return v___x_665_;
                }
            }
            1 => {
                v___x_657_ = leanh::lean_box(0);
                if v_isShared_656_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_655_, 1);
                    v___x_659_ = v___x_655_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_662_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_662_, 0, v_a_653_);
                    v___x_659_ = v_reuseFailAlloc_662_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_660_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_660_, 0, v___x_657_);
                leanh::lean_ctor_set(v___x_660_, 1, v___x_659_);
                v___x_661_ = lean_task_pure(v___x_660_);
                return v___x_661_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_IO_AsyncList_waitUntil(
    mut v_00_u03b1_666_: *mut leanh::LeanObject,
    mut v_00_u03b5_667_: *mut leanh::LeanObject,
    mut v_p_668_: *mut leanh::LeanObject,
    mut v_x_669_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_670_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_670_ = l_IO_AsyncList_waitUntil___redArg(v_p_668_, v_x_669_);
    return v___x_670_;
}
pub unsafe fn l_IO_AsyncList_waitAll___redArg___lam__0(
    mut v_x_671_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_672_: u8 = 0;
    v___x_672_ = 0;
    return v___x_672_;
}
pub unsafe fn l_IO_AsyncList_waitAll___redArg___lam__0___boxed(
    mut v_x_673_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_674_: u8 = 0;
    let mut v_r_675_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_674_ = l_IO_AsyncList_waitAll___redArg___lam__0(v_x_673_);
    leanh::lean_dec(v_x_673_);
    v_r_675_ = leanh::lean_box((v_res_674_) as usize);
    return v_r_675_;
}
pub unsafe fn l_IO_AsyncList_waitAll___redArg(
    mut v_a_677_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_678_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_679_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_678_ = l_IO_AsyncList_waitAll___redArg___closed__0;
    v___x_679_ = l_IO_AsyncList_waitUntil___redArg(v___f_678_, v_a_677_);
    return v___x_679_;
}
pub unsafe fn l_IO_AsyncList_waitAll(
    mut v_00_u03b5_680_: *mut leanh::LeanObject,
    mut v_00_u03b1_681_: *mut leanh::LeanObject,
    mut v_a_682_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_683_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_683_ = l_IO_AsyncList_waitAll___redArg(v_a_682_);
    return v___x_683_;
}
pub unsafe fn _init_l_IO_AsyncList_waitFind_x3f___redArg___closed__1()
-> *mut leanh::LeanObject {
    let mut v___x_686_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_687_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_686_ = l_IO_AsyncList_waitFind_x3f___redArg___closed__0;
    v___x_687_ = lean_task_pure(v___x_686_);
    return v___x_687_;
}
pub unsafe fn l_IO_AsyncList_waitFind_x3f___redArg(
    mut v_p_688_: *mut leanh::LeanObject,
    mut v_x_689_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_hd_690_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tl_691_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_692_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_693_: u8 = 0;
    let mut v___x_695_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_696_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_697_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tl_698_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_699_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_700_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_701_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => match leanh::lean_obj_tag(v_x_689_) {
                0 => {
                    v_hd_690_ = leanh::lean_ctor_get(v_x_689_, 0);
                    leanh::lean_inc_n(v_hd_690_, 2);
                    v_tl_691_ = leanh::lean_ctor_get(v_x_689_, 1);
                    leanh::lean_inc(v_tl_691_);
                    leanh::lean_dec_ref_known(v_x_689_, 2);
                    leanh::lean_inc_ref(v_p_688_);
                    v___x_692_ = leanh::lean_apply_1(v_p_688_, v_hd_690_);
                    v___x_693_ = (leanh::lean_unbox(v___x_692_) as u8);
                    if v___x_693_ == 0 {
                        leanh::lean_dec(v_hd_690_);
                        v_x_689_ = v_tl_691_;
                        state = 0;
                        continue;
                    } else {
                        leanh::lean_dec(v_tl_691_);
                        leanh::lean_dec_ref(v_p_688_);
                        v___x_695_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        leanh::lean_ctor_set(v___x_695_, 0, v_hd_690_);
                        v___x_696_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        leanh::lean_ctor_set(v___x_696_, 0, v___x_695_);
                        v___x_697_ = lean_task_pure(v___x_696_);
                        return v___x_697_;
                    }
                }
                1 => {
                    v_tl_698_ = leanh::lean_ctor_get(v_x_689_, 0);
                    leanh::lean_inc_ref(v_tl_698_);
                    leanh::lean_dec_ref_known(v_x_689_, 1);
                    v___f_699_ = leanh::lean_alloc_closure(
                        l_IO_AsyncList_waitFind_x3f___redArg___lam__0 as *mut core::ffi::c_void,
                        2,
                        1,
                    );
                    leanh::lean_closure_set(v___f_699_, 0, v_p_688_);
                    v___x_700_ = l_Lean_Server_ServerTask_bindCheap___redArg(v_tl_698_, v___f_699_);
                    return v___x_700_;
                }
                _ => {
                    leanh::lean_dec_ref(v_p_688_);
                    v___x_701_ = leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(l_IO_AsyncList_waitFind_x3f___redArg___closed__1),
                        core::ptr::addr_of_mut!(
                            l_IO_AsyncList_waitFind_x3f___redArg___closed__1_once
                        ),
                        _init_l_IO_AsyncList_waitFind_x3f___redArg___closed__1,
                    );
                    return v___x_701_;
                }
            },
            _ => {}
        }
    }
}
pub unsafe fn l_IO_AsyncList_waitFind_x3f___redArg___lam__0(
    mut v_p_702_: *mut leanh::LeanObject,
    mut v_x_703_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_a_704_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_706_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_707_: u8 = 0;
    let mut v___x_709_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_710_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_711_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_712_: u8 = 0;
    let mut v_a_713_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_714_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_703_) == 0 {
                    leanh::lean_dec_ref(v_p_702_);
                    v_a_704_ = leanh::lean_ctor_get(v_x_703_, 0);
                    v_isSharedCheck_712_ = (!leanh::lean_is_exclusive(v_x_703_)) as u8;
                    if v_isSharedCheck_712_ == 0 {
                        v___x_706_ = v_x_703_;
                        v_isShared_707_ = v_isSharedCheck_712_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_704_);
                        leanh::lean_dec(v_x_703_);
                        v___x_706_ = leanh::lean_box(0);
                        v_isShared_707_ = v_isSharedCheck_712_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_713_ = leanh::lean_ctor_get(v_x_703_, 0);
                    leanh::lean_inc(v_a_713_);
                    leanh::lean_dec_ref_known(v_x_703_, 1);
                    v___x_714_ = l_IO_AsyncList_waitFind_x3f___redArg(v_p_702_, v_a_713_);
                    return v___x_714_;
                }
            }
            1 => {
                if v_isShared_707_ == 0 {
                    v___x_709_ = v___x_706_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_711_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_711_, 0, v_a_704_);
                    v___x_709_ = v_reuseFailAlloc_711_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_710_ = lean_task_pure(v___x_709_);
                return v___x_710_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_IO_AsyncList_waitFind_x3f(
    mut v_00_u03b1_715_: *mut leanh::LeanObject,
    mut v_00_u03b5_716_: *mut leanh::LeanObject,
    mut v_p_717_: *mut leanh::LeanObject,
    mut v_x_718_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_719_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_719_ = l_IO_AsyncList_waitFind_x3f___redArg(v_p_717_, v_x_718_);
    return v___x_719_;
}
pub unsafe fn l_IO_AsyncList_getFinishedPrefix___redArg(
    mut v_x_727_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_hd_729_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tl_730_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_732_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_733_: u8 = 0;
    let mut v___x_734_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_735_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_736_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_738_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_739_: u8 = 0;
    let mut v___x_741_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_743_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_744_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_745_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_746_: u8 = 0;
    let mut v_isSharedCheck_747_: u8 = 0;
    let mut v_tl_748_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_749_: u8 = 0;
    let mut v___x_750_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_751_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_752_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_753_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_754_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_755_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_756_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_758_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_759_: u8 = 0;
    let mut v___x_760_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_762_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_763_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_764_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_765_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_766_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_767_: u8 = 0;
    let mut v_a_768_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_770_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => match leanh::lean_obj_tag(v_x_727_) {
                0 => {
                    v_hd_729_ = leanh::lean_ctor_get(v_x_727_, 0);
                    v_tl_730_ = leanh::lean_ctor_get(v_x_727_, 1);
                    v_isSharedCheck_747_ = (!leanh::lean_is_exclusive(v_x_727_)) as u8;
                    if v_isSharedCheck_747_ == 0 {
                        v___x_732_ = v_x_727_;
                        v_isShared_733_ = v_isSharedCheck_747_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_tl_730_);
                        leanh::lean_inc(v_hd_729_);
                        leanh::lean_dec(v_x_727_);
                        v___x_732_ = leanh::lean_box(0);
                        v_isShared_733_ = v_isSharedCheck_747_;
                        state = 1;
                        continue;
                    }
                }
                1 => {
                    v_tl_748_ = leanh::lean_ctor_get(v_x_727_, 0);
                    leanh::lean_inc_ref(v_tl_748_);
                    leanh::lean_dec_ref_known(v_x_727_, 1);
                    v___x_749_ = l_Lean_Server_ServerTask_hasFinished___redArg(v_tl_748_);
                    if v___x_749_ == 0 {
                        leanh::lean_dec_ref(v_tl_748_);
                        v___x_750_ = leanh::lean_box(0);
                        v___x_751_ = leanh::lean_box(0);
                        v___x_752_ = leanh::lean_box((v___x_749_) as usize);
                        v___x_753_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        leanh::lean_ctor_set(v___x_753_, 0, v___x_751_);
                        leanh::lean_ctor_set(v___x_753_, 1, v___x_752_);
                        v___x_754_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        leanh::lean_ctor_set(v___x_754_, 0, v___x_750_);
                        leanh::lean_ctor_set(v___x_754_, 1, v___x_753_);
                        return v___x_754_;
                    } else {
                        v___x_755_ = lean_io_wait(v_tl_748_);
                        if leanh::lean_obj_tag(v___x_755_) == 0 {
                            v_a_756_ = leanh::lean_ctor_get(v___x_755_, 0);
                            v_isSharedCheck_767_ =
                                (!leanh::lean_is_exclusive(v___x_755_)) as u8;
                            if v_isSharedCheck_767_ == 0 {
                                v___x_758_ = v___x_755_;
                                v_isShared_759_ = v_isSharedCheck_767_;
                                state = 5;
                                continue;
                            } else {
                                leanh::lean_inc(v_a_756_);
                                leanh::lean_dec(v___x_755_);
                                v___x_758_ = leanh::lean_box(0);
                                v_isShared_759_ = v_isSharedCheck_767_;
                                state = 5;
                                continue;
                            }
                        } else {
                            v_a_768_ = leanh::lean_ctor_get(v___x_755_, 0);
                            leanh::lean_inc(v_a_768_);
                            leanh::lean_dec_ref_known(v___x_755_, 1);
                            v_x_727_ = v_a_768_;
                            state = 0;
                            continue;
                        }
                    }
                }
                _ => {
                    v___x_770_ = l_IO_AsyncList_getFinishedPrefix___redArg___closed__1;
                    return v___x_770_;
                }
            },
            1 => {
                v___x_734_ = l_IO_AsyncList_getFinishedPrefix___redArg(v_tl_730_);
                v_fst_735_ = leanh::lean_ctor_get(v___x_734_, 0);
                v_snd_736_ = leanh::lean_ctor_get(v___x_734_, 1);
                v_isSharedCheck_746_ = (!leanh::lean_is_exclusive(v___x_734_)) as u8;
                if v_isSharedCheck_746_ == 0 {
                    v___x_738_ = v___x_734_;
                    v_isShared_739_ = v_isSharedCheck_746_;
                    state = 2;
                    continue;
                } else {
                    leanh::lean_inc(v_snd_736_);
                    leanh::lean_inc(v_fst_735_);
                    leanh::lean_dec(v___x_734_);
                    v___x_738_ = leanh::lean_box(0);
                    v_isShared_739_ = v_isSharedCheck_746_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                if v_isShared_733_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_732_, 1);
                    leanh::lean_ctor_set(v___x_732_, 1, v_fst_735_);
                    v___x_741_ = v___x_732_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_745_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_745_, 0, v_hd_729_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_745_, 1, v_fst_735_);
                    v___x_741_ = v_reuseFailAlloc_745_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_739_ == 0 {
                    leanh::lean_ctor_set(v___x_738_, 0, v___x_741_);
                    v___x_743_ = v___x_738_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_744_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_744_, 0, v___x_741_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_744_, 1, v_snd_736_);
                    v___x_743_ = v_reuseFailAlloc_744_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_743_;
            }
            5 => {
                v___x_760_ = leanh::lean_box(0);
                if v_isShared_759_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_758_, 1);
                    v___x_762_ = v___x_758_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_766_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_766_, 0, v_a_756_);
                    v___x_762_ = v_reuseFailAlloc_766_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                v___x_763_ = leanh::lean_box((v___x_749_) as usize);
                v___x_764_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_764_, 0, v___x_762_);
                leanh::lean_ctor_set(v___x_764_, 1, v___x_763_);
                v___x_765_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_765_, 0, v___x_760_);
                leanh::lean_ctor_set(v___x_765_, 1, v___x_764_);
                return v___x_765_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_IO_AsyncList_getFinishedPrefix___redArg___boxed(
    mut v_x_771_: *mut leanh::LeanObject,
    mut v_a_772_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_773_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_773_ = l_IO_AsyncList_getFinishedPrefix___redArg(v_x_771_);
    return v_res_773_;
}
pub unsafe fn l_IO_AsyncList_getFinishedPrefix(
    mut v_00_u03b5_774_: *mut leanh::LeanObject,
    mut v_00_u03b1_775_: *mut leanh::LeanObject,
    mut v_x_776_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_778_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_778_ = l_IO_AsyncList_getFinishedPrefix___redArg(v_x_776_);
    return v___x_778_;
}
pub unsafe fn l_IO_AsyncList_getFinishedPrefix___boxed(
    mut v_00_u03b5_779_: *mut leanh::LeanObject,
    mut v_00_u03b1_780_: *mut leanh::LeanObject,
    mut v_x_781_: *mut leanh::LeanObject,
    mut v_a_782_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_783_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_783_ = l_IO_AsyncList_getFinishedPrefix(v_00_u03b5_779_, v_00_u03b1_780_, v_x_781_);
    return v_res_783_;
}
pub unsafe fn l___private_Lean_Server_AsyncList_0__IO_AsyncList_getFinishedPrefixWithTimeout_go___redArg___lam__0(
    mut v_val_784_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_785_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_785_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_785_, 0, v_val_784_);
    return v___x_785_;
}
pub unsafe fn l_List_mapTR_loop___at___00__private_Lean_Server_AsyncList_0__IO_AsyncList_getFinishedPrefixWithTimeout_go_spec__0___redArg___lam__0(
    mut v_val_786_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_787_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_787_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_787_, 0, v_val_786_);
    return v___x_787_;
}
pub unsafe fn l_List_mapTR_loop___at___00__private_Lean_Server_AsyncList_0__IO_AsyncList_getFinishedPrefixWithTimeout_go_spec__0___redArg(
    mut v_a_789_: *mut leanh::LeanObject,
    mut v_a_790_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_791_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_head_792_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_793_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_795_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_796_: u8 = 0;
    let mut v___f_797_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_798_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_800_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_802_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_803_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_a_789_) == 0 {
                    v___x_791_ = l_List_reverse___redArg(v_a_790_);
                    return v___x_791_;
                } else {
                    v_head_792_ = leanh::lean_ctor_get(v_a_789_, 0);
                    v_tail_793_ = leanh::lean_ctor_get(v_a_789_, 1);
                    v_isSharedCheck_803_ = (!leanh::lean_is_exclusive(v_a_789_)) as u8;
                    if v_isSharedCheck_803_ == 0 {
                        v___x_795_ = v_a_789_;
                        v_isShared_796_ = v_isSharedCheck_803_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_tail_793_);
                        leanh::lean_inc(v_head_792_);
                        leanh::lean_dec(v_a_789_);
                        v___x_795_ = leanh::lean_box(0);
                        v_isShared_796_ = v_isSharedCheck_803_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___f_797_ = l_List_mapTR_loop___at___00__private_Lean_Server_AsyncList_0__IO_AsyncList_getFinishedPrefixWithTimeout_go_spec__0___redArg___closed__0;
                v___x_798_ = l_Lean_Server_ServerTask_mapCheap___redArg(v___f_797_, v_head_792_);
                if v_isShared_796_ == 0 {
                    leanh::lean_ctor_set(v___x_795_, 1, v_a_790_);
                    leanh::lean_ctor_set(v___x_795_, 0, v___x_798_);
                    v___x_800_ = v___x_795_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_802_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_802_, 0, v___x_798_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_802_, 1, v_a_790_);
                    v___x_800_ = v_reuseFailAlloc_802_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v_a_789_ = v_tail_793_;
                v_a_790_ = v___x_800_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Server_AsyncList_0__IO_AsyncList_getFinishedPrefixWithTimeout_go___redArg(
    mut v_cancelTks_805_: *mut leanh::LeanObject,
    mut v_timeoutTask_806_: *mut leanh::LeanObject,
    mut v_xs_807_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_hd_809_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tl_810_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_812_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_813_: u8 = 0;
    let mut v___x_814_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_815_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_816_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_818_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_819_: u8 = 0;
    let mut v___x_821_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_823_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_824_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_825_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_826_: u8 = 0;
    let mut v_isSharedCheck_827_: u8 = 0;
    let mut v_tl_828_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_829_: u8 = 0;
    let mut v___x_830_: u8 = 0;
    let mut v___f_831_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_832_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_833_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_834_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_835_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_836_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_837_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_838_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_839_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_840_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_841_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_842_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_843_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_844_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_846_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_847_: u8 = 0;
    let mut v___x_849_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_850_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_851_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_852_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_853_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_854_: u8 = 0;
    let mut v_a_855_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_857_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_858_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_860_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_861_: u8 = 0;
    let mut v___x_862_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_864_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_865_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_866_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_867_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_868_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_869_: u8 = 0;
    let mut v_a_870_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_872_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => match leanh::lean_obj_tag(v_xs_807_) {
                0 => {
                    v_hd_809_ = leanh::lean_ctor_get(v_xs_807_, 0);
                    v_tl_810_ = leanh::lean_ctor_get(v_xs_807_, 1);
                    v_isSharedCheck_827_ = (!leanh::lean_is_exclusive(v_xs_807_)) as u8;
                    if v_isSharedCheck_827_ == 0 {
                        v___x_812_ = v_xs_807_;
                        v_isShared_813_ = v_isSharedCheck_827_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_tl_810_);
                        leanh::lean_inc(v_hd_809_);
                        leanh::lean_dec(v_xs_807_);
                        v___x_812_ = leanh::lean_box(0);
                        v_isShared_813_ = v_isSharedCheck_827_;
                        state = 1;
                        continue;
                    }
                }
                1 => {
                    v_tl_828_ = leanh::lean_ctor_get(v_xs_807_, 0);
                    leanh::lean_inc_ref(v_tl_828_);
                    leanh::lean_dec_ref_known(v_xs_807_, 1);
                    v___x_829_ = l_Lean_Server_ServerTask_hasFinished___redArg(v_tl_828_);
                    v___x_830_ = 1;
                    if v___x_829_ == 0 {
                        v___f_831_ = l___private_Lean_Server_AsyncList_0__IO_AsyncList_getFinishedPrefixWithTimeout_go___redArg___closed__0;
                        v___x_832_ =
                            l_Lean_Server_ServerTask_mapCheap___redArg(v___f_831_, v_tl_828_);
                        v___x_833_ = leanh::lean_box(0);
                        leanh::lean_inc(v_cancelTks_805_);
                        v___x_834_ = l_List_mapTR_loop___at___00__private_Lean_Server_AsyncList_0__IO_AsyncList_getFinishedPrefixWithTimeout_go_spec__0___redArg(v_cancelTks_805_, v___x_833_);
                        v___x_835_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                        leanh::lean_ctor_set(v___x_835_, 0, v___x_832_);
                        leanh::lean_ctor_set(v___x_835_, 1, v___x_834_);
                        leanh::lean_inc_ref(v_timeoutTask_806_);
                        v___x_836_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                        leanh::lean_ctor_set(v___x_836_, 0, v_timeoutTask_806_);
                        leanh::lean_ctor_set(v___x_836_, 1, v___x_833_);
                        v___x_837_ = l_List_appendTR___redArg(v___x_835_, v___x_836_);
                        v___x_838_ = l_Lean_Server_ServerTask_waitAny___redArg(v___x_837_);
                        if leanh::lean_obj_tag(v___x_838_) == 0 {
                            leanh::lean_dec_ref_known(v___x_838_, 1);
                            leanh::lean_dec_ref(v_timeoutTask_806_);
                            leanh::lean_dec(v_cancelTks_805_);
                            v___x_839_ = leanh::lean_box(0);
                            v___x_840_ = leanh::lean_box((v___x_829_) as usize);
                            v___x_841_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                            leanh::lean_ctor_set(v___x_841_, 0, v___x_839_);
                            leanh::lean_ctor_set(v___x_841_, 1, v___x_840_);
                            v___x_842_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                            leanh::lean_ctor_set(v___x_842_, 0, v___x_833_);
                            leanh::lean_ctor_set(v___x_842_, 1, v___x_841_);
                            return v___x_842_;
                        } else {
                            v_val_843_ = leanh::lean_ctor_get(v___x_838_, 0);
                            leanh::lean_inc(v_val_843_);
                            leanh::lean_dec_ref_known(v___x_838_, 1);
                            if leanh::lean_obj_tag(v_val_843_) == 0 {
                                leanh::lean_dec_ref(v_timeoutTask_806_);
                                leanh::lean_dec(v_cancelTks_805_);
                                v_a_844_ = leanh::lean_ctor_get(v_val_843_, 0);
                                v_isSharedCheck_854_ =
                                    (!leanh::lean_is_exclusive(v_val_843_)) as u8;
                                if v_isSharedCheck_854_ == 0 {
                                    v___x_846_ = v_val_843_;
                                    v_isShared_847_ = v_isSharedCheck_854_;
                                    state = 5;
                                    continue;
                                } else {
                                    leanh::lean_inc(v_a_844_);
                                    leanh::lean_dec(v_val_843_);
                                    v___x_846_ = leanh::lean_box(0);
                                    v_isShared_847_ = v_isSharedCheck_854_;
                                    state = 5;
                                    continue;
                                }
                            } else {
                                v_a_855_ = leanh::lean_ctor_get(v_val_843_, 0);
                                leanh::lean_inc(v_a_855_);
                                leanh::lean_dec_ref_known(v_val_843_, 1);
                                v_xs_807_ = v_a_855_;
                                state = 0;
                                continue;
                            }
                        }
                    } else {
                        v___x_857_ = lean_io_wait(v_tl_828_);
                        if leanh::lean_obj_tag(v___x_857_) == 0 {
                            leanh::lean_dec_ref(v_timeoutTask_806_);
                            leanh::lean_dec(v_cancelTks_805_);
                            v_a_858_ = leanh::lean_ctor_get(v___x_857_, 0);
                            v_isSharedCheck_869_ =
                                (!leanh::lean_is_exclusive(v___x_857_)) as u8;
                            if v_isSharedCheck_869_ == 0 {
                                v___x_860_ = v___x_857_;
                                v_isShared_861_ = v_isSharedCheck_869_;
                                state = 7;
                                continue;
                            } else {
                                leanh::lean_inc(v_a_858_);
                                leanh::lean_dec(v___x_857_);
                                v___x_860_ = leanh::lean_box(0);
                                v_isShared_861_ = v_isSharedCheck_869_;
                                state = 7;
                                continue;
                            }
                        } else {
                            v_a_870_ = leanh::lean_ctor_get(v___x_857_, 0);
                            leanh::lean_inc(v_a_870_);
                            leanh::lean_dec_ref_known(v___x_857_, 1);
                            v_xs_807_ = v_a_870_;
                            state = 0;
                            continue;
                        }
                    }
                }
                _ => {
                    leanh::lean_dec_ref(v_timeoutTask_806_);
                    leanh::lean_dec(v_cancelTks_805_);
                    v___x_872_ = l_IO_AsyncList_getFinishedPrefix___redArg___closed__1;
                    return v___x_872_;
                }
            },
            1 => {
                v___x_814_ = l___private_Lean_Server_AsyncList_0__IO_AsyncList_getFinishedPrefixWithTimeout_go___redArg(v_cancelTks_805_, v_timeoutTask_806_, v_tl_810_);
                v_fst_815_ = leanh::lean_ctor_get(v___x_814_, 0);
                v_snd_816_ = leanh::lean_ctor_get(v___x_814_, 1);
                v_isSharedCheck_826_ = (!leanh::lean_is_exclusive(v___x_814_)) as u8;
                if v_isSharedCheck_826_ == 0 {
                    v___x_818_ = v___x_814_;
                    v_isShared_819_ = v_isSharedCheck_826_;
                    state = 2;
                    continue;
                } else {
                    leanh::lean_inc(v_snd_816_);
                    leanh::lean_inc(v_fst_815_);
                    leanh::lean_dec(v___x_814_);
                    v___x_818_ = leanh::lean_box(0);
                    v_isShared_819_ = v_isSharedCheck_826_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                if v_isShared_813_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_812_, 1);
                    leanh::lean_ctor_set(v___x_812_, 1, v_fst_815_);
                    v___x_821_ = v___x_812_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_825_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_825_, 0, v_hd_809_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_825_, 1, v_fst_815_);
                    v___x_821_ = v_reuseFailAlloc_825_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_819_ == 0 {
                    leanh::lean_ctor_set(v___x_818_, 0, v___x_821_);
                    v___x_823_ = v___x_818_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_824_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_824_, 0, v___x_821_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_824_, 1, v_snd_816_);
                    v___x_823_ = v_reuseFailAlloc_824_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_823_;
            }
            5 => {
                if v_isShared_847_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_846_, 1);
                    v___x_849_ = v___x_846_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_853_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_853_, 0, v_a_844_);
                    v___x_849_ = v_reuseFailAlloc_853_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                v___x_850_ = leanh::lean_box((v___x_830_) as usize);
                v___x_851_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_851_, 0, v___x_849_);
                leanh::lean_ctor_set(v___x_851_, 1, v___x_850_);
                v___x_852_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_852_, 0, v___x_833_);
                leanh::lean_ctor_set(v___x_852_, 1, v___x_851_);
                return v___x_852_;
            }
            7 => {
                v___x_862_ = leanh::lean_box(0);
                if v_isShared_861_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_860_, 1);
                    v___x_864_ = v___x_860_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_868_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_868_, 0, v_a_858_);
                    v___x_864_ = v_reuseFailAlloc_868_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                v___x_865_ = leanh::lean_box((v___x_830_) as usize);
                v___x_866_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_866_, 0, v___x_864_);
                leanh::lean_ctor_set(v___x_866_, 1, v___x_865_);
                v___x_867_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_867_, 0, v___x_862_);
                leanh::lean_ctor_set(v___x_867_, 1, v___x_866_);
                return v___x_867_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Server_AsyncList_0__IO_AsyncList_getFinishedPrefixWithTimeout_go___redArg___boxed(
    mut v_cancelTks_873_: *mut leanh::LeanObject,
    mut v_timeoutTask_874_: *mut leanh::LeanObject,
    mut v_xs_875_: *mut leanh::LeanObject,
    mut v_a_876_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_877_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_877_ =
        l___private_Lean_Server_AsyncList_0__IO_AsyncList_getFinishedPrefixWithTimeout_go___redArg(
            v_cancelTks_873_,
            v_timeoutTask_874_,
            v_xs_875_,
        );
    return v_res_877_;
}
pub unsafe fn l___private_Lean_Server_AsyncList_0__IO_AsyncList_getFinishedPrefixWithTimeout_go(
    mut v_00_u03b5_878_: *mut leanh::LeanObject,
    mut v_00_u03b1_879_: *mut leanh::LeanObject,
    mut v_cancelTks_880_: *mut leanh::LeanObject,
    mut v_timeoutTask_881_: *mut leanh::LeanObject,
    mut v_xs_882_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_884_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_884_ =
        l___private_Lean_Server_AsyncList_0__IO_AsyncList_getFinishedPrefixWithTimeout_go___redArg(
            v_cancelTks_880_,
            v_timeoutTask_881_,
            v_xs_882_,
        );
    return v___x_884_;
}
pub unsafe fn l___private_Lean_Server_AsyncList_0__IO_AsyncList_getFinishedPrefixWithTimeout_go___boxed(
    mut v_00_u03b5_885_: *mut leanh::LeanObject,
    mut v_00_u03b1_886_: *mut leanh::LeanObject,
    mut v_cancelTks_887_: *mut leanh::LeanObject,
    mut v_timeoutTask_888_: *mut leanh::LeanObject,
    mut v_xs_889_: *mut leanh::LeanObject,
    mut v_a_890_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_891_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_891_ = l___private_Lean_Server_AsyncList_0__IO_AsyncList_getFinishedPrefixWithTimeout_go(
        v_00_u03b5_885_,
        v_00_u03b1_886_,
        v_cancelTks_887_,
        v_timeoutTask_888_,
        v_xs_889_,
    );
    return v_res_891_;
}
pub unsafe fn l_List_mapTR_loop___at___00__private_Lean_Server_AsyncList_0__IO_AsyncList_getFinishedPrefixWithTimeout_go_spec__0(
    mut v_00_u03b5_892_: *mut leanh::LeanObject,
    mut v_00_u03b1_893_: *mut leanh::LeanObject,
    mut v_a_894_: *mut leanh::LeanObject,
    mut v_a_895_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_896_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_896_ = l_List_mapTR_loop___at___00__private_Lean_Server_AsyncList_0__IO_AsyncList_getFinishedPrefixWithTimeout_go_spec__0___redArg(v_a_894_, v_a_895_);
    return v___x_896_;
}
pub unsafe fn l_IO_AsyncList_getFinishedPrefixWithTimeout___redArg___lam__0(
    mut v_timeoutMs_899_: u32,
) -> *mut leanh::LeanObject {
    let mut v___x_901_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_902_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_901_ = l_IO_sleep(v_timeoutMs_899_);
    v___x_902_ = l_IO_AsyncList_getFinishedPrefixWithTimeout___redArg___lam__0___closed__0;
    return v___x_902_;
}
pub unsafe fn l_IO_AsyncList_getFinishedPrefixWithTimeout___redArg___lam__0___boxed(
    mut v_timeoutMs_903_: *mut leanh::LeanObject,
    mut v___y_904_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_timeoutMs_boxed_905_: u32 = 0;
    let mut v_res_906_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_timeoutMs_boxed_905_ = leanh::lean_unbox_uint32(v_timeoutMs_903_);
    leanh::lean_dec(v_timeoutMs_903_);
    v_res_906_ =
        l_IO_AsyncList_getFinishedPrefixWithTimeout___redArg___lam__0(v_timeoutMs_boxed_905_);
    return v_res_906_;
}
pub unsafe fn _init_l_IO_AsyncList_getFinishedPrefixWithTimeout___redArg___closed__0()
-> *mut leanh::LeanObject {
    let mut v___x_907_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_908_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_907_ = l_IO_AsyncList_getFinishedPrefixWithTimeout___redArg___lam__0___closed__0;
    v___x_908_ = lean_task_pure(v___x_907_);
    return v___x_908_;
}
pub unsafe fn l_IO_AsyncList_getFinishedPrefixWithTimeout___redArg(
    mut v_xs_909_: *mut leanh::LeanObject,
    mut v_timeoutMs_910_: u32,
    mut v_cancelTks_911_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_913_: u32 = 0;
    let mut v___x_914_: u8 = 0;
    v___x_913_ = 0;
    v___x_914_ = lean_uint32_dec_eq(v_timeoutMs_910_, v___x_913_);
    if v___x_914_ == 0 {
        let mut v___x_915_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___f_916_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_917_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_918_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_915_ = leanh::lean_box_uint32(v_timeoutMs_910_);
        v___f_916_ = leanh::lean_alloc_closure(
            l_IO_AsyncList_getFinishedPrefixWithTimeout___redArg___lam__0___boxed
                as *mut core::ffi::c_void,
            2,
            1,
        );
        leanh::lean_closure_set(v___f_916_, 0, v___x_915_);
        v___x_917_ = l_Lean_Server_ServerTask_BaseIO_asTask___redArg(v___f_916_);
        v___x_918_ = l___private_Lean_Server_AsyncList_0__IO_AsyncList_getFinishedPrefixWithTimeout_go___redArg(v_cancelTks_911_, v___x_917_, v_xs_909_);
        return v___x_918_;
    } else {
        let mut v___x_919_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_920_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_919_ = leanh::lean_obj_once(
            core::ptr::addr_of_mut!(
                l_IO_AsyncList_getFinishedPrefixWithTimeout___redArg___closed__0
            ),
            core::ptr::addr_of_mut!(
                l_IO_AsyncList_getFinishedPrefixWithTimeout___redArg___closed__0_once
            ),
            _init_l_IO_AsyncList_getFinishedPrefixWithTimeout___redArg___closed__0,
        );
        v___x_920_ = l___private_Lean_Server_AsyncList_0__IO_AsyncList_getFinishedPrefixWithTimeout_go___redArg(v_cancelTks_911_, v___x_919_, v_xs_909_);
        return v___x_920_;
    }
}
pub unsafe fn l_IO_AsyncList_getFinishedPrefixWithTimeout___redArg___boxed(
    mut v_xs_921_: *mut leanh::LeanObject,
    mut v_timeoutMs_922_: *mut leanh::LeanObject,
    mut v_cancelTks_923_: *mut leanh::LeanObject,
    mut v_a_924_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_timeoutMs_boxed_925_: u32 = 0;
    let mut v_res_926_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_timeoutMs_boxed_925_ = leanh::lean_unbox_uint32(v_timeoutMs_922_);
    leanh::lean_dec(v_timeoutMs_922_);
    v_res_926_ = l_IO_AsyncList_getFinishedPrefixWithTimeout___redArg(
        v_xs_921_,
        v_timeoutMs_boxed_925_,
        v_cancelTks_923_,
    );
    return v_res_926_;
}
pub unsafe fn l_IO_AsyncList_getFinishedPrefixWithTimeout(
    mut v_00_u03b5_927_: *mut leanh::LeanObject,
    mut v_00_u03b1_928_: *mut leanh::LeanObject,
    mut v_xs_929_: *mut leanh::LeanObject,
    mut v_timeoutMs_930_: u32,
    mut v_cancelTks_931_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_933_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_933_ = l_IO_AsyncList_getFinishedPrefixWithTimeout___redArg(
        v_xs_929_,
        v_timeoutMs_930_,
        v_cancelTks_931_,
    );
    return v___x_933_;
}
pub unsafe fn l_IO_AsyncList_getFinishedPrefixWithTimeout___boxed(
    mut v_00_u03b5_934_: *mut leanh::LeanObject,
    mut v_00_u03b1_935_: *mut leanh::LeanObject,
    mut v_xs_936_: *mut leanh::LeanObject,
    mut v_timeoutMs_937_: *mut leanh::LeanObject,
    mut v_cancelTks_938_: *mut leanh::LeanObject,
    mut v_a_939_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_timeoutMs_boxed_940_: u32 = 0;
    let mut v_res_941_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_timeoutMs_boxed_940_ = leanh::lean_unbox_uint32(v_timeoutMs_937_);
    leanh::lean_dec(v_timeoutMs_937_);
    v_res_941_ = l_IO_AsyncList_getFinishedPrefixWithTimeout(
        v_00_u03b5_934_,
        v_00_u03b1_935_,
        v_xs_936_,
        v_timeoutMs_boxed_940_,
        v_cancelTks_938_,
    );
    return v_res_941_;
}
pub unsafe fn l_List_anyM___at___00__private_Lean_Server_AsyncList_0__IO_AsyncList_getFinishedPrefixWithConsistentLatency_sleepWithCancellation_spec__0(
    mut v_x_942_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_944_: u8 = 0;
    let mut v_head_945_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_946_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_947_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_942_) == 0 {
                    v___x_944_ = 0;
                    return v___x_944_;
                } else {
                    v_head_945_ = leanh::lean_ctor_get(v_x_942_, 0);
                    v_tail_946_ = leanh::lean_ctor_get(v_x_942_, 1);
                    v___x_947_ = l_Lean_Server_ServerTask_hasFinished___redArg(v_head_945_);
                    if v___x_947_ == 0 {
                        v_x_942_ = v_tail_946_;
                        state = 0;
                        continue;
                    } else {
                        return v___x_947_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_anyM___at___00__private_Lean_Server_AsyncList_0__IO_AsyncList_getFinishedPrefixWithConsistentLatency_sleepWithCancellation_spec__0___boxed(
    mut v_x_949_: *mut leanh::LeanObject,
    mut v___y_950_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_951_: u8 = 0;
    let mut v_r_952_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_951_ = l_List_anyM___at___00__private_Lean_Server_AsyncList_0__IO_AsyncList_getFinishedPrefixWithConsistentLatency_sleepWithCancellation_spec__0(v_x_949_);
    leanh::lean_dec(v_x_949_);
    v_r_952_ = leanh::lean_box((v_res_951_) as usize);
    return v_r_952_;
}
pub unsafe fn l___private_Lean_Server_AsyncList_0__IO_AsyncList_getFinishedPrefixWithConsistentLatency_sleepWithCancellation(
    mut v_cancelTks_953_: *mut leanh::LeanObject,
    mut v_sleepDurationMs_954_: u32,
) -> *mut leanh::LeanObject {
    let mut v___x_956_: u32 = 0;
    let mut v___x_957_: u8 = 0;
    v___x_956_ = 0;
    v___x_957_ = lean_uint32_dec_eq(v_sleepDurationMs_954_, v___x_956_);
    if v___x_957_ == 0 {
        let mut v___x_958_: u8 = 0;
        v___x_958_ = l_List_isEmpty___redArg(v_cancelTks_953_);
        if v___x_958_ == 0 {
            let mut v___x_959_: u8 = 0;
            v___x_959_ = l_List_anyM___at___00__private_Lean_Server_AsyncList_0__IO_AsyncList_getFinishedPrefixWithConsistentLatency_sleepWithCancellation_spec__0(v_cancelTks_953_);
            if v___x_959_ == 0 {
                let mut v___x_960_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_961_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_962_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_963_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_964_: *mut leanh::LeanObject = core::ptr::null_mut();
                v___x_960_ = leanh::lean_box_uint32(v_sleepDurationMs_954_);
                v___x_961_ = leanh::lean_alloc_closure(
                    l_IO_sleep___boxed as *mut core::ffi::c_void,
                    2,
                    1,
                );
                leanh::lean_closure_set(v___x_961_, 0, v___x_960_);
                v___x_962_ = l_Lean_Server_ServerTask_BaseIO_asTask___redArg(v___x_961_);
                v___x_963_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_963_, 0, v___x_962_);
                leanh::lean_ctor_set(v___x_963_, 1, v_cancelTks_953_);
                v___x_964_ = l_Lean_Server_ServerTask_waitAny___redArg(v___x_963_);
                return v___x_964_;
            } else {
                let mut v___x_965_: *mut leanh::LeanObject = core::ptr::null_mut();
                leanh::lean_dec(v_cancelTks_953_);
                v___x_965_ = leanh::lean_box(0);
                return v___x_965_;
            }
        } else {
            let mut v___x_966_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_967_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_cancelTks_953_);
            v___x_966_ = l_IO_sleep(v_sleepDurationMs_954_);
            v___x_967_ = leanh::lean_box(0);
            return v___x_967_;
        }
    } else {
        let mut v___x_968_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_cancelTks_953_);
        v___x_968_ = leanh::lean_box(0);
        return v___x_968_;
    }
}
pub unsafe fn l___private_Lean_Server_AsyncList_0__IO_AsyncList_getFinishedPrefixWithConsistentLatency_sleepWithCancellation___boxed(
    mut v_cancelTks_969_: *mut leanh::LeanObject,
    mut v_sleepDurationMs_970_: *mut leanh::LeanObject,
    mut v_a_971_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_sleepDurationMs_boxed_972_: u32 = 0;
    let mut v_res_973_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_sleepDurationMs_boxed_972_ = leanh::lean_unbox_uint32(v_sleepDurationMs_970_);
    leanh::lean_dec(v_sleepDurationMs_970_);
    v_res_973_ = l___private_Lean_Server_AsyncList_0__IO_AsyncList_getFinishedPrefixWithConsistentLatency_sleepWithCancellation(v_cancelTks_969_, v_sleepDurationMs_boxed_972_);
    return v_res_973_;
}
pub unsafe fn l_IO_AsyncList_getFinishedPrefixWithConsistentLatency___redArg(
    mut v_xs_974_: *mut leanh::LeanObject,
    mut v_latencyMs_975_: u32,
    mut v_cancelTks_976_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_978_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_979_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_980_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_981_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_982_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_983_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_984_: u32 = 0;
    let mut v___x_985_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_978_ = lean_io_mono_ms_now();
    leanh::lean_inc(v_cancelTks_976_);
    v___x_979_ = l_IO_AsyncList_getFinishedPrefixWithTimeout___redArg(
        v_xs_974_,
        v_latencyMs_975_,
        v_cancelTks_976_,
    );
    v___x_980_ = lean_io_mono_ms_now();
    v___x_981_ = lean_nat_sub(v___x_980_, v___x_978_);
    leanh::lean_dec(v___x_978_);
    leanh::lean_dec(v___x_980_);
    v___x_982_ = lean_uint32_to_nat(v_latencyMs_975_);
    v___x_983_ = lean_nat_sub(v___x_982_, v___x_981_);
    leanh::lean_dec(v___x_981_);
    leanh::lean_dec(v___x_982_);
    v___x_984_ = lean_uint32_of_nat(v___x_983_);
    leanh::lean_dec(v___x_983_);
    v___x_985_ = l___private_Lean_Server_AsyncList_0__IO_AsyncList_getFinishedPrefixWithConsistentLatency_sleepWithCancellation(v_cancelTks_976_, v___x_984_);
    return v___x_979_;
}
pub unsafe fn l_IO_AsyncList_getFinishedPrefixWithConsistentLatency___redArg___boxed(
    mut v_xs_986_: *mut leanh::LeanObject,
    mut v_latencyMs_987_: *mut leanh::LeanObject,
    mut v_cancelTks_988_: *mut leanh::LeanObject,
    mut v_a_989_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_latencyMs_boxed_990_: u32 = 0;
    let mut v_res_991_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_latencyMs_boxed_990_ = leanh::lean_unbox_uint32(v_latencyMs_987_);
    leanh::lean_dec(v_latencyMs_987_);
    v_res_991_ = l_IO_AsyncList_getFinishedPrefixWithConsistentLatency___redArg(
        v_xs_986_,
        v_latencyMs_boxed_990_,
        v_cancelTks_988_,
    );
    return v_res_991_;
}
pub unsafe fn l_IO_AsyncList_getFinishedPrefixWithConsistentLatency(
    mut v_00_u03b5_992_: *mut leanh::LeanObject,
    mut v_00_u03b1_993_: *mut leanh::LeanObject,
    mut v_xs_994_: *mut leanh::LeanObject,
    mut v_latencyMs_995_: u32,
    mut v_cancelTks_996_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_998_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_998_ = l_IO_AsyncList_getFinishedPrefixWithConsistentLatency___redArg(
        v_xs_994_,
        v_latencyMs_995_,
        v_cancelTks_996_,
    );
    return v___x_998_;
}
pub unsafe fn l_IO_AsyncList_getFinishedPrefixWithConsistentLatency___boxed(
    mut v_00_u03b5_999_: *mut leanh::LeanObject,
    mut v_00_u03b1_1000_: *mut leanh::LeanObject,
    mut v_xs_1001_: *mut leanh::LeanObject,
    mut v_latencyMs_1002_: *mut leanh::LeanObject,
    mut v_cancelTks_1003_: *mut leanh::LeanObject,
    mut v_a_1004_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_latencyMs_boxed_1005_: u32 = 0;
    let mut v_res_1006_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_latencyMs_boxed_1005_ = leanh::lean_unbox_uint32(v_latencyMs_1002_);
    leanh::lean_dec(v_latencyMs_1002_);
    v_res_1006_ = l_IO_AsyncList_getFinishedPrefixWithConsistentLatency(
        v_00_u03b5_999_,
        v_00_u03b1_1000_,
        v_xs_1001_,
        v_latencyMs_boxed_1005_,
        v_cancelTks_1003_,
    );
    return v_res_1006_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Server_AsyncList(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Server_ServerTask(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Server_AsyncList(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_meta_initialized = true;
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lean_Server_AsyncList(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Server_ServerTask(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Server_AsyncList(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_Server_AsyncList(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return initialize_Lean_Server_AsyncList(builtin);
}