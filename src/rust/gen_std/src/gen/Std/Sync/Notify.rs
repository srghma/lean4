// Lean compiler output
// Module: Std.Sync.Notify
// Imports: Init.Data.Queue Std.Sync.Mutex Std.Async.Select
use crate::ffi::{
    lean_io_basemutex_lock, lean_io_basemutex_unlock, lean_io_bind_task, lean_io_promise_new,
    lean_io_promise_resolve, lean_io_promise_result_opt, lean_st_ref_get, lean_st_ref_set,
    lean_st_ref_take, lean_task_map, lean_task_pure,
};
use crate::r#gen::Init::Data::List::Basic::{l_List_isEmpty___redArg, l_List_reverse___redArg};
use crate::r#gen::Init::Data::Queue::{
    initialize_Init_Data_Queue, l_Std_Queue_dequeue_x3f___redArg, l_Std_Queue_empty,
    l_Std_Queue_enqueue___redArg, runtime_initialize_Init_Data_Queue,
};
use crate::r#gen::Init::System::IOError::lean_mk_io_user_error;
use crate::r#gen::Std::Async::Basic::{
    l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask,
    l_Std_Async_EAsync_tryFinally_x27___redArg,
};
use crate::r#gen::Std::Async::Select::{
    initialize_Std_Async_Select, runtime_initialize_Std_Async_Select,
};
use crate::r#gen::Std::Sync::Mutex::{
    initialize_Std_Sync_Mutex, l_Std_Mutex_new___redArg, runtime_initialize_Std_Sync_Mutex,
};
pub static l_Std_Notify_Consumer_resolve___redArg___closed__0_value:
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
    m_fun: l_Std_Notify_Consumer_resolve___redArg___lam__0___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 1,
    m_objs: [(((0 as usize) << 1) | 1) as *mut leanh::LeanObject],
};
static mut l_Std_Notify_Consumer_resolve___redArg___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Notify_Consumer_resolve___redArg___closed__0_value)
        as *mut leanh::LeanObject;
static mut l_Std_Notify_new___closed__0_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Notify_new___closed__0: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Std_Notify_notify___closed__0_value: leanh::LeanClosureObject<0> =
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
        m_fun: l_Std_Notify_notify___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Std_Notify_notify___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Notify_notify___closed__0_value) as *mut leanh::LeanObject;
pub static l_Std_Notify_notifyOne___closed__0_value: leanh::LeanClosureObject<0> =
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
        m_fun: l_Std_Notify_notifyOne___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Std_Notify_notifyOne___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Notify_notifyOne___closed__0_value) as *mut leanh::LeanObject;
pub static l_Std_Notify_wait___lam__0___closed__0_value: leanh::LeanStringObject<15> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 15,
        m_capacity: 15,
        m_length: 14,
        m_data: [
            110, 111, 116, 105, 102, 121, 32, 100, 114, 111, 112, 112, 101, 100, 0,
        ],
    };
static mut l_Std_Notify_wait___lam__0___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Notify_wait___lam__0___closed__0_value)
        as *mut leanh::LeanObject;
static mut l_Std_Notify_wait___lam__0___closed__1_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Notify_wait___lam__0___closed__1: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_Notify_wait___lam__0___closed__2_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Notify_wait___lam__0___closed__2: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_Notify_wait___lam__0___closed__3_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Notify_wait___lam__0___closed__3: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Std_Notify_wait___closed__0_value: leanh::LeanClosureObject<0> =
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
        m_fun: l_Std_Notify_wait___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Std_Notify_wait___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Notify_wait___closed__0_value) as *mut leanh::LeanObject;
pub static l_Std_Notify_wait___closed__1_value: leanh::LeanClosureObject<1> =
    leanh::LeanClosureObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut leanh::LeanObject>() * 1)
                as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Std_Notify_wait___lam__1___boxed as *const core::ffi::c_void,
        m_arity: 3,
        m_num_fixed: 1,
        m_objs: [core::ptr::addr_of!(l_Std_Notify_wait___closed__0_value)
            as *mut leanh::LeanObject],
    };
static mut l_Std_Notify_wait___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Notify_wait___closed__1_value) as *mut leanh::LeanObject;
pub static l_Std_Mutex_atomically___at___00Std_Notify_selector_spec__0___redArg___closed__0_value: leanh::LeanClosureObject<0> = leanh::LeanClosureObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Std_Mutex_atomically___at___00Std_Notify_selector_spec__0___redArg___lam__3 as *const core::ffi::c_void, m_arity: 1, m_num_fixed: 0, m_objs: [] };
static mut l_Std_Mutex_atomically___at___00Std_Notify_selector_spec__0___redArg___closed__0:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Std_Mutex_atomically___at___00Std_Notify_selector_spec__0___redArg___closed__0_value
) as *mut leanh::LeanObject;
pub static l_List_filterAuxM___at___00Std_Queue_filterM___at___00Std_Notify_selector_spec__1_spec__1___redArg___closed__0_value: leanh::LeanCtorObject<1> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 1 }, m_objs: [((( 1 as usize) << 1) | 1) as *mut leanh::LeanObject] };
static mut l_List_filterAuxM___at___00Std_Queue_filterM___at___00Std_Notify_selector_spec__1_spec__1___redArg___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l_List_filterAuxM___at___00Std_Queue_filterM___at___00Std_Notify_selector_spec__1_spec__1___redArg___closed__0_value) as *mut leanh::LeanObject;
pub static l_List_filterAuxM___at___00Std_Queue_filterM___at___00Std_Notify_selector_spec__1_spec__1___redArg___closed__1_value: leanh::LeanCtorObject<1> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 0 }, m_objs: [core::ptr::addr_of!(l_List_filterAuxM___at___00Std_Queue_filterM___at___00Std_Notify_selector_spec__1_spec__1___redArg___closed__0_value) as *mut leanh::LeanObject] };
static mut l_List_filterAuxM___at___00Std_Queue_filterM___at___00Std_Notify_selector_spec__1_spec__1___redArg___closed__1: *mut leanh::LeanObject = core::ptr::addr_of!(l_List_filterAuxM___at___00Std_Queue_filterM___at___00Std_Notify_selector_spec__1_spec__1___redArg___closed__1_value) as *mut leanh::LeanObject;
pub static l_List_filterAuxM___at___00Std_Queue_filterM___at___00Std_Notify_selector_spec__1_spec__1___redArg___closed__2_value: leanh::LeanClosureObject<0> = leanh::LeanClosureObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_List_filterAuxM___at___00Std_Queue_filterM___at___00Std_Notify_selector_spec__1_spec__1___redArg___lam__1___boxed as *const core::ffi::c_void, m_arity: 2, m_num_fixed: 0, m_objs: [] };
static mut l_List_filterAuxM___at___00Std_Queue_filterM___at___00Std_Notify_selector_spec__1_spec__1___redArg___closed__2: *mut leanh::LeanObject = core::ptr::addr_of!(l_List_filterAuxM___at___00Std_Queue_filterM___at___00Std_Notify_selector_spec__1_spec__1___redArg___closed__2_value) as *mut leanh::LeanObject;
pub static l_Std_Queue_filterM___at___00Std_Notify_selector_spec__1___closed__0_value:
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
    m_fun: l_Std_Queue_filterM___at___00Std_Notify_selector_spec__1___lam__0___boxed
        as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_Queue_filterM___at___00Std_Notify_selector_spec__1___closed__0:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Queue_filterM___at___00Std_Notify_selector_spec__1___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Std_Notify_selector___lam__3___closed__0_value: leanh::LeanCtorObject<1> =
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
static mut l_Std_Notify_selector___lam__3___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Notify_selector___lam__3___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Std_Notify_selector___lam__3___closed__1_value: leanh::LeanCtorObject<1> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 0,
        },
        m_objs: [
            core::ptr::addr_of!(l_Std_Notify_selector___lam__3___closed__0_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Std_Notify_selector___lam__3___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Notify_selector___lam__3___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Std_Notify_selector___closed__0_value: leanh::LeanClosureObject<0> =
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
        m_fun: l_Std_Notify_selector___lam__2___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Std_Notify_selector___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Notify_selector___closed__0_value) as *mut leanh::LeanObject;
pub static l_Std_Notify_selector___closed__1_value: leanh::LeanClosureObject<1> =
    leanh::LeanClosureObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut leanh::LeanObject>() * 1)
                as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Std_Notify_selector___lam__5___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 1,
        m_objs: [(((0 as usize) << 1) | 1) as *mut leanh::LeanObject],
    };
static mut l_Std_Notify_selector___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Notify_selector___closed__1_value) as *mut leanh::LeanObject;
pub unsafe fn l_Std_Notify_Consumer_ctorIdx___redArg(
    mut v_x_714_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_x_714_) == 0 {
        let mut v___x_715_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_715_ = leanh::lean_unsigned_to_nat(0);
        return v___x_715_;
    } else {
        let mut v___x_716_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_716_ = leanh::lean_unsigned_to_nat(1);
        return v___x_716_;
    }
}
pub unsafe fn l_Std_Notify_Consumer_ctorIdx___redArg___boxed(
    mut v_x_717_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_718_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_718_ = l_Std_Notify_Consumer_ctorIdx___redArg(v_x_717_);
    leanh::lean_dec_ref(v_x_717_);
    return v_res_718_;
}
pub unsafe fn l_Std_Notify_Consumer_ctorIdx(
    mut v_00_u03b1_719_: *mut leanh::LeanObject,
    mut v_x_720_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_721_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_721_ = l_Std_Notify_Consumer_ctorIdx___redArg(v_x_720_);
    return v___x_721_;
}
pub unsafe fn l_Std_Notify_Consumer_ctorIdx___boxed(
    mut v_00_u03b1_722_: *mut leanh::LeanObject,
    mut v_x_723_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_724_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_724_ = l_Std_Notify_Consumer_ctorIdx(v_00_u03b1_722_, v_x_723_);
    leanh::lean_dec_ref(v_x_723_);
    return v_res_724_;
}
pub unsafe fn l_Std_Notify_Consumer_ctorElim___redArg(
    mut v_t_725_: *mut leanh::LeanObject,
    mut v_k_726_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_t_725_) == 0 {
        let mut v_promise_727_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_728_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_promise_727_ = leanh::lean_ctor_get(v_t_725_, 0);
        leanh::lean_inc(v_promise_727_);
        leanh::lean_dec_ref_known(v_t_725_, 1);
        v___x_728_ = leanh::lean_apply_1(v_k_726_, v_promise_727_);
        return v___x_728_;
    } else {
        let mut v_finished_729_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_730_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_finished_729_ = leanh::lean_ctor_get(v_t_725_, 0);
        leanh::lean_inc_ref(v_finished_729_);
        leanh::lean_dec_ref_known(v_t_725_, 1);
        v___x_730_ = leanh::lean_apply_1(v_k_726_, v_finished_729_);
        return v___x_730_;
    }
}
pub unsafe fn l_Std_Notify_Consumer_ctorElim(
    mut v_00_u03b1_731_: *mut leanh::LeanObject,
    mut v_motive_732_: *mut leanh::LeanObject,
    mut v_ctorIdx_733_: *mut leanh::LeanObject,
    mut v_t_734_: *mut leanh::LeanObject,
    mut v_h_735_: *mut leanh::LeanObject,
    mut v_k_736_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_737_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_737_ = l_Std_Notify_Consumer_ctorElim___redArg(v_t_734_, v_k_736_);
    return v___x_737_;
}
pub unsafe fn l_Std_Notify_Consumer_ctorElim___boxed(
    mut v_00_u03b1_738_: *mut leanh::LeanObject,
    mut v_motive_739_: *mut leanh::LeanObject,
    mut v_ctorIdx_740_: *mut leanh::LeanObject,
    mut v_t_741_: *mut leanh::LeanObject,
    mut v_h_742_: *mut leanh::LeanObject,
    mut v_k_743_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_744_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_744_ = l_Std_Notify_Consumer_ctorElim(
        v_00_u03b1_738_,
        v_motive_739_,
        v_ctorIdx_740_,
        v_t_741_,
        v_h_742_,
        v_k_743_,
    );
    leanh::lean_dec(v_ctorIdx_740_);
    return v_res_744_;
}
pub unsafe fn l_Std_Notify_Consumer_normal_elim___redArg(
    mut v_t_745_: *mut leanh::LeanObject,
    mut v_normal_746_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_747_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_747_ = l_Std_Notify_Consumer_ctorElim___redArg(v_t_745_, v_normal_746_);
    return v___x_747_;
}
pub unsafe fn l_Std_Notify_Consumer_normal_elim(
    mut v_00_u03b1_748_: *mut leanh::LeanObject,
    mut v_motive_749_: *mut leanh::LeanObject,
    mut v_t_750_: *mut leanh::LeanObject,
    mut v_h_751_: *mut leanh::LeanObject,
    mut v_normal_752_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_753_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_753_ = l_Std_Notify_Consumer_ctorElim___redArg(v_t_750_, v_normal_752_);
    return v___x_753_;
}
pub unsafe fn l_Std_Notify_Consumer_select_elim___redArg(
    mut v_t_754_: *mut leanh::LeanObject,
    mut v_select_755_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_756_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_756_ = l_Std_Notify_Consumer_ctorElim___redArg(v_t_754_, v_select_755_);
    return v___x_756_;
}
pub unsafe fn l_Std_Notify_Consumer_select_elim(
    mut v_00_u03b1_757_: *mut leanh::LeanObject,
    mut v_motive_758_: *mut leanh::LeanObject,
    mut v_t_759_: *mut leanh::LeanObject,
    mut v_h_760_: *mut leanh::LeanObject,
    mut v_select_761_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_762_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_762_ = l_Std_Notify_Consumer_ctorElim___redArg(v_t_759_, v_select_761_);
    return v___x_762_;
}
pub unsafe fn l_Std_Async_Waiter_race___at___00Std_Notify_Consumer_resolve_spec__0___redArg(
    mut v_x_763_: *mut leanh::LeanObject,
    mut v_w_764_: *mut leanh::LeanObject,
    mut v_lose_765_: *mut leanh::LeanObject,
) -> u8 {
    let mut v_finished_767_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_promise_768_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_769_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_771_: u8 = 0;
    let mut v___x_772_: u8 = 0;
    let mut v___x_773_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_774_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_775_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_776_: u8 = 0;
    let mut v___x_777_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_778_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_779_: u8 = 0;
    let mut v___x_780_: u8 = 0;
    let mut v___x_781_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_finished_767_ = leanh::lean_ctor_get(v_w_764_, 0);
                v_promise_768_ = leanh::lean_ctor_get(v_w_764_, 1);
                v___x_769_ = lean_st_ref_take(v_finished_767_);
                v___x_779_ = (leanh::lean_unbox(v___x_769_) as u8);
                leanh::lean_dec(v___x_769_);
                if v___x_779_ == 0 {
                    v___x_780_ = 1;
                    v___y_771_ = v___x_780_;
                    state = 1;
                    continue;
                } else {
                    v___x_781_ = 0;
                    v___y_771_ = v___x_781_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_772_ = 1;
                v___x_773_ = leanh::lean_box((v___x_772_) as usize);
                v___x_774_ = lean_st_ref_set(v_finished_767_, v___x_773_);
                if v___y_771_ == 0 {
                    leanh::lean_dec(v_x_763_);
                    v___x_775_ = leanh::lean_apply_1(v_lose_765_, leanh::lean_box(0));
                    v___x_776_ = (leanh::lean_unbox(v___x_775_) as u8);
                    return v___x_776_;
                } else {
                    leanh::lean_dec_ref(v_lose_765_);
                    v___x_777_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_777_, 0, v_x_763_);
                    v___x_778_ = lean_io_promise_resolve(v___x_777_, v_promise_768_);
                    return v___y_771_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Async_Waiter_race___at___00Std_Notify_Consumer_resolve_spec__0___redArg___boxed(
    mut v_x_782_: *mut leanh::LeanObject,
    mut v_w_783_: *mut leanh::LeanObject,
    mut v_lose_784_: *mut leanh::LeanObject,
    mut v___y_785_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_786_: u8 = 0;
    let mut v_r_787_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_786_ = l_Std_Async_Waiter_race___at___00Std_Notify_Consumer_resolve_spec__0___redArg(
        v_x_782_,
        v_w_783_,
        v_lose_784_,
    );
    leanh::lean_dec_ref(v_w_783_);
    v_r_787_ = leanh::lean_box((v_res_786_) as usize);
    return v_r_787_;
}
pub unsafe fn l_Std_Async_Waiter_race___at___00Std_Notify_Consumer_resolve_spec__0(
    mut v_00_u03b1_788_: *mut leanh::LeanObject,
    mut v_x_789_: *mut leanh::LeanObject,
    mut v_w_790_: *mut leanh::LeanObject,
    mut v_lose_791_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_793_: u8 = 0;
    v___x_793_ = l_Std_Async_Waiter_race___at___00Std_Notify_Consumer_resolve_spec__0___redArg(
        v_x_789_,
        v_w_790_,
        v_lose_791_,
    );
    return v___x_793_;
}
pub unsafe fn l_Std_Async_Waiter_race___at___00Std_Notify_Consumer_resolve_spec__0___boxed(
    mut v_00_u03b1_794_: *mut leanh::LeanObject,
    mut v_x_795_: *mut leanh::LeanObject,
    mut v_w_796_: *mut leanh::LeanObject,
    mut v_lose_797_: *mut leanh::LeanObject,
    mut v___y_798_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_799_: u8 = 0;
    let mut v_r_800_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_799_ = l_Std_Async_Waiter_race___at___00Std_Notify_Consumer_resolve_spec__0(
        v_00_u03b1_794_,
        v_x_795_,
        v_w_796_,
        v_lose_797_,
    );
    leanh::lean_dec_ref(v_w_796_);
    v_r_800_ = leanh::lean_box((v_res_799_) as usize);
    return v_r_800_;
}
pub unsafe fn l_Std_Notify_Consumer_resolve___redArg___lam__0(mut v___x_801_: u8) -> u8 {
    return v___x_801_;
}
pub unsafe fn l_Std_Notify_Consumer_resolve___redArg___lam__0___boxed(
    mut v___x_803_: *mut leanh::LeanObject,
    mut v___y_804_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_400__boxed_805_: u8 = 0;
    let mut v_res_806_: u8 = 0;
    let mut v_r_807_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_400__boxed_805_ = (leanh::lean_unbox(v___x_803_) as u8);
    v_res_806_ = l_Std_Notify_Consumer_resolve___redArg___lam__0(v___x_400__boxed_805_);
    v_r_807_ = leanh::lean_box((v_res_806_) as usize);
    return v_r_807_;
}
pub unsafe fn l_Std_Notify_Consumer_resolve___redArg(
    mut v_c_811_: *mut leanh::LeanObject,
    mut v_x_812_: *mut leanh::LeanObject,
) -> u8 {
    if leanh::lean_obj_tag(v_c_811_) == 0 {
        let mut v_promise_814_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_815_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_816_: u8 = 0;
        v_promise_814_ = leanh::lean_ctor_get(v_c_811_, 0);
        v___x_815_ = lean_io_promise_resolve(v_x_812_, v_promise_814_);
        v___x_816_ = 1;
        return v___x_816_;
    } else {
        let mut v_finished_817_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_lose_818_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_819_: u8 = 0;
        v_finished_817_ = leanh::lean_ctor_get(v_c_811_, 0);
        v_lose_818_ = l_Std_Notify_Consumer_resolve___redArg___closed__0;
        v___x_819_ = l_Std_Async_Waiter_race___at___00Std_Notify_Consumer_resolve_spec__0___redArg(
            v_x_812_,
            v_finished_817_,
            v_lose_818_,
        );
        return v___x_819_;
    }
}
pub unsafe fn l_Std_Notify_Consumer_resolve___redArg___boxed(
    mut v_c_820_: *mut leanh::LeanObject,
    mut v_x_821_: *mut leanh::LeanObject,
    mut v_a_822_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_823_: u8 = 0;
    let mut v_r_824_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_823_ = l_Std_Notify_Consumer_resolve___redArg(v_c_820_, v_x_821_);
    leanh::lean_dec_ref(v_c_820_);
    v_r_824_ = leanh::lean_box((v_res_823_) as usize);
    return v_r_824_;
}
pub unsafe fn l_Std_Notify_Consumer_resolve(
    mut v_00_u03b1_825_: *mut leanh::LeanObject,
    mut v_c_826_: *mut leanh::LeanObject,
    mut v_x_827_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_829_: u8 = 0;
    v___x_829_ = l_Std_Notify_Consumer_resolve___redArg(v_c_826_, v_x_827_);
    return v___x_829_;
}
pub unsafe fn l_Std_Notify_Consumer_resolve___boxed(
    mut v_00_u03b1_830_: *mut leanh::LeanObject,
    mut v_c_831_: *mut leanh::LeanObject,
    mut v_x_832_: *mut leanh::LeanObject,
    mut v_a_833_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_834_: u8 = 0;
    let mut v_r_835_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_834_ = l_Std_Notify_Consumer_resolve(v_00_u03b1_830_, v_c_831_, v_x_832_);
    leanh::lean_dec_ref(v_c_831_);
    v_r_835_ = leanh::lean_box((v_res_834_) as usize);
    return v_r_835_;
}
pub unsafe fn _init_l_Std_Notify_new___closed__0() -> *mut leanh::LeanObject {
    let mut v___x_836_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_836_ = l_Std_Queue_empty(leanh::lean_box(0));
    return v___x_836_;
}
pub unsafe fn l_Std_Notify_new() -> *mut leanh::LeanObject {
    let mut v___x_838_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_839_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_838_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Notify_new___closed__0),
        core::ptr::addr_of_mut!(l_Std_Notify_new___closed__0_once),
        _init_l_Std_Notify_new___closed__0,
    );
    v___x_839_ = l_Std_Mutex_new___redArg(v___x_838_);
    return v___x_839_;
}
pub unsafe fn l_Std_Notify_new___boxed(
    mut v_a_840_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_841_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_841_ = l_Std_Notify_new();
    return v_res_841_;
}
pub unsafe fn l_Std_Mutex_atomically___at___00Std_Notify_notify_spec__1___redArg(
    mut v_mutex_842_: *mut leanh::LeanObject,
    mut v_k_843_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_ref_845_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_mutex_846_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_847_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_848_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_849_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_ref_845_ = leanh::lean_ctor_get(v_mutex_842_, 0);
    leanh::lean_inc(v_ref_845_);
    v_mutex_846_ = leanh::lean_ctor_get(v_mutex_842_, 1);
    leanh::lean_inc(v_mutex_846_);
    leanh::lean_dec_ref(v_mutex_842_);
    v___x_847_ = lean_io_basemutex_lock(v_mutex_846_);
    v___x_848_ = leanh::lean_apply_2(v_k_843_, v_ref_845_, leanh::lean_box(0));
    v___x_849_ = lean_io_basemutex_unlock(v_mutex_846_);
    leanh::lean_dec(v_mutex_846_);
    return v___x_848_;
}
pub unsafe fn l_Std_Mutex_atomically___at___00Std_Notify_notify_spec__1___redArg___boxed(
    mut v_mutex_850_: *mut leanh::LeanObject,
    mut v_k_851_: *mut leanh::LeanObject,
    mut v___y_852_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_853_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_853_ =
        l_Std_Mutex_atomically___at___00Std_Notify_notify_spec__1___redArg(v_mutex_850_, v_k_851_);
    return v_res_853_;
}
pub unsafe fn l_Std_Mutex_atomically___at___00Std_Notify_notify_spec__1(
    mut v_00_u03b1_854_: *mut leanh::LeanObject,
    mut v_00_u03b2_855_: *mut leanh::LeanObject,
    mut v_mutex_856_: *mut leanh::LeanObject,
    mut v_k_857_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_859_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_859_ =
        l_Std_Mutex_atomically___at___00Std_Notify_notify_spec__1___redArg(v_mutex_856_, v_k_857_);
    return v___x_859_;
}
pub unsafe fn l_Std_Mutex_atomically___at___00Std_Notify_notify_spec__1___boxed(
    mut v_00_u03b1_860_: *mut leanh::LeanObject,
    mut v_00_u03b2_861_: *mut leanh::LeanObject,
    mut v_mutex_862_: *mut leanh::LeanObject,
    mut v_k_863_: *mut leanh::LeanObject,
    mut v___y_864_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_865_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_865_ = l_Std_Mutex_atomically___at___00Std_Notify_notify_spec__1(
        v_00_u03b1_860_,
        v_00_u03b2_861_,
        v_mutex_862_,
        v_k_863_,
    );
    return v_res_865_;
}
pub unsafe fn l___private_Init_While_0__whileM_erased___at___00Std_Notify_notify_spec__0___redArg(
    mut v_a_866_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_868_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_869_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_870_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_871_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_872_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_873_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                leanh::lean_inc_ref(v_a_866_);
                v___x_868_ = l_Std_Queue_dequeue_x3f___redArg(v_a_866_);
                if leanh::lean_obj_tag(v___x_868_) == 1 {
                    leanh::lean_dec_ref(v_a_866_);
                    v_val_869_ = leanh::lean_ctor_get(v___x_868_, 0);
                    leanh::lean_inc(v_val_869_);
                    leanh::lean_dec_ref_known(v___x_868_, 1);
                    v_fst_870_ = leanh::lean_ctor_get(v_val_869_, 0);
                    leanh::lean_inc(v_fst_870_);
                    v_snd_871_ = leanh::lean_ctor_get(v_val_869_, 1);
                    leanh::lean_inc(v_snd_871_);
                    leanh::lean_dec(v_val_869_);
                    v___x_872_ = leanh::lean_box(0);
                    v___x_873_ = l_Std_Notify_Consumer_resolve___redArg(v_fst_870_, v___x_872_);
                    leanh::lean_dec(v_fst_870_);
                    v_a_866_ = v_snd_871_;
                    state = 0;
                    continue;
                } else {
                    leanh::lean_dec(v___x_868_);
                    return v_a_866_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_While_0__whileM_erased___at___00Std_Notify_notify_spec__0___redArg___boxed(
    mut v_a_875_: *mut leanh::LeanObject,
    mut v___y_876_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_877_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_877_ =
        l___private_Init_While_0__whileM_erased___at___00Std_Notify_notify_spec__0___redArg(
            v_a_875_,
        );
    return v_res_877_;
}
pub unsafe fn l_Std_Notify_notify___lam__0(
    mut v___y_878_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_880_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_881_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_st_882_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_883_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_880_ = lean_st_ref_get(v___y_878_);
    v___x_881_ =
        l___private_Init_While_0__whileM_erased___at___00Std_Notify_notify_spec__0___redArg(
            v___x_880_,
        );
    leanh::lean_dec_ref(v___x_881_);
    v_st_882_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Notify_new___closed__0),
        core::ptr::addr_of_mut!(l_Std_Notify_new___closed__0_once),
        _init_l_Std_Notify_new___closed__0,
    );
    v___x_883_ = lean_st_ref_set(v___y_878_, v_st_882_);
    return v___x_883_;
}
pub unsafe fn l_Std_Notify_notify___lam__0___boxed(
    mut v___y_884_: *mut leanh::LeanObject,
    mut v___y_885_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_886_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_886_ = l_Std_Notify_notify___lam__0(v___y_884_);
    leanh::lean_dec(v___y_884_);
    return v_res_886_;
}
pub unsafe fn l_Std_Notify_notify(
    mut v_x_888_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_890_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_891_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_890_ = l_Std_Notify_notify___closed__0;
    v___x_891_ =
        l_Std_Mutex_atomically___at___00Std_Notify_notify_spec__1___redArg(v_x_888_, v___f_890_);
    return v___x_891_;
}
pub unsafe fn l_Std_Notify_notify___boxed(
    mut v_x_892_: *mut leanh::LeanObject,
    mut v_a_893_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_894_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_894_ = l_Std_Notify_notify(v_x_892_);
    return v_res_894_;
}
pub unsafe fn l___private_Init_While_0__whileM_erased___at___00Std_Notify_notify_spec__0(
    mut v_inst_895_: *mut leanh::LeanObject,
    mut v_a_896_: *mut leanh::LeanObject,
    mut v___y_897_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_899_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_899_ =
        l___private_Init_While_0__whileM_erased___at___00Std_Notify_notify_spec__0___redArg(
            v_a_896_,
        );
    return v___x_899_;
}
pub unsafe fn l___private_Init_While_0__whileM_erased___at___00Std_Notify_notify_spec__0___boxed(
    mut v_inst_900_: *mut leanh::LeanObject,
    mut v_a_901_: *mut leanh::LeanObject,
    mut v___y_902_: *mut leanh::LeanObject,
    mut v___y_903_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_904_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_904_ = l___private_Init_While_0__whileM_erased___at___00Std_Notify_notify_spec__0(
        v_inst_900_,
        v_a_901_,
        v___y_902_,
    );
    leanh::lean_dec(v___y_902_);
    return v_res_904_;
}
pub unsafe fn l_Std_Notify_notifyOne___lam__0(mut v___y_905_: *mut leanh::LeanObject) -> u8 {
    let mut v___x_907_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_908_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_907_ = lean_st_ref_get(v___y_905_);
    v___x_908_ = l_Std_Queue_dequeue_x3f___redArg(v___x_907_);
    if leanh::lean_obj_tag(v___x_908_) == 1 {
        let mut v_val_909_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_fst_910_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_snd_911_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_912_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_913_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_914_: u8 = 0;
        v_val_909_ = leanh::lean_ctor_get(v___x_908_, 0);
        leanh::lean_inc(v_val_909_);
        leanh::lean_dec_ref_known(v___x_908_, 1);
        v_fst_910_ = leanh::lean_ctor_get(v_val_909_, 0);
        leanh::lean_inc(v_fst_910_);
        v_snd_911_ = leanh::lean_ctor_get(v_val_909_, 1);
        leanh::lean_inc(v_snd_911_);
        leanh::lean_dec(v_val_909_);
        v___x_912_ = lean_st_ref_set(v___y_905_, v_snd_911_);
        v___x_913_ = leanh::lean_box(0);
        v___x_914_ = l_Std_Notify_Consumer_resolve___redArg(v_fst_910_, v___x_913_);
        leanh::lean_dec(v_fst_910_);
        return v___x_914_;
    } else {
        let mut v___x_915_: u8 = 0;
        leanh::lean_dec(v___x_908_);
        v___x_915_ = 0;
        return v___x_915_;
    }
}
pub unsafe fn l_Std_Notify_notifyOne___lam__0___boxed(
    mut v___y_916_: *mut leanh::LeanObject,
    mut v___y_917_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_918_: u8 = 0;
    let mut v_r_919_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_918_ = l_Std_Notify_notifyOne___lam__0(v___y_916_);
    leanh::lean_dec(v___y_916_);
    v_r_919_ = leanh::lean_box((v_res_918_) as usize);
    return v_r_919_;
}
pub unsafe fn l_Std_Notify_notifyOne(mut v_x_921_: *mut leanh::LeanObject) -> u8 {
    let mut v___f_923_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_924_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_925_: u8 = 0;
    v___f_923_ = l_Std_Notify_notifyOne___closed__0;
    v___x_924_ =
        l_Std_Mutex_atomically___at___00Std_Notify_notify_spec__1___redArg(v_x_921_, v___f_923_);
    v___x_925_ = (leanh::lean_unbox(v___x_924_) as u8);
    leanh::lean_dec(v___x_924_);
    return v___x_925_;
}
pub unsafe fn l_Std_Notify_notifyOne___boxed(
    mut v_x_926_: *mut leanh::LeanObject,
    mut v_a_927_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_928_: u8 = 0;
    let mut v_r_929_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_928_ = l_Std_Notify_notifyOne(v_x_926_);
    v_r_929_ = leanh::lean_box((v_res_928_) as usize);
    return v_r_929_;
}
pub unsafe fn l_Std_Mutex_atomically___at___00Std_Notify_wait_spec__0___redArg(
    mut v_mutex_930_: *mut leanh::LeanObject,
    mut v_k_931_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_ref_933_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_mutex_934_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_935_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_936_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_937_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_939_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_940_: u8 = 0;
    let mut v___x_941_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_943_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_944_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_945_: u8 = 0;
    let mut v_a_946_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_948_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_949_: u8 = 0;
    let mut v___x_950_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_952_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_953_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_954_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ref_933_ = leanh::lean_ctor_get(v_mutex_930_, 0);
                leanh::lean_inc(v_ref_933_);
                v_mutex_934_ = leanh::lean_ctor_get(v_mutex_930_, 1);
                leanh::lean_inc(v_mutex_934_);
                leanh::lean_dec_ref(v_mutex_930_);
                v___x_935_ = lean_io_basemutex_lock(v_mutex_934_);
                v_r_936_ =
                    leanh::lean_apply_2(v_k_931_, v_ref_933_, leanh::lean_box(0));
                if leanh::lean_obj_tag(v_r_936_) == 0 {
                    v_a_937_ = leanh::lean_ctor_get(v_r_936_, 0);
                    v_isSharedCheck_945_ = (!leanh::lean_is_exclusive(v_r_936_)) as u8;
                    if v_isSharedCheck_945_ == 0 {
                        v___x_939_ = v_r_936_;
                        v_isShared_940_ = v_isSharedCheck_945_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_937_);
                        leanh::lean_dec(v_r_936_);
                        v___x_939_ = leanh::lean_box(0);
                        v_isShared_940_ = v_isSharedCheck_945_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_946_ = leanh::lean_ctor_get(v_r_936_, 0);
                    v_isSharedCheck_954_ = (!leanh::lean_is_exclusive(v_r_936_)) as u8;
                    if v_isSharedCheck_954_ == 0 {
                        v___x_948_ = v_r_936_;
                        v_isShared_949_ = v_isSharedCheck_954_;
                        state = 3;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_946_);
                        leanh::lean_dec(v_r_936_);
                        v___x_948_ = leanh::lean_box(0);
                        v_isShared_949_ = v_isSharedCheck_954_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v___x_941_ = lean_io_basemutex_unlock(v_mutex_934_);
                leanh::lean_dec(v_mutex_934_);
                if v_isShared_940_ == 0 {
                    v___x_943_ = v___x_939_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_944_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_944_, 0, v_a_937_);
                    v___x_943_ = v_reuseFailAlloc_944_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_943_;
            }
            3 => {
                v___x_950_ = lean_io_basemutex_unlock(v_mutex_934_);
                leanh::lean_dec(v_mutex_934_);
                if v_isShared_949_ == 0 {
                    v___x_952_ = v___x_948_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_953_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_953_, 0, v_a_946_);
                    v___x_952_ = v_reuseFailAlloc_953_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_952_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Mutex_atomically___at___00Std_Notify_wait_spec__0___redArg___boxed(
    mut v_mutex_955_: *mut leanh::LeanObject,
    mut v_k_956_: *mut leanh::LeanObject,
    mut v___y_957_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_958_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_958_ =
        l_Std_Mutex_atomically___at___00Std_Notify_wait_spec__0___redArg(v_mutex_955_, v_k_956_);
    return v_res_958_;
}
pub unsafe fn l_Std_Mutex_atomically___at___00Std_Notify_wait_spec__0(
    mut v_00_u03b1_959_: *mut leanh::LeanObject,
    mut v_00_u03b2_960_: *mut leanh::LeanObject,
    mut v_mutex_961_: *mut leanh::LeanObject,
    mut v_k_962_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_964_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_964_ =
        l_Std_Mutex_atomically___at___00Std_Notify_wait_spec__0___redArg(v_mutex_961_, v_k_962_);
    return v___x_964_;
}
pub unsafe fn l_Std_Mutex_atomically___at___00Std_Notify_wait_spec__0___boxed(
    mut v_00_u03b1_965_: *mut leanh::LeanObject,
    mut v_00_u03b2_966_: *mut leanh::LeanObject,
    mut v_mutex_967_: *mut leanh::LeanObject,
    mut v_k_968_: *mut leanh::LeanObject,
    mut v___y_969_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_970_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_970_ = l_Std_Mutex_atomically___at___00Std_Notify_wait_spec__0(
        v_00_u03b1_965_,
        v_00_u03b2_966_,
        v_mutex_967_,
        v_k_968_,
    );
    return v_res_970_;
}
pub unsafe fn _init_l_Std_Notify_wait___lam__0___closed__1() -> *mut leanh::LeanObject {
    let mut v___x_972_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_973_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_972_ = l_Std_Notify_wait___lam__0___closed__0;
    v___x_973_ = lean_mk_io_user_error(v___x_972_);
    return v___x_973_;
}
pub unsafe fn _init_l_Std_Notify_wait___lam__0___closed__2() -> *mut leanh::LeanObject {
    let mut v___x_974_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_975_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_974_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Notify_wait___lam__0___closed__1),
        core::ptr::addr_of_mut!(l_Std_Notify_wait___lam__0___closed__1_once),
        _init_l_Std_Notify_wait___lam__0___closed__1,
    );
    v___x_975_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_975_, 0, v___x_974_);
    return v___x_975_;
}
pub unsafe fn _init_l_Std_Notify_wait___lam__0___closed__3() -> *mut leanh::LeanObject {
    let mut v___x_976_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_977_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_976_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Notify_wait___lam__0___closed__2),
        core::ptr::addr_of_mut!(l_Std_Notify_wait___lam__0___closed__2_once),
        _init_l_Std_Notify_wait___lam__0___closed__2,
    );
    v___x_977_ = lean_task_pure(v___x_976_);
    return v___x_977_;
}
pub unsafe fn l_Std_Notify_wait___lam__0(
    mut v_a_978_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_980_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_981_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_983_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_984_: u8 = 0;
    let mut v___x_986_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_987_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_988_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_989_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_a_978_) == 0 {
                    v___x_980_ = leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(l_Std_Notify_wait___lam__0___closed__3),
                        core::ptr::addr_of_mut!(l_Std_Notify_wait___lam__0___closed__3_once),
                        _init_l_Std_Notify_wait___lam__0___closed__3,
                    );
                    return v___x_980_;
                } else {
                    v_val_981_ = leanh::lean_ctor_get(v_a_978_, 0);
                    v_isSharedCheck_989_ = (!leanh::lean_is_exclusive(v_a_978_)) as u8;
                    if v_isSharedCheck_989_ == 0 {
                        v___x_983_ = v_a_978_;
                        v_isShared_984_ = v_isSharedCheck_989_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_val_981_);
                        leanh::lean_dec(v_a_978_);
                        v___x_983_ = leanh::lean_box(0);
                        v_isShared_984_ = v_isSharedCheck_989_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_984_ == 0 {
                    v___x_986_ = v___x_983_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_988_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_988_, 0, v_val_981_);
                    v___x_986_ = v_reuseFailAlloc_988_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_987_ = lean_task_pure(v___x_986_);
                return v___x_987_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Notify_wait___lam__0___boxed(
    mut v_a_990_: *mut leanh::LeanObject,
    mut v___y_991_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_992_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_992_ = l_Std_Notify_wait___lam__0(v_a_990_);
    return v_res_992_;
}
pub unsafe fn l_Std_Notify_wait___lam__1(
    mut v___f_993_: *mut leanh::LeanObject,
    mut v___y_994_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_996_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_997_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_998_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_999_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1000_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1001_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1002_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1003_: u8 = 0;
    let mut v___x_1004_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1005_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_996_ = lean_io_promise_new();
    v___x_997_ = lean_st_ref_take(v___y_994_);
    leanh::lean_inc(v___x_996_);
    v___x_998_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_998_, 0, v___x_996_);
    v___x_999_ = l_Std_Queue_enqueue___redArg(v___x_998_, v___x_997_);
    v___x_1000_ = lean_st_ref_set(v___y_994_, v___x_999_);
    v___x_1001_ = lean_io_promise_result_opt(v___x_996_);
    leanh::lean_dec(v___x_996_);
    v___x_1002_ = leanh::lean_unsigned_to_nat(0);
    v___x_1003_ = 0;
    v___x_1004_ = lean_io_bind_task(v___x_1001_, v___f_993_, v___x_1002_, v___x_1003_);
    v___x_1005_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_1005_, 0, v___x_1004_);
    return v___x_1005_;
}
pub unsafe fn l_Std_Notify_wait___lam__1___boxed(
    mut v___f_1006_: *mut leanh::LeanObject,
    mut v___y_1007_: *mut leanh::LeanObject,
    mut v___y_1008_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1009_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1009_ = l_Std_Notify_wait___lam__1(v___f_1006_, v___y_1007_);
    leanh::lean_dec(v___y_1007_);
    return v_res_1009_;
}
pub unsafe fn l_Std_Notify_wait(
    mut v_x_1013_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_1015_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1016_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_1015_ = l_Std_Notify_wait___closed__1;
    v___x_1016_ =
        l_Std_Mutex_atomically___at___00Std_Notify_wait_spec__0___redArg(v_x_1013_, v___f_1015_);
    return v___x_1016_;
}
pub unsafe fn l_Std_Notify_wait___boxed(
    mut v_x_1017_: *mut leanh::LeanObject,
    mut v_a_1018_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1019_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1019_ = l_Std_Notify_wait(v_x_1017_);
    return v_res_1019_;
}
pub unsafe fn l_Std_Mutex_atomically___at___00Std_Notify_selector_spec__0___redArg___lam__0(
    mut v_mutex_1020_: *mut leanh::LeanObject,
    mut v_x_1021_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1023_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1024_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1025_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1023_ = lean_io_basemutex_unlock(v_mutex_1020_);
    v___x_1024_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_1024_, 0, v___x_1023_);
    v___x_1025_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_1025_, 0, v___x_1024_);
    return v___x_1025_;
}
pub unsafe fn l_Std_Mutex_atomically___at___00Std_Notify_selector_spec__0___redArg___lam__0___boxed(
    mut v_mutex_1026_: *mut leanh::LeanObject,
    mut v_x_1027_: *mut leanh::LeanObject,
    mut v___y_1028_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1029_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1029_ = l_Std_Mutex_atomically___at___00Std_Notify_selector_spec__0___redArg___lam__0(
        v_mutex_1026_,
        v_x_1027_,
    );
    leanh::lean_dec(v_x_1027_);
    leanh::lean_dec(v_mutex_1026_);
    return v_res_1029_;
}
pub unsafe fn l_Std_Mutex_atomically___at___00Std_Notify_selector_spec__0___redArg___lam__1(
    mut v_k_1030_: *mut leanh::LeanObject,
    mut v_ref_1031_: *mut leanh::LeanObject,
    mut v_x_1032_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_a_1034_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1036_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1037_: u8 = 0;
    let mut v___x_1039_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1040_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1041_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1042_: u8 = 0;
    let mut v___x_1043_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_1032_) == 0 {
                    leanh::lean_dec(v_ref_1031_);
                    leanh::lean_dec_ref(v_k_1030_);
                    v_a_1034_ = leanh::lean_ctor_get(v_x_1032_, 0);
                    v_isSharedCheck_1042_ = (!leanh::lean_is_exclusive(v_x_1032_)) as u8;
                    if v_isSharedCheck_1042_ == 0 {
                        v___x_1036_ = v_x_1032_;
                        v_isShared_1037_ = v_isSharedCheck_1042_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_1034_);
                        leanh::lean_dec(v_x_1032_);
                        v___x_1036_ = leanh::lean_box(0);
                        v_isShared_1037_ = v_isSharedCheck_1042_;
                        state = 1;
                        continue;
                    }
                } else {
                    leanh::lean_dec_ref_known(v_x_1032_, 1);
                    v___x_1043_ = leanh::lean_apply_2(
                        v_k_1030_,
                        v_ref_1031_,
                        leanh::lean_box(0),
                    );
                    return v___x_1043_;
                }
            }
            1 => {
                if v_isShared_1037_ == 0 {
                    v___x_1039_ = v___x_1036_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1041_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1041_, 0, v_a_1034_);
                    v___x_1039_ = v_reuseFailAlloc_1041_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_1040_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_1040_, 0, v___x_1039_);
                return v___x_1040_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Mutex_atomically___at___00Std_Notify_selector_spec__0___redArg___lam__1___boxed(
    mut v_k_1044_: *mut leanh::LeanObject,
    mut v_ref_1045_: *mut leanh::LeanObject,
    mut v_x_1046_: *mut leanh::LeanObject,
    mut v___y_1047_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1048_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1048_ = l_Std_Mutex_atomically___at___00Std_Notify_selector_spec__0___redArg___lam__1(
        v_k_1044_,
        v_ref_1045_,
        v_x_1046_,
    );
    return v_res_1048_;
}
pub unsafe fn l_Std_Mutex_atomically___at___00Std_Notify_selector_spec__0___redArg___lam__2(
    mut v_mutex_1049_: *mut leanh::LeanObject,
    mut v___f_1050_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1052_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1053_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1054_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1055_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1056_: u8 = 0;
    let mut v___x_1057_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1052_ = lean_io_basemutex_lock(v_mutex_1049_);
    v___x_1053_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_1053_, 0, v___x_1052_);
    v___x_1054_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_1054_, 0, v___x_1053_);
    v___x_1055_ = leanh::lean_unsigned_to_nat(0);
    v___x_1056_ = 0;
    v___x_1057_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(
        leanh::lean_box(0),
        leanh::lean_box(0),
        v___x_1055_,
        v___x_1056_,
        v___x_1054_,
        v___f_1050_,
    );
    return v___x_1057_;
}
pub unsafe fn l_Std_Mutex_atomically___at___00Std_Notify_selector_spec__0___redArg___lam__2___boxed(
    mut v_mutex_1058_: *mut leanh::LeanObject,
    mut v___f_1059_: *mut leanh::LeanObject,
    mut v___y_1060_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1061_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1061_ = l_Std_Mutex_atomically___at___00Std_Notify_selector_spec__0___redArg___lam__2(
        v_mutex_1058_,
        v___f_1059_,
    );
    leanh::lean_dec(v_mutex_1058_);
    return v_res_1061_;
}
pub unsafe fn l_Std_Mutex_atomically___at___00Std_Notify_selector_spec__0___redArg___lam__3(
    mut v___y_1062_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_a_1063_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1065_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1066_: u8 = 0;
    let mut v___x_1068_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1069_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1070_: u8 = 0;
    let mut v_a_1071_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1073_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1074_: u8 = 0;
    let mut v_fst_1075_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1077_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1078_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1079_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v___y_1062_) == 0 {
                    v_a_1063_ = leanh::lean_ctor_get(v___y_1062_, 0);
                    v_isSharedCheck_1070_ = (!leanh::lean_is_exclusive(v___y_1062_)) as u8;
                    if v_isSharedCheck_1070_ == 0 {
                        v___x_1065_ = v___y_1062_;
                        v_isShared_1066_ = v_isSharedCheck_1070_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_1063_);
                        leanh::lean_dec(v___y_1062_);
                        v___x_1065_ = leanh::lean_box(0);
                        v_isShared_1066_ = v_isSharedCheck_1070_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_1071_ = leanh::lean_ctor_get(v___y_1062_, 0);
                    v_isSharedCheck_1079_ = (!leanh::lean_is_exclusive(v___y_1062_)) as u8;
                    if v_isSharedCheck_1079_ == 0 {
                        v___x_1073_ = v___y_1062_;
                        v_isShared_1074_ = v_isSharedCheck_1079_;
                        state = 3;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_1071_);
                        leanh::lean_dec(v___y_1062_);
                        v___x_1073_ = leanh::lean_box(0);
                        v_isShared_1074_ = v_isSharedCheck_1079_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_1066_ == 0 {
                    v___x_1068_ = v___x_1065_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1069_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1069_, 0, v_a_1063_);
                    v___x_1068_ = v_reuseFailAlloc_1069_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1068_;
            }
            3 => {
                v_fst_1075_ = leanh::lean_ctor_get(v_a_1071_, 0);
                leanh::lean_inc(v_fst_1075_);
                leanh::lean_dec(v_a_1071_);
                if v_isShared_1074_ == 0 {
                    leanh::lean_ctor_set(v___x_1073_, 0, v_fst_1075_);
                    v___x_1077_ = v___x_1073_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1078_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1078_, 0, v_fst_1075_);
                    v___x_1077_ = v_reuseFailAlloc_1078_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_1077_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Mutex_atomically___at___00Std_Notify_selector_spec__0___redArg(
    mut v_mutex_1081_: *mut leanh::LeanObject,
    mut v_k_1082_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_ref_1084_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_mutex_1085_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1086_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1087_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1088_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1089_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1090_: u8 = 0;
    let mut v___x_1091_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1093_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1094_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1095_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1096_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1098_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1099_: u8 = 0;
    let mut v___x_1101_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1102_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1103_: u8 = 0;
    let mut v_a_1104_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1106_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1107_: u8 = 0;
    let mut v_fst_1108_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1110_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1111_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1112_: u8 = 0;
    let mut v_a_1113_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1115_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1116_: u8 = 0;
    let mut v___f_1117_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1118_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1120_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1121_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1122_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ref_1084_ = leanh::lean_ctor_get(v_mutex_1081_, 0);
                leanh::lean_inc(v_ref_1084_);
                v_mutex_1085_ = leanh::lean_ctor_get(v_mutex_1081_, 1);
                leanh::lean_inc_n(v_mutex_1085_, 2);
                leanh::lean_dec_ref(v_mutex_1081_);
                v___f_1086_ = leanh::lean_alloc_closure(l_Std_Mutex_atomically___at___00Std_Notify_selector_spec__0___redArg___lam__0___boxed as *mut core::ffi::c_void, 3, 1);
                leanh::lean_closure_set(v___f_1086_, 0, v_mutex_1085_);
                v___f_1087_ = leanh::lean_alloc_closure(l_Std_Mutex_atomically___at___00Std_Notify_selector_spec__0___redArg___lam__1___boxed as *mut core::ffi::c_void, 4, 2);
                leanh::lean_closure_set(v___f_1087_, 0, v_k_1082_);
                leanh::lean_closure_set(v___f_1087_, 1, v_ref_1084_);
                v___f_1088_ = leanh::lean_alloc_closure(l_Std_Mutex_atomically___at___00Std_Notify_selector_spec__0___redArg___lam__2___boxed as *mut core::ffi::c_void, 3, 2);
                leanh::lean_closure_set(v___f_1088_, 0, v_mutex_1085_);
                leanh::lean_closure_set(v___f_1088_, 1, v___f_1087_);
                v___x_1089_ = leanh::lean_unsigned_to_nat(0);
                v___x_1090_ = 0;
                v___x_1091_ = l_Std_Async_EAsync_tryFinally_x27___redArg(
                    v___f_1088_,
                    v___f_1086_,
                    v___x_1089_,
                    v___x_1090_,
                );
                if leanh::lean_obj_tag(v___x_1091_) == 0 {
                    v_a_1095_ = leanh::lean_ctor_get(v___x_1091_, 0);
                    leanh::lean_inc(v_a_1095_);
                    leanh::lean_dec_ref_known(v___x_1091_, 1);
                    if leanh::lean_obj_tag(v_a_1095_) == 0 {
                        v_a_1096_ = leanh::lean_ctor_get(v_a_1095_, 0);
                        v_isSharedCheck_1103_ = (!leanh::lean_is_exclusive(v_a_1095_)) as u8;
                        if v_isSharedCheck_1103_ == 0 {
                            v___x_1098_ = v_a_1095_;
                            v_isShared_1099_ = v_isSharedCheck_1103_;
                            state = 2;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_1096_);
                            leanh::lean_dec(v_a_1095_);
                            v___x_1098_ = leanh::lean_box(0);
                            v_isShared_1099_ = v_isSharedCheck_1103_;
                            state = 2;
                            continue;
                        }
                    } else {
                        v_a_1104_ = leanh::lean_ctor_get(v_a_1095_, 0);
                        v_isSharedCheck_1112_ = (!leanh::lean_is_exclusive(v_a_1095_)) as u8;
                        if v_isSharedCheck_1112_ == 0 {
                            v___x_1106_ = v_a_1095_;
                            v_isShared_1107_ = v_isSharedCheck_1112_;
                            state = 4;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_1104_);
                            leanh::lean_dec(v_a_1095_);
                            v___x_1106_ = leanh::lean_box(0);
                            v_isShared_1107_ = v_isSharedCheck_1112_;
                            state = 4;
                            continue;
                        }
                    }
                } else {
                    v_a_1113_ = leanh::lean_ctor_get(v___x_1091_, 0);
                    v_isSharedCheck_1122_ = (!leanh::lean_is_exclusive(v___x_1091_)) as u8;
                    if v_isSharedCheck_1122_ == 0 {
                        v___x_1115_ = v___x_1091_;
                        v_isShared_1116_ = v_isSharedCheck_1122_;
                        state = 6;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_1113_);
                        leanh::lean_dec(v___x_1091_);
                        v___x_1115_ = leanh::lean_box(0);
                        v_isShared_1116_ = v_isSharedCheck_1122_;
                        state = 6;
                        continue;
                    }
                }
            }
            1 => {
                v___x_1094_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_1094_, 0, v___y_1093_);
                return v___x_1094_;
            }
            2 => {
                if v_isShared_1099_ == 0 {
                    v___x_1101_ = v___x_1098_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_1102_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1102_, 0, v_a_1096_);
                    v___x_1101_ = v_reuseFailAlloc_1102_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___y_1093_ = v___x_1101_;
                state = 1;
                continue;
            }
            4 => {
                v_fst_1108_ = leanh::lean_ctor_get(v_a_1104_, 0);
                leanh::lean_inc(v_fst_1108_);
                leanh::lean_dec(v_a_1104_);
                if v_isShared_1107_ == 0 {
                    leanh::lean_ctor_set(v___x_1106_, 0, v_fst_1108_);
                    v___x_1110_ = v___x_1106_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_1111_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1111_, 0, v_fst_1108_);
                    v___x_1110_ = v_reuseFailAlloc_1111_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v___y_1093_ = v___x_1110_;
                state = 1;
                continue;
            }
            6 => {
                v___f_1117_ = l_Std_Mutex_atomically___at___00Std_Notify_selector_spec__0___redArg___closed__0;
                v___x_1118_ = lean_task_map(v___f_1117_, v_a_1113_, v___x_1089_, v___x_1090_);
                if v_isShared_1116_ == 0 {
                    leanh::lean_ctor_set(v___x_1115_, 0, v___x_1118_);
                    v___x_1120_ = v___x_1115_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_1121_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1121_, 0, v___x_1118_);
                    v___x_1120_ = v_reuseFailAlloc_1121_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_1120_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Mutex_atomically___at___00Std_Notify_selector_spec__0___redArg___boxed(
    mut v_mutex_1123_: *mut leanh::LeanObject,
    mut v_k_1124_: *mut leanh::LeanObject,
    mut v___y_1125_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1126_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1126_ = l_Std_Mutex_atomically___at___00Std_Notify_selector_spec__0___redArg(
        v_mutex_1123_,
        v_k_1124_,
    );
    return v_res_1126_;
}
pub unsafe fn l_Std_Mutex_atomically___at___00Std_Notify_selector_spec__0(
    mut v_00_u03b1_1127_: *mut leanh::LeanObject,
    mut v_00_u03b2_1128_: *mut leanh::LeanObject,
    mut v_mutex_1129_: *mut leanh::LeanObject,
    mut v_k_1130_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1132_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1132_ = l_Std_Mutex_atomically___at___00Std_Notify_selector_spec__0___redArg(
        v_mutex_1129_,
        v_k_1130_,
    );
    return v___x_1132_;
}
pub unsafe fn l_Std_Mutex_atomically___at___00Std_Notify_selector_spec__0___boxed(
    mut v_00_u03b1_1133_: *mut leanh::LeanObject,
    mut v_00_u03b2_1134_: *mut leanh::LeanObject,
    mut v_mutex_1135_: *mut leanh::LeanObject,
    mut v_k_1136_: *mut leanh::LeanObject,
    mut v___y_1137_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1138_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1138_ = l_Std_Mutex_atomically___at___00Std_Notify_selector_spec__0(
        v_00_u03b1_1133_,
        v_00_u03b2_1134_,
        v_mutex_1135_,
        v_k_1136_,
    );
    return v_res_1138_;
}
pub unsafe fn l_Std_Notify_selector___lam__0(
    mut v___y_1139_: *mut leanh::LeanObject,
    mut v_x_1140_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_a_1142_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1144_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1145_: u8 = 0;
    let mut v___x_1147_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1148_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1149_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1150_: u8 = 0;
    let mut v_a_1151_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1153_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1154_: u8 = 0;
    let mut v___x_1155_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1157_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1158_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1159_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1160_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_1140_) == 0 {
                    v_a_1142_ = leanh::lean_ctor_get(v_x_1140_, 0);
                    v_isSharedCheck_1150_ = (!leanh::lean_is_exclusive(v_x_1140_)) as u8;
                    if v_isSharedCheck_1150_ == 0 {
                        v___x_1144_ = v_x_1140_;
                        v_isShared_1145_ = v_isSharedCheck_1150_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_1142_);
                        leanh::lean_dec(v_x_1140_);
                        v___x_1144_ = leanh::lean_box(0);
                        v_isShared_1145_ = v_isSharedCheck_1150_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_1151_ = leanh::lean_ctor_get(v_x_1140_, 0);
                    v_isSharedCheck_1160_ = (!leanh::lean_is_exclusive(v_x_1140_)) as u8;
                    if v_isSharedCheck_1160_ == 0 {
                        v___x_1153_ = v_x_1140_;
                        v_isShared_1154_ = v_isSharedCheck_1160_;
                        state = 3;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_1151_);
                        leanh::lean_dec(v_x_1140_);
                        v___x_1153_ = leanh::lean_box(0);
                        v_isShared_1154_ = v_isSharedCheck_1160_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_1145_ == 0 {
                    v___x_1147_ = v___x_1144_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1149_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1149_, 0, v_a_1142_);
                    v___x_1147_ = v_reuseFailAlloc_1149_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_1148_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_1148_, 0, v___x_1147_);
                return v___x_1148_;
            }
            3 => {
                v___x_1155_ = lean_st_ref_set(v___y_1139_, v_a_1151_);
                if v_isShared_1154_ == 0 {
                    leanh::lean_ctor_set(v___x_1153_, 0, v___x_1155_);
                    v___x_1157_ = v___x_1153_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1159_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1159_, 0, v___x_1155_);
                    v___x_1157_ = v_reuseFailAlloc_1159_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_1158_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_1158_, 0, v___x_1157_);
                return v___x_1158_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Notify_selector___lam__0___boxed(
    mut v___y_1161_: *mut leanh::LeanObject,
    mut v_x_1162_: *mut leanh::LeanObject,
    mut v___y_1163_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1164_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1164_ = l_Std_Notify_selector___lam__0(v___y_1161_, v_x_1162_);
    leanh::lean_dec(v___y_1161_);
    return v_res_1164_;
}
pub unsafe fn l_List_filterAuxM___at___00Std_Queue_filterM___at___00Std_Notify_selector_spec__1_spec__1___redArg___lam__1(
    mut v_x_1165_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___y_1168_: u8 = 0;
    let mut v___x_1169_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1170_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1171_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1172_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1173_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1174_: u8 = 0;
    let mut v___x_1175_: u8 = 0;
    let mut v___x_1176_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_1165_) == 0 {
                    v___x_1172_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_1172_, 0, v_x_1165_);
                    return v___x_1172_;
                } else {
                    v_a_1173_ = leanh::lean_ctor_get(v_x_1165_, 0);
                    leanh::lean_inc(v_a_1173_);
                    leanh::lean_dec_ref_known(v_x_1165_, 1);
                    v___x_1174_ = (leanh::lean_unbox(v_a_1173_) as u8);
                    leanh::lean_dec(v_a_1173_);
                    if v___x_1174_ == 0 {
                        v___x_1175_ = 1;
                        v___y_1168_ = v___x_1175_;
                        state = 1;
                        continue;
                    } else {
                        v___x_1176_ = 0;
                        v___y_1168_ = v___x_1176_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_1169_ = leanh::lean_box((v___y_1168_) as usize);
                v___x_1170_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_1170_, 0, v___x_1169_);
                v___x_1171_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_1171_, 0, v___x_1170_);
                return v___x_1171_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_filterAuxM___at___00Std_Queue_filterM___at___00Std_Notify_selector_spec__1_spec__1___redArg___lam__1___boxed(
    mut v_x_1177_: *mut leanh::LeanObject,
    mut v___y_1178_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1179_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1179_ = l_List_filterAuxM___at___00Std_Queue_filterM___at___00Std_Notify_selector_spec__1_spec__1___redArg___lam__1(v_x_1177_);
    return v_res_1179_;
}
pub unsafe fn l_List_filterAuxM___at___00Std_Queue_filterM___at___00Std_Notify_selector_spec__1_spec__1___redArg___lam__0___boxed(
    mut v_tail_1180_: *mut leanh::LeanObject,
    mut v_x_1181_: *mut leanh::LeanObject,
    mut v_head_1182_: *mut leanh::LeanObject,
    mut v_x_1183_: *mut leanh::LeanObject,
    mut v___y_1184_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1185_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1185_ = l_List_filterAuxM___at___00Std_Queue_filterM___at___00Std_Notify_selector_spec__1_spec__1___redArg___lam__0(v_tail_1180_, v_x_1181_, v_head_1182_, v_x_1183_);
    return v_res_1185_;
}
pub unsafe fn l_List_filterAuxM___at___00Std_Queue_filterM___at___00Std_Notify_selector_spec__1_spec__1___redArg(
    mut v_x_1192_: *mut leanh::LeanObject,
    mut v_x_1193_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1195_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1196_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_head_1197_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_1198_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1199_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1201_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1202_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1203_: u8 = 0;
    let mut v___x_1204_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1205_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_finished_1206_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1208_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1209_: u8 = 0;
    let mut v_finished_1210_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1211_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1212_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1214_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1215_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1216_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1217_: u8 = 0;
    let mut v___x_1218_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1219_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1220_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_1192_) == 0 {
                    v___x_1195_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_1195_, 0, v_x_1193_);
                    v___x_1196_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_1196_, 0, v___x_1195_);
                    return v___x_1196_;
                } else {
                    v_head_1197_ = leanh::lean_ctor_get(v_x_1192_, 0);
                    leanh::lean_inc_n(v_head_1197_, 2);
                    v_tail_1198_ = leanh::lean_ctor_get(v_x_1192_, 1);
                    leanh::lean_inc(v_tail_1198_);
                    leanh::lean_dec_ref_known(v_x_1192_, 2);
                    v___f_1199_ = leanh::lean_alloc_closure(l_List_filterAuxM___at___00Std_Queue_filterM___at___00Std_Notify_selector_spec__1_spec__1___redArg___lam__0___boxed as *mut core::ffi::c_void, 5, 3);
                    leanh::lean_closure_set(v___f_1199_, 0, v_tail_1198_);
                    leanh::lean_closure_set(v___f_1199_, 1, v_x_1193_);
                    leanh::lean_closure_set(v___f_1199_, 2, v_head_1197_);
                    if leanh::lean_obj_tag(v_head_1197_) == 0 {
                        leanh::lean_dec_ref_known(v_head_1197_, 1);
                        v___x_1205_ = l_List_filterAuxM___at___00Std_Queue_filterM___at___00Std_Notify_selector_spec__1_spec__1___redArg___closed__1;
                        v_val_1201_ = v___x_1205_;
                        state = 1;
                        continue;
                    } else {
                        v_finished_1206_ = leanh::lean_ctor_get(v_head_1197_, 0);
                        v_isSharedCheck_1220_ =
                            (!leanh::lean_is_exclusive(v_head_1197_)) as u8;
                        if v_isSharedCheck_1220_ == 0 {
                            v___x_1208_ = v_head_1197_;
                            v_isShared_1209_ = v_isSharedCheck_1220_;
                            state = 2;
                            continue;
                        } else {
                            leanh::lean_inc(v_finished_1206_);
                            leanh::lean_dec(v_head_1197_);
                            v___x_1208_ = leanh::lean_box(0);
                            v_isShared_1209_ = v_isSharedCheck_1220_;
                            state = 2;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v___x_1202_ = leanh::lean_unsigned_to_nat(0);
                v___x_1203_ = 0;
                v___x_1204_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(
                    leanh::lean_box(0),
                    leanh::lean_box(0),
                    v___x_1202_,
                    v___x_1203_,
                    v_val_1201_,
                    v___f_1199_,
                );
                return v___x_1204_;
            }
            2 => {
                v_finished_1210_ = leanh::lean_ctor_get(v_finished_1206_, 0);
                leanh::lean_inc(v_finished_1210_);
                leanh::lean_dec_ref(v_finished_1206_);
                v___x_1211_ = lean_st_ref_get(v_finished_1210_);
                leanh::lean_dec(v_finished_1210_);
                v___f_1212_ = l_List_filterAuxM___at___00Std_Queue_filterM___at___00Std_Notify_selector_spec__1_spec__1___redArg___closed__2;
                if v_isShared_1209_ == 0 {
                    leanh::lean_ctor_set(v___x_1208_, 0, v___x_1211_);
                    v___x_1214_ = v___x_1208_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_1219_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1219_, 0, v___x_1211_);
                    v___x_1214_ = v_reuseFailAlloc_1219_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_1215_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_1215_, 0, v___x_1214_);
                v___x_1216_ = leanh::lean_unsigned_to_nat(0);
                v___x_1217_ = 0;
                v___x_1218_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(
                    leanh::lean_box(0),
                    leanh::lean_box(0),
                    v___x_1216_,
                    v___x_1217_,
                    v___x_1215_,
                    v___f_1212_,
                );
                v_val_1201_ = v___x_1218_;
                state = 1;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_filterAuxM___at___00Std_Queue_filterM___at___00Std_Notify_selector_spec__1_spec__1___redArg___lam__0(
    mut v_tail_1221_: *mut leanh::LeanObject,
    mut v_x_1222_: *mut leanh::LeanObject,
    mut v_head_1223_: *mut leanh::LeanObject,
    mut v_x_1224_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_a_1226_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1228_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1229_: u8 = 0;
    let mut v___x_1231_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1232_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1233_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1234_: u8 = 0;
    let mut v_a_1235_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1236_: u8 = 0;
    let mut v___x_1237_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1238_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1239_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_1224_) == 0 {
                    leanh::lean_dec_ref(v_head_1223_);
                    leanh::lean_dec(v_x_1222_);
                    leanh::lean_dec(v_tail_1221_);
                    v_a_1226_ = leanh::lean_ctor_get(v_x_1224_, 0);
                    v_isSharedCheck_1234_ = (!leanh::lean_is_exclusive(v_x_1224_)) as u8;
                    if v_isSharedCheck_1234_ == 0 {
                        v___x_1228_ = v_x_1224_;
                        v_isShared_1229_ = v_isSharedCheck_1234_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_1226_);
                        leanh::lean_dec(v_x_1224_);
                        v___x_1228_ = leanh::lean_box(0);
                        v_isShared_1229_ = v_isSharedCheck_1234_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_1235_ = leanh::lean_ctor_get(v_x_1224_, 0);
                    leanh::lean_inc(v_a_1235_);
                    leanh::lean_dec_ref_known(v_x_1224_, 1);
                    v___x_1236_ = (leanh::lean_unbox(v_a_1235_) as u8);
                    leanh::lean_dec(v_a_1235_);
                    if v___x_1236_ == 0 {
                        leanh::lean_dec_ref(v_head_1223_);
                        v___x_1237_ = l_List_filterAuxM___at___00Std_Queue_filterM___at___00Std_Notify_selector_spec__1_spec__1___redArg(v_tail_1221_, v_x_1222_);
                        return v___x_1237_;
                    } else {
                        v___x_1238_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                        leanh::lean_ctor_set(v___x_1238_, 0, v_head_1223_);
                        leanh::lean_ctor_set(v___x_1238_, 1, v_x_1222_);
                        v___x_1239_ = l_List_filterAuxM___at___00Std_Queue_filterM___at___00Std_Notify_selector_spec__1_spec__1___redArg(v_tail_1221_, v___x_1238_);
                        return v___x_1239_;
                    }
                }
            }
            1 => {
                if v_isShared_1229_ == 0 {
                    v___x_1231_ = v___x_1228_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1233_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1233_, 0, v_a_1226_);
                    v___x_1231_ = v_reuseFailAlloc_1233_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_1232_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_1232_, 0, v___x_1231_);
                return v___x_1232_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_filterAuxM___at___00Std_Queue_filterM___at___00Std_Notify_selector_spec__1_spec__1___redArg___boxed(
    mut v_x_1240_: *mut leanh::LeanObject,
    mut v_x_1241_: *mut leanh::LeanObject,
    mut v___y_1242_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1243_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1243_ = l_List_filterAuxM___at___00Std_Queue_filterM___at___00Std_Notify_selector_spec__1_spec__1___redArg(v_x_1240_, v_x_1241_);
    return v_res_1243_;
}
pub unsafe fn l_Std_Queue_filterM___at___00Std_Notify_selector_spec__1___lam__0(
    mut v_x_1244_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1246_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1247_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1249_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1250_: u8 = 0;
    let mut v___x_1251_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1253_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1254_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1255_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1256_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_1244_) == 0 {
                    v___x_1246_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_1246_, 0, v_x_1244_);
                    return v___x_1246_;
                } else {
                    v_a_1247_ = leanh::lean_ctor_get(v_x_1244_, 0);
                    v_isSharedCheck_1256_ = (!leanh::lean_is_exclusive(v_x_1244_)) as u8;
                    if v_isSharedCheck_1256_ == 0 {
                        v___x_1249_ = v_x_1244_;
                        v_isShared_1250_ = v_isSharedCheck_1256_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_1247_);
                        leanh::lean_dec(v_x_1244_);
                        v___x_1249_ = leanh::lean_box(0);
                        v_isShared_1250_ = v_isSharedCheck_1256_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_1251_ = l_List_reverse___redArg(v_a_1247_);
                if v_isShared_1250_ == 0 {
                    leanh::lean_ctor_set(v___x_1249_, 0, v___x_1251_);
                    v___x_1253_ = v___x_1249_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1255_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1255_, 0, v___x_1251_);
                    v___x_1253_ = v_reuseFailAlloc_1255_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_1254_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_1254_, 0, v___x_1253_);
                return v___x_1254_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Queue_filterM___at___00Std_Notify_selector_spec__1___lam__0___boxed(
    mut v_x_1257_: *mut leanh::LeanObject,
    mut v___y_1258_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1259_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1259_ = l_Std_Queue_filterM___at___00Std_Notify_selector_spec__1___lam__0(v_x_1257_);
    return v_res_1259_;
}
pub unsafe fn l_Std_Queue_filterM___at___00Std_Notify_selector_spec__1___lam__2(
    mut v_a_1260_: *mut leanh::LeanObject,
    mut v___x_1261_: *mut leanh::LeanObject,
    mut v_x_1262_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_a_1264_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1266_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1267_: u8 = 0;
    let mut v___x_1269_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1270_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1271_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1272_: u8 = 0;
    let mut v_a_1273_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1275_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1276_: u8 = 0;
    let mut v___x_1277_: u8 = 0;
    let mut v___x_1278_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1280_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1281_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1282_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1283_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1284_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1286_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1287_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1288_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1289_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_1262_) == 0 {
                    leanh::lean_dec(v___x_1261_);
                    leanh::lean_dec(v_a_1260_);
                    v_a_1264_ = leanh::lean_ctor_get(v_x_1262_, 0);
                    v_isSharedCheck_1272_ = (!leanh::lean_is_exclusive(v_x_1262_)) as u8;
                    if v_isSharedCheck_1272_ == 0 {
                        v___x_1266_ = v_x_1262_;
                        v_isShared_1267_ = v_isSharedCheck_1272_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_1264_);
                        leanh::lean_dec(v_x_1262_);
                        v___x_1266_ = leanh::lean_box(0);
                        v_isShared_1267_ = v_isSharedCheck_1272_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_1273_ = leanh::lean_ctor_get(v_x_1262_, 0);
                    v_isSharedCheck_1289_ = (!leanh::lean_is_exclusive(v_x_1262_)) as u8;
                    if v_isSharedCheck_1289_ == 0 {
                        v___x_1275_ = v_x_1262_;
                        v_isShared_1276_ = v_isSharedCheck_1289_;
                        state = 3;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_1273_);
                        leanh::lean_dec(v_x_1262_);
                        v___x_1275_ = leanh::lean_box(0);
                        v_isShared_1276_ = v_isSharedCheck_1289_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_1267_ == 0 {
                    v___x_1269_ = v___x_1266_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1271_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1271_, 0, v_a_1264_);
                    v___x_1269_ = v_reuseFailAlloc_1271_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_1270_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_1270_, 0, v___x_1269_);
                return v___x_1270_;
            }
            3 => {
                v___x_1277_ = l_List_isEmpty___redArg(v_a_1260_);
                if v___x_1277_ == 0 {
                    leanh::lean_dec(v___x_1261_);
                    v___x_1278_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_1278_, 0, v_a_1273_);
                    leanh::lean_ctor_set(v___x_1278_, 1, v_a_1260_);
                    if v_isShared_1276_ == 0 {
                        leanh::lean_ctor_set(v___x_1275_, 0, v___x_1278_);
                        v___x_1280_ = v___x_1275_;
                        state = 4;
                        continue;
                    } else {
                        v_reuseFailAlloc_1282_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_1282_, 0, v___x_1278_);
                        v___x_1280_ = v_reuseFailAlloc_1282_;
                        state = 4;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v_a_1260_);
                    v___x_1283_ = l_List_reverse___redArg(v_a_1273_);
                    v___x_1284_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_1284_, 0, v___x_1261_);
                    leanh::lean_ctor_set(v___x_1284_, 1, v___x_1283_);
                    if v_isShared_1276_ == 0 {
                        leanh::lean_ctor_set(v___x_1275_, 0, v___x_1284_);
                        v___x_1286_ = v___x_1275_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_1288_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_1288_, 0, v___x_1284_);
                        v___x_1286_ = v_reuseFailAlloc_1288_;
                        state = 5;
                        continue;
                    }
                }
            }
            4 => {
                v___x_1281_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_1281_, 0, v___x_1280_);
                return v___x_1281_;
            }
            5 => {
                v___x_1287_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_1287_, 0, v___x_1286_);
                return v___x_1287_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Queue_filterM___at___00Std_Notify_selector_spec__1___lam__2___boxed(
    mut v_a_1290_: *mut leanh::LeanObject,
    mut v___x_1291_: *mut leanh::LeanObject,
    mut v_x_1292_: *mut leanh::LeanObject,
    mut v___y_1293_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1294_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1294_ = l_Std_Queue_filterM___at___00Std_Notify_selector_spec__1___lam__2(
        v_a_1290_,
        v___x_1291_,
        v_x_1292_,
    );
    return v_res_1294_;
}
pub unsafe fn l_Std_Queue_filterM___at___00Std_Notify_selector_spec__1___lam__1(
    mut v_eList_1295_: *mut leanh::LeanObject,
    mut v___x_1296_: *mut leanh::LeanObject,
    mut v___f_1297_: *mut leanh::LeanObject,
    mut v_x_1298_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_a_1300_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1302_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1303_: u8 = 0;
    let mut v___x_1305_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1306_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1307_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1308_: u8 = 0;
    let mut v_a_1309_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1310_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1311_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1312_: u8 = 0;
    let mut v___x_1313_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1314_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1315_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_1298_) == 0 {
                    leanh::lean_dec_ref(v___f_1297_);
                    leanh::lean_dec(v___x_1296_);
                    leanh::lean_dec(v_eList_1295_);
                    v_a_1300_ = leanh::lean_ctor_get(v_x_1298_, 0);
                    v_isSharedCheck_1308_ = (!leanh::lean_is_exclusive(v_x_1298_)) as u8;
                    if v_isSharedCheck_1308_ == 0 {
                        v___x_1302_ = v_x_1298_;
                        v_isShared_1303_ = v_isSharedCheck_1308_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_1300_);
                        leanh::lean_dec(v_x_1298_);
                        v___x_1302_ = leanh::lean_box(0);
                        v_isShared_1303_ = v_isSharedCheck_1308_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_1309_ = leanh::lean_ctor_get(v_x_1298_, 0);
                    leanh::lean_inc(v_a_1309_);
                    leanh::lean_dec_ref_known(v_x_1298_, 1);
                    leanh::lean_inc(v___x_1296_);
                    v___x_1310_ = l_List_filterAuxM___at___00Std_Queue_filterM___at___00Std_Notify_selector_spec__1_spec__1___redArg(v_eList_1295_, v___x_1296_);
                    v___x_1311_ = leanh::lean_unsigned_to_nat(0);
                    v___x_1312_ = 0;
                    v___x_1313_ =
                        l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(
                            leanh::lean_box(0),
                            leanh::lean_box(0),
                            v___x_1311_,
                            v___x_1312_,
                            v___x_1310_,
                            v___f_1297_,
                        );
                    v___f_1314_ = leanh::lean_alloc_closure(
                        l_Std_Queue_filterM___at___00Std_Notify_selector_spec__1___lam__2___boxed
                            as *mut core::ffi::c_void,
                        4,
                        2,
                    );
                    leanh::lean_closure_set(v___f_1314_, 0, v_a_1309_);
                    leanh::lean_closure_set(v___f_1314_, 1, v___x_1296_);
                    v___x_1315_ =
                        l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(
                            leanh::lean_box(0),
                            leanh::lean_box(0),
                            v___x_1311_,
                            v___x_1312_,
                            v___x_1313_,
                            v___f_1314_,
                        );
                    return v___x_1315_;
                }
            }
            1 => {
                if v_isShared_1303_ == 0 {
                    v___x_1305_ = v___x_1302_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1307_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1307_, 0, v_a_1300_);
                    v___x_1305_ = v_reuseFailAlloc_1307_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_1306_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_1306_, 0, v___x_1305_);
                return v___x_1306_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Queue_filterM___at___00Std_Notify_selector_spec__1___lam__1___boxed(
    mut v_eList_1316_: *mut leanh::LeanObject,
    mut v___x_1317_: *mut leanh::LeanObject,
    mut v___f_1318_: *mut leanh::LeanObject,
    mut v_x_1319_: *mut leanh::LeanObject,
    mut v___y_1320_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1321_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1321_ = l_Std_Queue_filterM___at___00Std_Notify_selector_spec__1___lam__1(
        v_eList_1316_,
        v___x_1317_,
        v___f_1318_,
        v_x_1319_,
    );
    return v_res_1321_;
}
pub unsafe fn l_Std_Queue_filterM___at___00Std_Notify_selector_spec__1(
    mut v_q_1323_: *mut leanh::LeanObject,
    mut v___y_1324_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_eList_1326_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_dList_1327_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1328_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1329_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1330_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1331_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1332_: u8 = 0;
    let mut v___x_1333_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1334_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1335_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_eList_1326_ = leanh::lean_ctor_get(v_q_1323_, 0);
    leanh::lean_inc(v_eList_1326_);
    v_dList_1327_ = leanh::lean_ctor_get(v_q_1323_, 1);
    leanh::lean_inc(v_dList_1327_);
    leanh::lean_dec_ref(v_q_1323_);
    v___x_1328_ = leanh::lean_box(0);
    v___x_1329_ = l_List_filterAuxM___at___00Std_Queue_filterM___at___00Std_Notify_selector_spec__1_spec__1___redArg(v_dList_1327_, v___x_1328_);
    v___f_1330_ = l_Std_Queue_filterM___at___00Std_Notify_selector_spec__1___closed__0;
    v___x_1331_ = leanh::lean_unsigned_to_nat(0);
    v___x_1332_ = 0;
    v___x_1333_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(
        leanh::lean_box(0),
        leanh::lean_box(0),
        v___x_1331_,
        v___x_1332_,
        v___x_1329_,
        v___f_1330_,
    );
    v___f_1334_ = leanh::lean_alloc_closure(
        l_Std_Queue_filterM___at___00Std_Notify_selector_spec__1___lam__1___boxed
            as *mut core::ffi::c_void,
        5,
        3,
    );
    leanh::lean_closure_set(v___f_1334_, 0, v_eList_1326_);
    leanh::lean_closure_set(v___f_1334_, 1, v___x_1328_);
    leanh::lean_closure_set(v___f_1334_, 2, v___f_1330_);
    v___x_1335_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(
        leanh::lean_box(0),
        leanh::lean_box(0),
        v___x_1331_,
        v___x_1332_,
        v___x_1333_,
        v___f_1334_,
    );
    return v___x_1335_;
}
pub unsafe fn l_Std_Queue_filterM___at___00Std_Notify_selector_spec__1___boxed(
    mut v_q_1336_: *mut leanh::LeanObject,
    mut v___y_1337_: *mut leanh::LeanObject,
    mut v___y_1338_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1339_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1339_ = l_Std_Queue_filterM___at___00Std_Notify_selector_spec__1(v_q_1336_, v___y_1337_);
    leanh::lean_dec(v___y_1337_);
    return v_res_1339_;
}
pub unsafe fn l_Std_Notify_selector___lam__1(
    mut v___y_1340_: *mut leanh::LeanObject,
    mut v___f_1341_: *mut leanh::LeanObject,
    mut v_x_1342_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_a_1344_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1346_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1347_: u8 = 0;
    let mut v___x_1349_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1350_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1351_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1352_: u8 = 0;
    let mut v_a_1353_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1354_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1355_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1356_: u8 = 0;
    let mut v___x_1357_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_1342_) == 0 {
                    leanh::lean_dec_ref(v___f_1341_);
                    v_a_1344_ = leanh::lean_ctor_get(v_x_1342_, 0);
                    v_isSharedCheck_1352_ = (!leanh::lean_is_exclusive(v_x_1342_)) as u8;
                    if v_isSharedCheck_1352_ == 0 {
                        v___x_1346_ = v_x_1342_;
                        v_isShared_1347_ = v_isSharedCheck_1352_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_1344_);
                        leanh::lean_dec(v_x_1342_);
                        v___x_1346_ = leanh::lean_box(0);
                        v_isShared_1347_ = v_isSharedCheck_1352_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_1353_ = leanh::lean_ctor_get(v_x_1342_, 0);
                    leanh::lean_inc(v_a_1353_);
                    leanh::lean_dec_ref_known(v_x_1342_, 1);
                    v___x_1354_ = l_Std_Queue_filterM___at___00Std_Notify_selector_spec__1(
                        v_a_1353_,
                        v___y_1340_,
                    );
                    v___x_1355_ = leanh::lean_unsigned_to_nat(0);
                    v___x_1356_ = 0;
                    v___x_1357_ =
                        l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(
                            leanh::lean_box(0),
                            leanh::lean_box(0),
                            v___x_1355_,
                            v___x_1356_,
                            v___x_1354_,
                            v___f_1341_,
                        );
                    return v___x_1357_;
                }
            }
            1 => {
                if v_isShared_1347_ == 0 {
                    v___x_1349_ = v___x_1346_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1351_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1351_, 0, v_a_1344_);
                    v___x_1349_ = v_reuseFailAlloc_1351_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_1350_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_1350_, 0, v___x_1349_);
                return v___x_1350_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Notify_selector___lam__1___boxed(
    mut v___y_1358_: *mut leanh::LeanObject,
    mut v___f_1359_: *mut leanh::LeanObject,
    mut v_x_1360_: *mut leanh::LeanObject,
    mut v___y_1361_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1362_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1362_ = l_Std_Notify_selector___lam__1(v___y_1358_, v___f_1359_, v_x_1360_);
    leanh::lean_dec(v___y_1358_);
    return v_res_1362_;
}
pub unsafe fn l_Std_Notify_selector___lam__2(
    mut v___y_1363_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1365_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1366_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1367_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1368_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1369_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1370_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1371_: u8 = 0;
    let mut v___x_1372_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1365_ = lean_st_ref_get(v___y_1363_);
    leanh::lean_inc_n(v___y_1363_, 2);
    v___f_1366_ = leanh::lean_alloc_closure(
        l_Std_Notify_selector___lam__0___boxed as *mut core::ffi::c_void,
        3,
        1,
    );
    leanh::lean_closure_set(v___f_1366_, 0, v___y_1363_);
    v___f_1367_ = leanh::lean_alloc_closure(
        l_Std_Notify_selector___lam__1___boxed as *mut core::ffi::c_void,
        4,
        2,
    );
    leanh::lean_closure_set(v___f_1367_, 0, v___y_1363_);
    leanh::lean_closure_set(v___f_1367_, 1, v___f_1366_);
    v___x_1368_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_1368_, 0, v___x_1365_);
    v___x_1369_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_1369_, 0, v___x_1368_);
    v___x_1370_ = leanh::lean_unsigned_to_nat(0);
    v___x_1371_ = 0;
    v___x_1372_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(
        leanh::lean_box(0),
        leanh::lean_box(0),
        v___x_1370_,
        v___x_1371_,
        v___x_1369_,
        v___f_1367_,
    );
    return v___x_1372_;
}
pub unsafe fn l_Std_Notify_selector___lam__2___boxed(
    mut v___y_1373_: *mut leanh::LeanObject,
    mut v___y_1374_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1375_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1375_ = l_Std_Notify_selector___lam__2(v___y_1373_);
    leanh::lean_dec(v___y_1373_);
    return v_res_1375_;
}
pub unsafe fn l_Std_Notify_selector___lam__3(
    mut v_waiter_1380_: *mut leanh::LeanObject,
    mut v___y_1381_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1383_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1384_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1385_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1386_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1387_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1383_ = lean_st_ref_take(v___y_1381_);
    v___x_1384_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_1384_, 0, v_waiter_1380_);
    v___x_1385_ = l_Std_Queue_enqueue___redArg(v___x_1384_, v___x_1383_);
    v___x_1386_ = lean_st_ref_set(v___y_1381_, v___x_1385_);
    v___x_1387_ = l_Std_Notify_selector___lam__3___closed__1;
    return v___x_1387_;
}
pub unsafe fn l_Std_Notify_selector___lam__3___boxed(
    mut v_waiter_1388_: *mut leanh::LeanObject,
    mut v___y_1389_: *mut leanh::LeanObject,
    mut v___y_1390_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1391_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1391_ = l_Std_Notify_selector___lam__3(v_waiter_1388_, v___y_1389_);
    leanh::lean_dec(v___y_1389_);
    return v_res_1391_;
}
pub unsafe fn l_Std_Notify_selector___lam__4(
    mut v_notify_1392_: *mut leanh::LeanObject,
    mut v_waiter_1393_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_1395_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1396_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_1395_ = leanh::lean_alloc_closure(
        l_Std_Notify_selector___lam__3___boxed as *mut core::ffi::c_void,
        3,
        1,
    );
    leanh::lean_closure_set(v___f_1395_, 0, v_waiter_1393_);
    v___x_1396_ = l_Std_Mutex_atomically___at___00Std_Notify_selector_spec__0___redArg(
        v_notify_1392_,
        v___f_1395_,
    );
    return v___x_1396_;
}
pub unsafe fn l_Std_Notify_selector___lam__4___boxed(
    mut v_notify_1397_: *mut leanh::LeanObject,
    mut v_waiter_1398_: *mut leanh::LeanObject,
    mut v___y_1399_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1400_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1400_ = l_Std_Notify_selector___lam__4(v_notify_1397_, v_waiter_1398_);
    return v_res_1400_;
}
pub unsafe fn l_Std_Notify_selector___lam__5(
    mut v___x_1401_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1403_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1404_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1403_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_1403_, 0, v___x_1401_);
    v___x_1404_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_1404_, 0, v___x_1403_);
    return v___x_1404_;
}
pub unsafe fn l_Std_Notify_selector___lam__5___boxed(
    mut v___x_1405_: *mut leanh::LeanObject,
    mut v___y_1406_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1407_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1407_ = l_Std_Notify_selector___lam__5(v___x_1405_);
    return v_res_1407_;
}
pub unsafe fn l_Std_Notify_selector(
    mut v_notify_1411_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_1412_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1413_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1414_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1415_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1416_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_1412_ = l_Std_Notify_selector___closed__0;
    leanh::lean_inc_ref(v_notify_1411_);
    v___f_1413_ = leanh::lean_alloc_closure(
        l_Std_Notify_selector___lam__4___boxed as *mut core::ffi::c_void,
        3,
        1,
    );
    leanh::lean_closure_set(v___f_1413_, 0, v_notify_1411_);
    v___f_1414_ = l_Std_Notify_selector___closed__1;
    v___x_1415_ = leanh::lean_alloc_closure(
        l_Std_Mutex_atomically___at___00Std_Notify_selector_spec__0___boxed
            as *mut core::ffi::c_void,
        5,
        4,
    );
    leanh::lean_closure_set(v___x_1415_, 0, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_1415_, 1, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_1415_, 2, v_notify_1411_);
    leanh::lean_closure_set(v___x_1415_, 3, v___f_1412_);
    v___x_1416_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
    leanh::lean_ctor_set(v___x_1416_, 0, v___f_1414_);
    leanh::lean_ctor_set(v___x_1416_, 1, v___f_1413_);
    leanh::lean_ctor_set(v___x_1416_, 2, v___x_1415_);
    return v___x_1416_;
}
pub unsafe fn l_List_filterAuxM___at___00Std_Queue_filterM___at___00Std_Notify_selector_spec__1_spec__1(
    mut v_x_1417_: *mut leanh::LeanObject,
    mut v_x_1418_: *mut leanh::LeanObject,
    mut v___y_1419_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1421_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1421_ = l_List_filterAuxM___at___00Std_Queue_filterM___at___00Std_Notify_selector_spec__1_spec__1___redArg(v_x_1417_, v_x_1418_);
    return v___x_1421_;
}
pub unsafe fn l_List_filterAuxM___at___00Std_Queue_filterM___at___00Std_Notify_selector_spec__1_spec__1___boxed(
    mut v_x_1422_: *mut leanh::LeanObject,
    mut v_x_1423_: *mut leanh::LeanObject,
    mut v___y_1424_: *mut leanh::LeanObject,
    mut v___y_1425_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1426_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1426_ =
        l_List_filterAuxM___at___00Std_Queue_filterM___at___00Std_Notify_selector_spec__1_spec__1(
            v_x_1422_,
            v_x_1423_,
            v___y_1424_,
        );
    leanh::lean_dec(v___y_1424_);
    return v_res_1426_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Std_Sync_Notify(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Init_Data_Queue(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Std_Sync_Mutex(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Std_Async_Select(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Std_Sync_Notify(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_meta_initialized = true;
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Std_Sync_Notify(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Init_Data_Queue(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Std_Sync_Mutex(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Std_Async_Select(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Std_Sync_Notify(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = meta_initialize_Std_Sync_Notify(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return initialize_Std_Sync_Notify(builtin);
}