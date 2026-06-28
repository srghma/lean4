// Lean compiler output
// Module: Std.Sync.Notify
// Imports: Init.Data.Queue Std.Sync.Mutex Std.Async.Select
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
use crate::lean_imports_rs::Init::Core::{lean_task_map, lean_task_pure};
use crate::lean_imports_rs::Init::System::IO::lean_io_bind_task;
use crate::lean_imports_rs::Init::System::Promise::{
    lean_io_promise_new, lean_io_promise_resolve, lean_io_promise_result_opt,
};
use crate::lean_imports_rs::Init::System::ST::{
    lean_st_ref_get, lean_st_ref_set, lean_st_ref_take,
};
use crate::lean_imports_rs::Std::Sync::Mutex::{lean_io_basemutex_lock, lean_io_basemutex_unlock};
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_alloc_closure, lean_alloc_ctor, lean_apply_1,
    lean_apply_2, lean_box, lean_closure_set, lean_ctor_get, lean_ctor_set, lean_dec, lean_dec_ref,
    lean_dec_ref_known, lean_inc, lean_inc_n, lean_inc_ref, lean_io_result_is_error,
    lean_io_result_mk_ok, lean_is_exclusive, lean_obj_once, lean_obj_tag, lean_unbox,
    lean_unsigned_to_nat,
};
pub static l_Std_Notify_Consumer_resolve___redArg___closed__0_value: LeanClosureObject<1> =
    LeanClosureObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut LeanObject>() * 1) as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Std_Notify_Consumer_resolve___redArg___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 1,
        m_objs: [(((0 as usize) << 1) | 1) as *mut LeanObject],
    };
static mut l_Std_Notify_Consumer_resolve___redArg___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Notify_Consumer_resolve___redArg___closed__0_value)
        as *mut LeanObject;
static mut l_Std_Notify_new___closed__0_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_Notify_new___closed__0: *mut LeanObject = core::ptr::null_mut();
pub static l_Std_Notify_notify___closed__0_value: LeanClosureObject<0> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Std_Notify_notify___lam__0___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_Notify_notify___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Notify_notify___closed__0_value) as *mut LeanObject;
pub static l_Std_Notify_notifyOne___closed__0_value: LeanClosureObject<0> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Std_Notify_notifyOne___lam__0___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_Notify_notifyOne___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Notify_notifyOne___closed__0_value) as *mut LeanObject;
pub static l_Std_Notify_wait___lam__0___closed__0_value: LeanStringObject<15> = LeanStringObject {
    m_header: LeanObject {
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
static mut l_Std_Notify_wait___lam__0___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Notify_wait___lam__0___closed__0_value) as *mut LeanObject;
static mut l_Std_Notify_wait___lam__0___closed__1_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_Notify_wait___lam__0___closed__1: *mut LeanObject = core::ptr::null_mut();
static mut l_Std_Notify_wait___lam__0___closed__2_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_Notify_wait___lam__0___closed__2: *mut LeanObject = core::ptr::null_mut();
static mut l_Std_Notify_wait___lam__0___closed__3_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_Notify_wait___lam__0___closed__3: *mut LeanObject = core::ptr::null_mut();
pub static l_Std_Notify_wait___closed__0_value: LeanClosureObject<0> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Std_Notify_wait___lam__0___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_Notify_wait___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Notify_wait___closed__0_value) as *mut LeanObject;
pub static l_Std_Notify_wait___closed__1_value: LeanClosureObject<1> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 1) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Std_Notify_wait___lam__1___boxed as *const core::ffi::c_void,
    m_arity: 3,
    m_num_fixed: 1,
    m_objs: [core::ptr::addr_of!(l_Std_Notify_wait___closed__0_value) as *mut LeanObject],
};
static mut l_Std_Notify_wait___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Notify_wait___closed__1_value) as *mut LeanObject;
pub static l_Std_Mutex_atomically___at___00Std_Notify_selector_spec__0___redArg___closed__0_value: LeanClosureObject<0> = LeanClosureObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Std_Mutex_atomically___at___00Std_Notify_selector_spec__0___redArg___lam__3 as *const core::ffi::c_void, m_arity: 1, m_num_fixed: 0, m_objs: [] };
static mut l_Std_Mutex_atomically___at___00Std_Notify_selector_spec__0___redArg___closed__0:
    *mut LeanObject = core::ptr::addr_of!(
    l_Std_Mutex_atomically___at___00Std_Notify_selector_spec__0___redArg___closed__0_value
) as *mut LeanObject;
pub static l_List_filterAuxM___at___00Std_Queue_filterM___at___00Std_Notify_selector_spec__1_spec__1___redArg___closed__0_value: LeanCtorObject<1> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*1 + 0) as u16, other: 1, tag: 1 }, m_objs: [((( 1 as usize) << 1) | 1) as *mut LeanObject] };
static mut l_List_filterAuxM___at___00Std_Queue_filterM___at___00Std_Notify_selector_spec__1_spec__1___redArg___closed__0: *mut LeanObject = core::ptr::addr_of!(l_List_filterAuxM___at___00Std_Queue_filterM___at___00Std_Notify_selector_spec__1_spec__1___redArg___closed__0_value) as *mut LeanObject;
pub static l_List_filterAuxM___at___00Std_Queue_filterM___at___00Std_Notify_selector_spec__1_spec__1___redArg___closed__1_value: LeanCtorObject<1> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*1 + 0) as u16, other: 1, tag: 0 }, m_objs: [core::ptr::addr_of!(l_List_filterAuxM___at___00Std_Queue_filterM___at___00Std_Notify_selector_spec__1_spec__1___redArg___closed__0_value) as *mut LeanObject] };
static mut l_List_filterAuxM___at___00Std_Queue_filterM___at___00Std_Notify_selector_spec__1_spec__1___redArg___closed__1: *mut LeanObject = core::ptr::addr_of!(l_List_filterAuxM___at___00Std_Queue_filterM___at___00Std_Notify_selector_spec__1_spec__1___redArg___closed__1_value) as *mut LeanObject;
pub static l_List_filterAuxM___at___00Std_Queue_filterM___at___00Std_Notify_selector_spec__1_spec__1___redArg___closed__2_value: LeanClosureObject<0> = LeanClosureObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_List_filterAuxM___at___00Std_Queue_filterM___at___00Std_Notify_selector_spec__1_spec__1___redArg___lam__1___boxed as *const core::ffi::c_void, m_arity: 2, m_num_fixed: 0, m_objs: [] };
static mut l_List_filterAuxM___at___00Std_Queue_filterM___at___00Std_Notify_selector_spec__1_spec__1___redArg___closed__2: *mut LeanObject = core::ptr::addr_of!(l_List_filterAuxM___at___00Std_Queue_filterM___at___00Std_Notify_selector_spec__1_spec__1___redArg___closed__2_value) as *mut LeanObject;
pub static l_Std_Queue_filterM___at___00Std_Notify_selector_spec__1___closed__0_value:
    LeanClosureObject<0> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Std_Queue_filterM___at___00Std_Notify_selector_spec__1___lam__0___boxed
        as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_Queue_filterM___at___00Std_Notify_selector_spec__1___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Queue_filterM___at___00Std_Notify_selector_spec__1___closed__0_value)
        as *mut LeanObject;
pub static l_Std_Notify_selector___lam__3___closed__0_value: LeanCtorObject<1> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 1,
    },
    m_objs: [(((0 as usize) << 1) | 1) as *mut LeanObject],
};
static mut l_Std_Notify_selector___lam__3___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Notify_selector___lam__3___closed__0_value) as *mut LeanObject;
pub static l_Std_Notify_selector___lam__3___closed__1_value: LeanCtorObject<1> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 0,
    },
    m_objs: [
        core::ptr::addr_of!(l_Std_Notify_selector___lam__3___closed__0_value) as *mut LeanObject,
    ],
};
static mut l_Std_Notify_selector___lam__3___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Notify_selector___lam__3___closed__1_value) as *mut LeanObject;
pub static l_Std_Notify_selector___closed__0_value: LeanClosureObject<0> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Std_Notify_selector___lam__2___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_Notify_selector___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Notify_selector___closed__0_value) as *mut LeanObject;
pub static l_Std_Notify_selector___closed__1_value: LeanClosureObject<1> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 1) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Std_Notify_selector___lam__5___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 1,
    m_objs: [(((0 as usize) << 1) | 1) as *mut LeanObject],
};
static mut l_Std_Notify_selector___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Notify_selector___closed__1_value) as *mut LeanObject;
pub unsafe fn l_Std_Notify_Consumer_ctorIdx___redArg(
    mut v_x_714_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_714_) == 0 {
        let mut v___x_715_: *mut LeanObject = core::ptr::null_mut();
        v___x_715_ = lean_unsigned_to_nat(0);
        return v___x_715_;
    } else {
        let mut v___x_716_: *mut LeanObject = core::ptr::null_mut();
        v___x_716_ = lean_unsigned_to_nat(1);
        return v___x_716_;
    }
}
pub unsafe fn l_Std_Notify_Consumer_ctorIdx___redArg___boxed(
    mut v_x_717_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_718_: *mut LeanObject = core::ptr::null_mut();
    v_res_718_ = l_Std_Notify_Consumer_ctorIdx___redArg(v_x_717_);
    lean_dec_ref(v_x_717_);
    return v_res_718_;
}
pub unsafe fn l_Std_Notify_Consumer_ctorIdx(
    mut v_00_u03b1_719_: *mut LeanObject,
    mut v_x_720_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_721_: *mut LeanObject = core::ptr::null_mut();
    v___x_721_ = l_Std_Notify_Consumer_ctorIdx___redArg(v_x_720_);
    return v___x_721_;
}
pub unsafe fn l_Std_Notify_Consumer_ctorIdx___boxed(
    mut v_00_u03b1_722_: *mut LeanObject,
    mut v_x_723_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_724_: *mut LeanObject = core::ptr::null_mut();
    v_res_724_ = l_Std_Notify_Consumer_ctorIdx(v_00_u03b1_722_, v_x_723_);
    lean_dec_ref(v_x_723_);
    return v_res_724_;
}
pub unsafe fn l_Std_Notify_Consumer_ctorElim___redArg(
    mut v_t_725_: *mut LeanObject,
    mut v_k_726_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_t_725_) == 0 {
        let mut v_promise_727_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_728_: *mut LeanObject = core::ptr::null_mut();
        v_promise_727_ = lean_ctor_get(v_t_725_, 0);
        lean_inc(v_promise_727_);
        lean_dec_ref_known(v_t_725_, 1);
        v___x_728_ = lean_apply_1(v_k_726_, v_promise_727_);
        return v___x_728_;
    } else {
        let mut v_finished_729_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_730_: *mut LeanObject = core::ptr::null_mut();
        v_finished_729_ = lean_ctor_get(v_t_725_, 0);
        lean_inc_ref(v_finished_729_);
        lean_dec_ref_known(v_t_725_, 1);
        v___x_730_ = lean_apply_1(v_k_726_, v_finished_729_);
        return v___x_730_;
    }
}
pub unsafe fn l_Std_Notify_Consumer_ctorElim(
    mut v_00_u03b1_731_: *mut LeanObject,
    mut v_motive_732_: *mut LeanObject,
    mut v_ctorIdx_733_: *mut LeanObject,
    mut v_t_734_: *mut LeanObject,
    mut v_h_735_: *mut LeanObject,
    mut v_k_736_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_737_: *mut LeanObject = core::ptr::null_mut();
    v___x_737_ = l_Std_Notify_Consumer_ctorElim___redArg(v_t_734_, v_k_736_);
    return v___x_737_;
}
pub unsafe fn l_Std_Notify_Consumer_ctorElim___boxed(
    mut v_00_u03b1_738_: *mut LeanObject,
    mut v_motive_739_: *mut LeanObject,
    mut v_ctorIdx_740_: *mut LeanObject,
    mut v_t_741_: *mut LeanObject,
    mut v_h_742_: *mut LeanObject,
    mut v_k_743_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_744_: *mut LeanObject = core::ptr::null_mut();
    v_res_744_ = l_Std_Notify_Consumer_ctorElim(
        v_00_u03b1_738_,
        v_motive_739_,
        v_ctorIdx_740_,
        v_t_741_,
        v_h_742_,
        v_k_743_,
    );
    lean_dec(v_ctorIdx_740_);
    return v_res_744_;
}
pub unsafe fn l_Std_Notify_Consumer_normal_elim___redArg(
    mut v_t_745_: *mut LeanObject,
    mut v_normal_746_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_747_: *mut LeanObject = core::ptr::null_mut();
    v___x_747_ = l_Std_Notify_Consumer_ctorElim___redArg(v_t_745_, v_normal_746_);
    return v___x_747_;
}
pub unsafe fn l_Std_Notify_Consumer_normal_elim(
    mut v_00_u03b1_748_: *mut LeanObject,
    mut v_motive_749_: *mut LeanObject,
    mut v_t_750_: *mut LeanObject,
    mut v_h_751_: *mut LeanObject,
    mut v_normal_752_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_753_: *mut LeanObject = core::ptr::null_mut();
    v___x_753_ = l_Std_Notify_Consumer_ctorElim___redArg(v_t_750_, v_normal_752_);
    return v___x_753_;
}
pub unsafe fn l_Std_Notify_Consumer_select_elim___redArg(
    mut v_t_754_: *mut LeanObject,
    mut v_select_755_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_756_: *mut LeanObject = core::ptr::null_mut();
    v___x_756_ = l_Std_Notify_Consumer_ctorElim___redArg(v_t_754_, v_select_755_);
    return v___x_756_;
}
pub unsafe fn l_Std_Notify_Consumer_select_elim(
    mut v_00_u03b1_757_: *mut LeanObject,
    mut v_motive_758_: *mut LeanObject,
    mut v_t_759_: *mut LeanObject,
    mut v_h_760_: *mut LeanObject,
    mut v_select_761_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_762_: *mut LeanObject = core::ptr::null_mut();
    v___x_762_ = l_Std_Notify_Consumer_ctorElim___redArg(v_t_759_, v_select_761_);
    return v___x_762_;
}
pub unsafe fn l_Std_Async_Waiter_race___at___00Std_Notify_Consumer_resolve_spec__0___redArg(
    mut v_x_763_: *mut LeanObject,
    mut v_w_764_: *mut LeanObject,
    mut v_lose_765_: *mut LeanObject,
) -> u8 {
    let mut v_finished_767_: *mut LeanObject = core::ptr::null_mut();
    let mut v_promise_768_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_769_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_771_: u8 = 0;
    let mut v___x_772_: u8 = 0;
    let mut v___x_773_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_774_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_775_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_776_: u8 = 0;
    let mut v___x_777_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_778_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_779_: u8 = 0;
    let mut v___x_780_: u8 = 0;
    let mut v___x_781_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_finished_767_ = lean_ctor_get(v_w_764_, 0);
                v_promise_768_ = lean_ctor_get(v_w_764_, 1);
                v___x_769_ = lean_st_ref_take(v_finished_767_);
                v___x_779_ = (lean_unbox(v___x_769_) as u8);
                lean_dec(v___x_769_);
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
                v___x_773_ = lean_box((v___x_772_) as usize);
                v___x_774_ = lean_st_ref_set(v_finished_767_, v___x_773_);
                if v___y_771_ == 0 {
                    lean_dec(v_x_763_);
                    v___x_775_ = lean_apply_1(v_lose_765_, lean_box(0));
                    v___x_776_ = (lean_unbox(v___x_775_) as u8);
                    return v___x_776_;
                } else {
                    lean_dec_ref(v_lose_765_);
                    v___x_777_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v___x_777_, 0, v_x_763_);
                    v___x_778_ = lean_io_promise_resolve(v___x_777_, v_promise_768_);
                    return v___y_771_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Async_Waiter_race___at___00Std_Notify_Consumer_resolve_spec__0___redArg___boxed(
    mut v_x_782_: *mut LeanObject,
    mut v_w_783_: *mut LeanObject,
    mut v_lose_784_: *mut LeanObject,
    mut v___y_785_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_786_: u8 = 0;
    let mut v_r_787_: *mut LeanObject = core::ptr::null_mut();
    v_res_786_ = l_Std_Async_Waiter_race___at___00Std_Notify_Consumer_resolve_spec__0___redArg(
        v_x_782_,
        v_w_783_,
        v_lose_784_,
    );
    lean_dec_ref(v_w_783_);
    v_r_787_ = lean_box((v_res_786_) as usize);
    return v_r_787_;
}
pub unsafe fn l_Std_Async_Waiter_race___at___00Std_Notify_Consumer_resolve_spec__0(
    mut v_00_u03b1_788_: *mut LeanObject,
    mut v_x_789_: *mut LeanObject,
    mut v_w_790_: *mut LeanObject,
    mut v_lose_791_: *mut LeanObject,
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
    mut v_00_u03b1_794_: *mut LeanObject,
    mut v_x_795_: *mut LeanObject,
    mut v_w_796_: *mut LeanObject,
    mut v_lose_797_: *mut LeanObject,
    mut v___y_798_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_799_: u8 = 0;
    let mut v_r_800_: *mut LeanObject = core::ptr::null_mut();
    v_res_799_ = l_Std_Async_Waiter_race___at___00Std_Notify_Consumer_resolve_spec__0(
        v_00_u03b1_794_,
        v_x_795_,
        v_w_796_,
        v_lose_797_,
    );
    lean_dec_ref(v_w_796_);
    v_r_800_ = lean_box((v_res_799_) as usize);
    return v_r_800_;
}
pub unsafe fn l_Std_Notify_Consumer_resolve___redArg___lam__0(mut v___x_801_: u8) -> u8 {
    return v___x_801_;
}
pub unsafe fn l_Std_Notify_Consumer_resolve___redArg___lam__0___boxed(
    mut v___x_803_: *mut LeanObject,
    mut v___y_804_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_400__boxed_805_: u8 = 0;
    let mut v_res_806_: u8 = 0;
    let mut v_r_807_: *mut LeanObject = core::ptr::null_mut();
    v___x_400__boxed_805_ = (lean_unbox(v___x_803_) as u8);
    v_res_806_ = l_Std_Notify_Consumer_resolve___redArg___lam__0(v___x_400__boxed_805_);
    v_r_807_ = lean_box((v_res_806_) as usize);
    return v_r_807_;
}
pub unsafe fn l_Std_Notify_Consumer_resolve___redArg(
    mut v_c_811_: *mut LeanObject,
    mut v_x_812_: *mut LeanObject,
) -> u8 {
    if lean_obj_tag(v_c_811_) == 0 {
        let mut v_promise_814_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_815_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_816_: u8 = 0;
        v_promise_814_ = lean_ctor_get(v_c_811_, 0);
        v___x_815_ = lean_io_promise_resolve(v_x_812_, v_promise_814_);
        v___x_816_ = 1;
        return v___x_816_;
    } else {
        let mut v_finished_817_: *mut LeanObject = core::ptr::null_mut();
        let mut v_lose_818_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_819_: u8 = 0;
        v_finished_817_ = lean_ctor_get(v_c_811_, 0);
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
    mut v_c_820_: *mut LeanObject,
    mut v_x_821_: *mut LeanObject,
    mut v_a_822_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_823_: u8 = 0;
    let mut v_r_824_: *mut LeanObject = core::ptr::null_mut();
    v_res_823_ = l_Std_Notify_Consumer_resolve___redArg(v_c_820_, v_x_821_);
    lean_dec_ref(v_c_820_);
    v_r_824_ = lean_box((v_res_823_) as usize);
    return v_r_824_;
}
pub unsafe fn l_Std_Notify_Consumer_resolve(
    mut v_00_u03b1_825_: *mut LeanObject,
    mut v_c_826_: *mut LeanObject,
    mut v_x_827_: *mut LeanObject,
) -> u8 {
    let mut v___x_829_: u8 = 0;
    v___x_829_ = l_Std_Notify_Consumer_resolve___redArg(v_c_826_, v_x_827_);
    return v___x_829_;
}
pub unsafe fn l_Std_Notify_Consumer_resolve___boxed(
    mut v_00_u03b1_830_: *mut LeanObject,
    mut v_c_831_: *mut LeanObject,
    mut v_x_832_: *mut LeanObject,
    mut v_a_833_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_834_: u8 = 0;
    let mut v_r_835_: *mut LeanObject = core::ptr::null_mut();
    v_res_834_ = l_Std_Notify_Consumer_resolve(v_00_u03b1_830_, v_c_831_, v_x_832_);
    lean_dec_ref(v_c_831_);
    v_r_835_ = lean_box((v_res_834_) as usize);
    return v_r_835_;
}
pub unsafe fn _init_l_Std_Notify_new___closed__0() -> *mut LeanObject {
    let mut v___x_836_: *mut LeanObject = core::ptr::null_mut();
    v___x_836_ = l_Std_Queue_empty(lean_box(0));
    return v___x_836_;
}
pub unsafe fn l_Std_Notify_new() -> *mut LeanObject {
    let mut v___x_838_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_839_: *mut LeanObject = core::ptr::null_mut();
    v___x_838_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Notify_new___closed__0),
        core::ptr::addr_of_mut!(l_Std_Notify_new___closed__0_once),
        _init_l_Std_Notify_new___closed__0,
    );
    v___x_839_ = l_Std_Mutex_new___redArg(v___x_838_);
    return v___x_839_;
}
pub unsafe fn l_Std_Notify_new___boxed(mut v_a_840_: *mut LeanObject) -> *mut LeanObject {
    let mut v_res_841_: *mut LeanObject = core::ptr::null_mut();
    v_res_841_ = l_Std_Notify_new();
    return v_res_841_;
}
pub unsafe fn l_Std_Mutex_atomically___at___00Std_Notify_notify_spec__1___redArg(
    mut v_mutex_842_: *mut LeanObject,
    mut v_k_843_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_ref_845_: *mut LeanObject = core::ptr::null_mut();
    let mut v_mutex_846_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_847_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_848_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_849_: *mut LeanObject = core::ptr::null_mut();
    v_ref_845_ = lean_ctor_get(v_mutex_842_, 0);
    lean_inc(v_ref_845_);
    v_mutex_846_ = lean_ctor_get(v_mutex_842_, 1);
    lean_inc(v_mutex_846_);
    lean_dec_ref(v_mutex_842_);
    v___x_847_ = lean_io_basemutex_lock(v_mutex_846_);
    v___x_848_ = lean_apply_2(v_k_843_, v_ref_845_, lean_box(0));
    v___x_849_ = lean_io_basemutex_unlock(v_mutex_846_);
    lean_dec(v_mutex_846_);
    return v___x_848_;
}
pub unsafe fn l_Std_Mutex_atomically___at___00Std_Notify_notify_spec__1___redArg___boxed(
    mut v_mutex_850_: *mut LeanObject,
    mut v_k_851_: *mut LeanObject,
    mut v___y_852_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_853_: *mut LeanObject = core::ptr::null_mut();
    v_res_853_ =
        l_Std_Mutex_atomically___at___00Std_Notify_notify_spec__1___redArg(v_mutex_850_, v_k_851_);
    return v_res_853_;
}
pub unsafe fn l_Std_Mutex_atomically___at___00Std_Notify_notify_spec__1(
    mut v_00_u03b1_854_: *mut LeanObject,
    mut v_00_u03b2_855_: *mut LeanObject,
    mut v_mutex_856_: *mut LeanObject,
    mut v_k_857_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_859_: *mut LeanObject = core::ptr::null_mut();
    v___x_859_ =
        l_Std_Mutex_atomically___at___00Std_Notify_notify_spec__1___redArg(v_mutex_856_, v_k_857_);
    return v___x_859_;
}
pub unsafe fn l_Std_Mutex_atomically___at___00Std_Notify_notify_spec__1___boxed(
    mut v_00_u03b1_860_: *mut LeanObject,
    mut v_00_u03b2_861_: *mut LeanObject,
    mut v_mutex_862_: *mut LeanObject,
    mut v_k_863_: *mut LeanObject,
    mut v___y_864_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_865_: *mut LeanObject = core::ptr::null_mut();
    v_res_865_ = l_Std_Mutex_atomically___at___00Std_Notify_notify_spec__1(
        v_00_u03b1_860_,
        v_00_u03b2_861_,
        v_mutex_862_,
        v_k_863_,
    );
    return v_res_865_;
}
pub unsafe fn l___private_Init_While_0__whileM_erased___at___00Std_Notify_notify_spec__0___redArg(
    mut v_a_866_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_868_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_869_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_870_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_871_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_872_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_873_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                lean_inc_ref(v_a_866_);
                v___x_868_ = l_Std_Queue_dequeue_x3f___redArg(v_a_866_);
                if lean_obj_tag(v___x_868_) == 1 {
                    lean_dec_ref(v_a_866_);
                    v_val_869_ = lean_ctor_get(v___x_868_, 0);
                    lean_inc(v_val_869_);
                    lean_dec_ref_known(v___x_868_, 1);
                    v_fst_870_ = lean_ctor_get(v_val_869_, 0);
                    lean_inc(v_fst_870_);
                    v_snd_871_ = lean_ctor_get(v_val_869_, 1);
                    lean_inc(v_snd_871_);
                    lean_dec(v_val_869_);
                    v___x_872_ = lean_box(0);
                    v___x_873_ = l_Std_Notify_Consumer_resolve___redArg(v_fst_870_, v___x_872_);
                    lean_dec(v_fst_870_);
                    v_a_866_ = v_snd_871_;
                    state = 0;
                    continue;
                } else {
                    lean_dec(v___x_868_);
                    return v_a_866_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_While_0__whileM_erased___at___00Std_Notify_notify_spec__0___redArg___boxed(
    mut v_a_875_: *mut LeanObject,
    mut v___y_876_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_877_: *mut LeanObject = core::ptr::null_mut();
    v_res_877_ =
        l___private_Init_While_0__whileM_erased___at___00Std_Notify_notify_spec__0___redArg(
            v_a_875_,
        );
    return v_res_877_;
}
pub unsafe fn l_Std_Notify_notify___lam__0(mut v___y_878_: *mut LeanObject) -> *mut LeanObject {
    let mut v___x_880_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_881_: *mut LeanObject = core::ptr::null_mut();
    let mut v_st_882_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_883_: *mut LeanObject = core::ptr::null_mut();
    v___x_880_ = lean_st_ref_get(v___y_878_);
    v___x_881_ =
        l___private_Init_While_0__whileM_erased___at___00Std_Notify_notify_spec__0___redArg(
            v___x_880_,
        );
    lean_dec_ref(v___x_881_);
    v_st_882_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Notify_new___closed__0),
        core::ptr::addr_of_mut!(l_Std_Notify_new___closed__0_once),
        _init_l_Std_Notify_new___closed__0,
    );
    v___x_883_ = lean_st_ref_set(v___y_878_, v_st_882_);
    return v___x_883_;
}
pub unsafe fn l_Std_Notify_notify___lam__0___boxed(
    mut v___y_884_: *mut LeanObject,
    mut v___y_885_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_886_: *mut LeanObject = core::ptr::null_mut();
    v_res_886_ = l_Std_Notify_notify___lam__0(v___y_884_);
    lean_dec(v___y_884_);
    return v_res_886_;
}
pub unsafe fn l_Std_Notify_notify(mut v_x_888_: *mut LeanObject) -> *mut LeanObject {
    let mut v___f_890_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_891_: *mut LeanObject = core::ptr::null_mut();
    v___f_890_ = l_Std_Notify_notify___closed__0;
    v___x_891_ =
        l_Std_Mutex_atomically___at___00Std_Notify_notify_spec__1___redArg(v_x_888_, v___f_890_);
    return v___x_891_;
}
pub unsafe fn l_Std_Notify_notify___boxed(
    mut v_x_892_: *mut LeanObject,
    mut v_a_893_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_894_: *mut LeanObject = core::ptr::null_mut();
    v_res_894_ = l_Std_Notify_notify(v_x_892_);
    return v_res_894_;
}
pub unsafe fn l___private_Init_While_0__whileM_erased___at___00Std_Notify_notify_spec__0(
    mut v_inst_895_: *mut LeanObject,
    mut v_a_896_: *mut LeanObject,
    mut v___y_897_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_899_: *mut LeanObject = core::ptr::null_mut();
    v___x_899_ =
        l___private_Init_While_0__whileM_erased___at___00Std_Notify_notify_spec__0___redArg(
            v_a_896_,
        );
    return v___x_899_;
}
pub unsafe fn l___private_Init_While_0__whileM_erased___at___00Std_Notify_notify_spec__0___boxed(
    mut v_inst_900_: *mut LeanObject,
    mut v_a_901_: *mut LeanObject,
    mut v___y_902_: *mut LeanObject,
    mut v___y_903_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_904_: *mut LeanObject = core::ptr::null_mut();
    v_res_904_ = l___private_Init_While_0__whileM_erased___at___00Std_Notify_notify_spec__0(
        v_inst_900_,
        v_a_901_,
        v___y_902_,
    );
    lean_dec(v___y_902_);
    return v_res_904_;
}
pub unsafe fn l_Std_Notify_notifyOne___lam__0(mut v___y_905_: *mut LeanObject) -> u8 {
    let mut v___x_907_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_908_: *mut LeanObject = core::ptr::null_mut();
    v___x_907_ = lean_st_ref_get(v___y_905_);
    v___x_908_ = l_Std_Queue_dequeue_x3f___redArg(v___x_907_);
    if lean_obj_tag(v___x_908_) == 1 {
        let mut v_val_909_: *mut LeanObject = core::ptr::null_mut();
        let mut v_fst_910_: *mut LeanObject = core::ptr::null_mut();
        let mut v_snd_911_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_912_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_913_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_914_: u8 = 0;
        v_val_909_ = lean_ctor_get(v___x_908_, 0);
        lean_inc(v_val_909_);
        lean_dec_ref_known(v___x_908_, 1);
        v_fst_910_ = lean_ctor_get(v_val_909_, 0);
        lean_inc(v_fst_910_);
        v_snd_911_ = lean_ctor_get(v_val_909_, 1);
        lean_inc(v_snd_911_);
        lean_dec(v_val_909_);
        v___x_912_ = lean_st_ref_set(v___y_905_, v_snd_911_);
        v___x_913_ = lean_box(0);
        v___x_914_ = l_Std_Notify_Consumer_resolve___redArg(v_fst_910_, v___x_913_);
        lean_dec(v_fst_910_);
        return v___x_914_;
    } else {
        let mut v___x_915_: u8 = 0;
        lean_dec(v___x_908_);
        v___x_915_ = 0;
        return v___x_915_;
    }
}
pub unsafe fn l_Std_Notify_notifyOne___lam__0___boxed(
    mut v___y_916_: *mut LeanObject,
    mut v___y_917_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_918_: u8 = 0;
    let mut v_r_919_: *mut LeanObject = core::ptr::null_mut();
    v_res_918_ = l_Std_Notify_notifyOne___lam__0(v___y_916_);
    lean_dec(v___y_916_);
    v_r_919_ = lean_box((v_res_918_) as usize);
    return v_r_919_;
}
pub unsafe fn l_Std_Notify_notifyOne(mut v_x_921_: *mut LeanObject) -> u8 {
    let mut v___f_923_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_924_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_925_: u8 = 0;
    v___f_923_ = l_Std_Notify_notifyOne___closed__0;
    v___x_924_ =
        l_Std_Mutex_atomically___at___00Std_Notify_notify_spec__1___redArg(v_x_921_, v___f_923_);
    v___x_925_ = (lean_unbox(v___x_924_) as u8);
    lean_dec(v___x_924_);
    return v___x_925_;
}
pub unsafe fn l_Std_Notify_notifyOne___boxed(
    mut v_x_926_: *mut LeanObject,
    mut v_a_927_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_928_: u8 = 0;
    let mut v_r_929_: *mut LeanObject = core::ptr::null_mut();
    v_res_928_ = l_Std_Notify_notifyOne(v_x_926_);
    v_r_929_ = lean_box((v_res_928_) as usize);
    return v_r_929_;
}
pub unsafe fn l_Std_Mutex_atomically___at___00Std_Notify_wait_spec__0___redArg(
    mut v_mutex_930_: *mut LeanObject,
    mut v_k_931_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_ref_933_: *mut LeanObject = core::ptr::null_mut();
    let mut v_mutex_934_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_935_: *mut LeanObject = core::ptr::null_mut();
    let mut v_r_936_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_937_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_939_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_940_: u8 = 0;
    let mut v___x_941_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_943_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_944_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_945_: u8 = 0;
    let mut v_a_946_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_948_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_949_: u8 = 0;
    let mut v___x_950_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_952_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_953_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_954_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ref_933_ = lean_ctor_get(v_mutex_930_, 0);
                lean_inc(v_ref_933_);
                v_mutex_934_ = lean_ctor_get(v_mutex_930_, 1);
                lean_inc(v_mutex_934_);
                lean_dec_ref(v_mutex_930_);
                v___x_935_ = lean_io_basemutex_lock(v_mutex_934_);
                v_r_936_ = lean_apply_2(v_k_931_, v_ref_933_, lean_box(0));
                if lean_obj_tag(v_r_936_) == 0 {
                    v_a_937_ = lean_ctor_get(v_r_936_, 0);
                    v_isSharedCheck_945_ = (!lean_is_exclusive(v_r_936_)) as u8;
                    if v_isSharedCheck_945_ == 0 {
                        v___x_939_ = v_r_936_;
                        v_isShared_940_ = v_isSharedCheck_945_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_937_);
                        lean_dec(v_r_936_);
                        v___x_939_ = lean_box(0);
                        v_isShared_940_ = v_isSharedCheck_945_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_946_ = lean_ctor_get(v_r_936_, 0);
                    v_isSharedCheck_954_ = (!lean_is_exclusive(v_r_936_)) as u8;
                    if v_isSharedCheck_954_ == 0 {
                        v___x_948_ = v_r_936_;
                        v_isShared_949_ = v_isSharedCheck_954_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_946_);
                        lean_dec(v_r_936_);
                        v___x_948_ = lean_box(0);
                        v_isShared_949_ = v_isSharedCheck_954_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v___x_941_ = lean_io_basemutex_unlock(v_mutex_934_);
                lean_dec(v_mutex_934_);
                if v_isShared_940_ == 0 {
                    v___x_943_ = v___x_939_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_944_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_944_, 0, v_a_937_);
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
                lean_dec(v_mutex_934_);
                if v_isShared_949_ == 0 {
                    v___x_952_ = v___x_948_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_953_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_953_, 0, v_a_946_);
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
    mut v_mutex_955_: *mut LeanObject,
    mut v_k_956_: *mut LeanObject,
    mut v___y_957_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_958_: *mut LeanObject = core::ptr::null_mut();
    v_res_958_ =
        l_Std_Mutex_atomically___at___00Std_Notify_wait_spec__0___redArg(v_mutex_955_, v_k_956_);
    return v_res_958_;
}
pub unsafe fn l_Std_Mutex_atomically___at___00Std_Notify_wait_spec__0(
    mut v_00_u03b1_959_: *mut LeanObject,
    mut v_00_u03b2_960_: *mut LeanObject,
    mut v_mutex_961_: *mut LeanObject,
    mut v_k_962_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_964_: *mut LeanObject = core::ptr::null_mut();
    v___x_964_ =
        l_Std_Mutex_atomically___at___00Std_Notify_wait_spec__0___redArg(v_mutex_961_, v_k_962_);
    return v___x_964_;
}
pub unsafe fn l_Std_Mutex_atomically___at___00Std_Notify_wait_spec__0___boxed(
    mut v_00_u03b1_965_: *mut LeanObject,
    mut v_00_u03b2_966_: *mut LeanObject,
    mut v_mutex_967_: *mut LeanObject,
    mut v_k_968_: *mut LeanObject,
    mut v___y_969_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_970_: *mut LeanObject = core::ptr::null_mut();
    v_res_970_ = l_Std_Mutex_atomically___at___00Std_Notify_wait_spec__0(
        v_00_u03b1_965_,
        v_00_u03b2_966_,
        v_mutex_967_,
        v_k_968_,
    );
    return v_res_970_;
}
pub unsafe fn _init_l_Std_Notify_wait___lam__0___closed__1() -> *mut LeanObject {
    let mut v___x_972_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_973_: *mut LeanObject = core::ptr::null_mut();
    v___x_972_ = l_Std_Notify_wait___lam__0___closed__0;
    v___x_973_ = lean_mk_io_user_error(v___x_972_);
    return v___x_973_;
}
pub unsafe fn _init_l_Std_Notify_wait___lam__0___closed__2() -> *mut LeanObject {
    let mut v___x_974_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_975_: *mut LeanObject = core::ptr::null_mut();
    v___x_974_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Notify_wait___lam__0___closed__1),
        core::ptr::addr_of_mut!(l_Std_Notify_wait___lam__0___closed__1_once),
        _init_l_Std_Notify_wait___lam__0___closed__1,
    );
    v___x_975_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_975_, 0, v___x_974_);
    return v___x_975_;
}
pub unsafe fn _init_l_Std_Notify_wait___lam__0___closed__3() -> *mut LeanObject {
    let mut v___x_976_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_977_: *mut LeanObject = core::ptr::null_mut();
    v___x_976_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Notify_wait___lam__0___closed__2),
        core::ptr::addr_of_mut!(l_Std_Notify_wait___lam__0___closed__2_once),
        _init_l_Std_Notify_wait___lam__0___closed__2,
    );
    v___x_977_ = lean_task_pure(v___x_976_);
    return v___x_977_;
}
pub unsafe fn l_Std_Notify_wait___lam__0(mut v_a_978_: *mut LeanObject) -> *mut LeanObject {
    let mut v___x_980_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_981_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_983_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_984_: u8 = 0;
    let mut v___x_986_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_987_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_988_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_989_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_a_978_) == 0 {
                    v___x_980_ = lean_obj_once(
                        core::ptr::addr_of_mut!(l_Std_Notify_wait___lam__0___closed__3),
                        core::ptr::addr_of_mut!(l_Std_Notify_wait___lam__0___closed__3_once),
                        _init_l_Std_Notify_wait___lam__0___closed__3,
                    );
                    return v___x_980_;
                } else {
                    v_val_981_ = lean_ctor_get(v_a_978_, 0);
                    v_isSharedCheck_989_ = (!lean_is_exclusive(v_a_978_)) as u8;
                    if v_isSharedCheck_989_ == 0 {
                        v___x_983_ = v_a_978_;
                        v_isShared_984_ = v_isSharedCheck_989_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_val_981_);
                        lean_dec(v_a_978_);
                        v___x_983_ = lean_box(0);
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
                    v_reuseFailAlloc_988_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_988_, 0, v_val_981_);
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
    mut v_a_990_: *mut LeanObject,
    mut v___y_991_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_992_: *mut LeanObject = core::ptr::null_mut();
    v_res_992_ = l_Std_Notify_wait___lam__0(v_a_990_);
    return v_res_992_;
}
pub unsafe fn l_Std_Notify_wait___lam__1(
    mut v___f_993_: *mut LeanObject,
    mut v___y_994_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_996_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_997_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_998_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_999_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1000_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1001_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1002_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1003_: u8 = 0;
    let mut v___x_1004_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1005_: *mut LeanObject = core::ptr::null_mut();
    v___x_996_ = lean_io_promise_new();
    v___x_997_ = lean_st_ref_take(v___y_994_);
    lean_inc(v___x_996_);
    v___x_998_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_998_, 0, v___x_996_);
    v___x_999_ = l_Std_Queue_enqueue___redArg(v___x_998_, v___x_997_);
    v___x_1000_ = lean_st_ref_set(v___y_994_, v___x_999_);
    v___x_1001_ = lean_io_promise_result_opt(v___x_996_);
    lean_dec(v___x_996_);
    v___x_1002_ = lean_unsigned_to_nat(0);
    v___x_1003_ = 0;
    v___x_1004_ = lean_io_bind_task(v___x_1001_, v___f_993_, v___x_1002_, v___x_1003_);
    v___x_1005_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_1005_, 0, v___x_1004_);
    return v___x_1005_;
}
pub unsafe fn l_Std_Notify_wait___lam__1___boxed(
    mut v___f_1006_: *mut LeanObject,
    mut v___y_1007_: *mut LeanObject,
    mut v___y_1008_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1009_: *mut LeanObject = core::ptr::null_mut();
    v_res_1009_ = l_Std_Notify_wait___lam__1(v___f_1006_, v___y_1007_);
    lean_dec(v___y_1007_);
    return v_res_1009_;
}
pub unsafe fn l_Std_Notify_wait(mut v_x_1013_: *mut LeanObject) -> *mut LeanObject {
    let mut v___f_1015_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1016_: *mut LeanObject = core::ptr::null_mut();
    v___f_1015_ = l_Std_Notify_wait___closed__1;
    v___x_1016_ =
        l_Std_Mutex_atomically___at___00Std_Notify_wait_spec__0___redArg(v_x_1013_, v___f_1015_);
    return v___x_1016_;
}
pub unsafe fn l_Std_Notify_wait___boxed(
    mut v_x_1017_: *mut LeanObject,
    mut v_a_1018_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1019_: *mut LeanObject = core::ptr::null_mut();
    v_res_1019_ = l_Std_Notify_wait(v_x_1017_);
    return v_res_1019_;
}
pub unsafe fn l_Std_Mutex_atomically___at___00Std_Notify_selector_spec__0___redArg___lam__0(
    mut v_mutex_1020_: *mut LeanObject,
    mut v_x_1021_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1023_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1024_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1025_: *mut LeanObject = core::ptr::null_mut();
    v___x_1023_ = lean_io_basemutex_unlock(v_mutex_1020_);
    v___x_1024_ = lean_alloc_ctor(1, 1, (0) as u32);
    lean_ctor_set(v___x_1024_, 0, v___x_1023_);
    v___x_1025_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_1025_, 0, v___x_1024_);
    return v___x_1025_;
}
pub unsafe fn l_Std_Mutex_atomically___at___00Std_Notify_selector_spec__0___redArg___lam__0___boxed(
    mut v_mutex_1026_: *mut LeanObject,
    mut v_x_1027_: *mut LeanObject,
    mut v___y_1028_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1029_: *mut LeanObject = core::ptr::null_mut();
    v_res_1029_ = l_Std_Mutex_atomically___at___00Std_Notify_selector_spec__0___redArg___lam__0(
        v_mutex_1026_,
        v_x_1027_,
    );
    lean_dec(v_x_1027_);
    lean_dec(v_mutex_1026_);
    return v_res_1029_;
}
pub unsafe fn l_Std_Mutex_atomically___at___00Std_Notify_selector_spec__0___redArg___lam__1(
    mut v_k_1030_: *mut LeanObject,
    mut v_ref_1031_: *mut LeanObject,
    mut v_x_1032_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_1034_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1036_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1037_: u8 = 0;
    let mut v___x_1039_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1040_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1041_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1042_: u8 = 0;
    let mut v___x_1043_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_1032_) == 0 {
                    lean_dec(v_ref_1031_);
                    lean_dec_ref(v_k_1030_);
                    v_a_1034_ = lean_ctor_get(v_x_1032_, 0);
                    v_isSharedCheck_1042_ = (!lean_is_exclusive(v_x_1032_)) as u8;
                    if v_isSharedCheck_1042_ == 0 {
                        v___x_1036_ = v_x_1032_;
                        v_isShared_1037_ = v_isSharedCheck_1042_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_1034_);
                        lean_dec(v_x_1032_);
                        v___x_1036_ = lean_box(0);
                        v_isShared_1037_ = v_isSharedCheck_1042_;
                        state = 1;
                        continue;
                    }
                } else {
                    lean_dec_ref_known(v_x_1032_, 1);
                    v___x_1043_ = lean_apply_2(v_k_1030_, v_ref_1031_, lean_box(0));
                    return v___x_1043_;
                }
            }
            1 => {
                if v_isShared_1037_ == 0 {
                    v___x_1039_ = v___x_1036_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1041_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1041_, 0, v_a_1034_);
                    v___x_1039_ = v_reuseFailAlloc_1041_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_1040_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_1040_, 0, v___x_1039_);
                return v___x_1040_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Mutex_atomically___at___00Std_Notify_selector_spec__0___redArg___lam__1___boxed(
    mut v_k_1044_: *mut LeanObject,
    mut v_ref_1045_: *mut LeanObject,
    mut v_x_1046_: *mut LeanObject,
    mut v___y_1047_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1048_: *mut LeanObject = core::ptr::null_mut();
    v_res_1048_ = l_Std_Mutex_atomically___at___00Std_Notify_selector_spec__0___redArg___lam__1(
        v_k_1044_,
        v_ref_1045_,
        v_x_1046_,
    );
    return v_res_1048_;
}
pub unsafe fn l_Std_Mutex_atomically___at___00Std_Notify_selector_spec__0___redArg___lam__2(
    mut v_mutex_1049_: *mut LeanObject,
    mut v___f_1050_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1052_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1053_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1054_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1055_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1056_: u8 = 0;
    let mut v___x_1057_: *mut LeanObject = core::ptr::null_mut();
    v___x_1052_ = lean_io_basemutex_lock(v_mutex_1049_);
    v___x_1053_ = lean_alloc_ctor(1, 1, (0) as u32);
    lean_ctor_set(v___x_1053_, 0, v___x_1052_);
    v___x_1054_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_1054_, 0, v___x_1053_);
    v___x_1055_ = lean_unsigned_to_nat(0);
    v___x_1056_ = 0;
    v___x_1057_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(
        lean_box(0),
        lean_box(0),
        v___x_1055_,
        v___x_1056_,
        v___x_1054_,
        v___f_1050_,
    );
    return v___x_1057_;
}
pub unsafe fn l_Std_Mutex_atomically___at___00Std_Notify_selector_spec__0___redArg___lam__2___boxed(
    mut v_mutex_1058_: *mut LeanObject,
    mut v___f_1059_: *mut LeanObject,
    mut v___y_1060_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1061_: *mut LeanObject = core::ptr::null_mut();
    v_res_1061_ = l_Std_Mutex_atomically___at___00Std_Notify_selector_spec__0___redArg___lam__2(
        v_mutex_1058_,
        v___f_1059_,
    );
    lean_dec(v_mutex_1058_);
    return v_res_1061_;
}
pub unsafe fn l_Std_Mutex_atomically___at___00Std_Notify_selector_spec__0___redArg___lam__3(
    mut v___y_1062_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_1063_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1065_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1066_: u8 = 0;
    let mut v___x_1068_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1069_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1070_: u8 = 0;
    let mut v_a_1071_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1073_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1074_: u8 = 0;
    let mut v_fst_1075_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1077_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1078_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1079_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v___y_1062_) == 0 {
                    v_a_1063_ = lean_ctor_get(v___y_1062_, 0);
                    v_isSharedCheck_1070_ = (!lean_is_exclusive(v___y_1062_)) as u8;
                    if v_isSharedCheck_1070_ == 0 {
                        v___x_1065_ = v___y_1062_;
                        v_isShared_1066_ = v_isSharedCheck_1070_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_1063_);
                        lean_dec(v___y_1062_);
                        v___x_1065_ = lean_box(0);
                        v_isShared_1066_ = v_isSharedCheck_1070_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_1071_ = lean_ctor_get(v___y_1062_, 0);
                    v_isSharedCheck_1079_ = (!lean_is_exclusive(v___y_1062_)) as u8;
                    if v_isSharedCheck_1079_ == 0 {
                        v___x_1073_ = v___y_1062_;
                        v_isShared_1074_ = v_isSharedCheck_1079_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_1071_);
                        lean_dec(v___y_1062_);
                        v___x_1073_ = lean_box(0);
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
                    v_reuseFailAlloc_1069_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1069_, 0, v_a_1063_);
                    v___x_1068_ = v_reuseFailAlloc_1069_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1068_;
            }
            3 => {
                v_fst_1075_ = lean_ctor_get(v_a_1071_, 0);
                lean_inc(v_fst_1075_);
                lean_dec(v_a_1071_);
                if v_isShared_1074_ == 0 {
                    lean_ctor_set(v___x_1073_, 0, v_fst_1075_);
                    v___x_1077_ = v___x_1073_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1078_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1078_, 0, v_fst_1075_);
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
    mut v_mutex_1081_: *mut LeanObject,
    mut v_k_1082_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_ref_1084_: *mut LeanObject = core::ptr::null_mut();
    let mut v_mutex_1085_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_1086_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_1087_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_1088_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1089_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1090_: u8 = 0;
    let mut v___x_1091_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1093_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1094_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1095_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1096_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1098_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1099_: u8 = 0;
    let mut v___x_1101_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1102_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1103_: u8 = 0;
    let mut v_a_1104_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1106_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1107_: u8 = 0;
    let mut v_fst_1108_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1110_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1111_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1112_: u8 = 0;
    let mut v_a_1113_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1115_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1116_: u8 = 0;
    let mut v___f_1117_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1118_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1120_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1121_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1122_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ref_1084_ = lean_ctor_get(v_mutex_1081_, 0);
                lean_inc(v_ref_1084_);
                v_mutex_1085_ = lean_ctor_get(v_mutex_1081_, 1);
                lean_inc_n(v_mutex_1085_, 2);
                lean_dec_ref(v_mutex_1081_);
                v___f_1086_ = lean_alloc_closure(l_Std_Mutex_atomically___at___00Std_Notify_selector_spec__0___redArg___lam__0___boxed as *mut core::ffi::c_void, 3, 1);
                lean_closure_set(v___f_1086_, 0, v_mutex_1085_);
                v___f_1087_ = lean_alloc_closure(l_Std_Mutex_atomically___at___00Std_Notify_selector_spec__0___redArg___lam__1___boxed as *mut core::ffi::c_void, 4, 2);
                lean_closure_set(v___f_1087_, 0, v_k_1082_);
                lean_closure_set(v___f_1087_, 1, v_ref_1084_);
                v___f_1088_ = lean_alloc_closure(l_Std_Mutex_atomically___at___00Std_Notify_selector_spec__0___redArg___lam__2___boxed as *mut core::ffi::c_void, 3, 2);
                lean_closure_set(v___f_1088_, 0, v_mutex_1085_);
                lean_closure_set(v___f_1088_, 1, v___f_1087_);
                v___x_1089_ = lean_unsigned_to_nat(0);
                v___x_1090_ = 0;
                v___x_1091_ = l_Std_Async_EAsync_tryFinally_x27___redArg(
                    v___f_1088_,
                    v___f_1086_,
                    v___x_1089_,
                    v___x_1090_,
                );
                if lean_obj_tag(v___x_1091_) == 0 {
                    v_a_1095_ = lean_ctor_get(v___x_1091_, 0);
                    lean_inc(v_a_1095_);
                    lean_dec_ref_known(v___x_1091_, 1);
                    if lean_obj_tag(v_a_1095_) == 0 {
                        v_a_1096_ = lean_ctor_get(v_a_1095_, 0);
                        v_isSharedCheck_1103_ = (!lean_is_exclusive(v_a_1095_)) as u8;
                        if v_isSharedCheck_1103_ == 0 {
                            v___x_1098_ = v_a_1095_;
                            v_isShared_1099_ = v_isSharedCheck_1103_;
                            state = 2;
                            continue;
                        } else {
                            lean_inc(v_a_1096_);
                            lean_dec(v_a_1095_);
                            v___x_1098_ = lean_box(0);
                            v_isShared_1099_ = v_isSharedCheck_1103_;
                            state = 2;
                            continue;
                        }
                    } else {
                        v_a_1104_ = lean_ctor_get(v_a_1095_, 0);
                        v_isSharedCheck_1112_ = (!lean_is_exclusive(v_a_1095_)) as u8;
                        if v_isSharedCheck_1112_ == 0 {
                            v___x_1106_ = v_a_1095_;
                            v_isShared_1107_ = v_isSharedCheck_1112_;
                            state = 4;
                            continue;
                        } else {
                            lean_inc(v_a_1104_);
                            lean_dec(v_a_1095_);
                            v___x_1106_ = lean_box(0);
                            v_isShared_1107_ = v_isSharedCheck_1112_;
                            state = 4;
                            continue;
                        }
                    }
                } else {
                    v_a_1113_ = lean_ctor_get(v___x_1091_, 0);
                    v_isSharedCheck_1122_ = (!lean_is_exclusive(v___x_1091_)) as u8;
                    if v_isSharedCheck_1122_ == 0 {
                        v___x_1115_ = v___x_1091_;
                        v_isShared_1116_ = v_isSharedCheck_1122_;
                        state = 6;
                        continue;
                    } else {
                        lean_inc(v_a_1113_);
                        lean_dec(v___x_1091_);
                        v___x_1115_ = lean_box(0);
                        v_isShared_1116_ = v_isSharedCheck_1122_;
                        state = 6;
                        continue;
                    }
                }
            }
            1 => {
                v___x_1094_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_1094_, 0, v___y_1093_);
                return v___x_1094_;
            }
            2 => {
                if v_isShared_1099_ == 0 {
                    v___x_1101_ = v___x_1098_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_1102_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1102_, 0, v_a_1096_);
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
                v_fst_1108_ = lean_ctor_get(v_a_1104_, 0);
                lean_inc(v_fst_1108_);
                lean_dec(v_a_1104_);
                if v_isShared_1107_ == 0 {
                    lean_ctor_set(v___x_1106_, 0, v_fst_1108_);
                    v___x_1110_ = v___x_1106_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_1111_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1111_, 0, v_fst_1108_);
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
                    lean_ctor_set(v___x_1115_, 0, v___x_1118_);
                    v___x_1120_ = v___x_1115_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_1121_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1121_, 0, v___x_1118_);
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
    mut v_mutex_1123_: *mut LeanObject,
    mut v_k_1124_: *mut LeanObject,
    mut v___y_1125_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1126_: *mut LeanObject = core::ptr::null_mut();
    v_res_1126_ = l_Std_Mutex_atomically___at___00Std_Notify_selector_spec__0___redArg(
        v_mutex_1123_,
        v_k_1124_,
    );
    return v_res_1126_;
}
pub unsafe fn l_Std_Mutex_atomically___at___00Std_Notify_selector_spec__0(
    mut v_00_u03b1_1127_: *mut LeanObject,
    mut v_00_u03b2_1128_: *mut LeanObject,
    mut v_mutex_1129_: *mut LeanObject,
    mut v_k_1130_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1132_: *mut LeanObject = core::ptr::null_mut();
    v___x_1132_ = l_Std_Mutex_atomically___at___00Std_Notify_selector_spec__0___redArg(
        v_mutex_1129_,
        v_k_1130_,
    );
    return v___x_1132_;
}
pub unsafe fn l_Std_Mutex_atomically___at___00Std_Notify_selector_spec__0___boxed(
    mut v_00_u03b1_1133_: *mut LeanObject,
    mut v_00_u03b2_1134_: *mut LeanObject,
    mut v_mutex_1135_: *mut LeanObject,
    mut v_k_1136_: *mut LeanObject,
    mut v___y_1137_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1138_: *mut LeanObject = core::ptr::null_mut();
    v_res_1138_ = l_Std_Mutex_atomically___at___00Std_Notify_selector_spec__0(
        v_00_u03b1_1133_,
        v_00_u03b2_1134_,
        v_mutex_1135_,
        v_k_1136_,
    );
    return v_res_1138_;
}
pub unsafe fn l_Std_Notify_selector___lam__0(
    mut v___y_1139_: *mut LeanObject,
    mut v_x_1140_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_1142_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1144_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1145_: u8 = 0;
    let mut v___x_1147_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1148_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1149_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1150_: u8 = 0;
    let mut v_a_1151_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1153_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1154_: u8 = 0;
    let mut v___x_1155_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1157_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1158_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1159_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1160_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_1140_) == 0 {
                    v_a_1142_ = lean_ctor_get(v_x_1140_, 0);
                    v_isSharedCheck_1150_ = (!lean_is_exclusive(v_x_1140_)) as u8;
                    if v_isSharedCheck_1150_ == 0 {
                        v___x_1144_ = v_x_1140_;
                        v_isShared_1145_ = v_isSharedCheck_1150_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_1142_);
                        lean_dec(v_x_1140_);
                        v___x_1144_ = lean_box(0);
                        v_isShared_1145_ = v_isSharedCheck_1150_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_1151_ = lean_ctor_get(v_x_1140_, 0);
                    v_isSharedCheck_1160_ = (!lean_is_exclusive(v_x_1140_)) as u8;
                    if v_isSharedCheck_1160_ == 0 {
                        v___x_1153_ = v_x_1140_;
                        v_isShared_1154_ = v_isSharedCheck_1160_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_1151_);
                        lean_dec(v_x_1140_);
                        v___x_1153_ = lean_box(0);
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
                    v_reuseFailAlloc_1149_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1149_, 0, v_a_1142_);
                    v___x_1147_ = v_reuseFailAlloc_1149_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_1148_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_1148_, 0, v___x_1147_);
                return v___x_1148_;
            }
            3 => {
                v___x_1155_ = lean_st_ref_set(v___y_1139_, v_a_1151_);
                if v_isShared_1154_ == 0 {
                    lean_ctor_set(v___x_1153_, 0, v___x_1155_);
                    v___x_1157_ = v___x_1153_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1159_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1159_, 0, v___x_1155_);
                    v___x_1157_ = v_reuseFailAlloc_1159_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_1158_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_1158_, 0, v___x_1157_);
                return v___x_1158_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Notify_selector___lam__0___boxed(
    mut v___y_1161_: *mut LeanObject,
    mut v_x_1162_: *mut LeanObject,
    mut v___y_1163_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1164_: *mut LeanObject = core::ptr::null_mut();
    v_res_1164_ = l_Std_Notify_selector___lam__0(v___y_1161_, v_x_1162_);
    lean_dec(v___y_1161_);
    return v_res_1164_;
}
pub unsafe fn l_List_filterAuxM___at___00Std_Queue_filterM___at___00Std_Notify_selector_spec__1_spec__1___redArg___lam__1(
    mut v_x_1165_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___y_1168_: u8 = 0;
    let mut v___x_1169_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1170_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1171_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1172_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1173_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1174_: u8 = 0;
    let mut v___x_1175_: u8 = 0;
    let mut v___x_1176_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_1165_) == 0 {
                    v___x_1172_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_1172_, 0, v_x_1165_);
                    return v___x_1172_;
                } else {
                    v_a_1173_ = lean_ctor_get(v_x_1165_, 0);
                    lean_inc(v_a_1173_);
                    lean_dec_ref_known(v_x_1165_, 1);
                    v___x_1174_ = (lean_unbox(v_a_1173_) as u8);
                    lean_dec(v_a_1173_);
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
                v___x_1169_ = lean_box((v___y_1168_) as usize);
                v___x_1170_ = lean_alloc_ctor(1, 1, (0) as u32);
                lean_ctor_set(v___x_1170_, 0, v___x_1169_);
                v___x_1171_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_1171_, 0, v___x_1170_);
                return v___x_1171_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_filterAuxM___at___00Std_Queue_filterM___at___00Std_Notify_selector_spec__1_spec__1___redArg___lam__1___boxed(
    mut v_x_1177_: *mut LeanObject,
    mut v___y_1178_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1179_: *mut LeanObject = core::ptr::null_mut();
    v_res_1179_ = l_List_filterAuxM___at___00Std_Queue_filterM___at___00Std_Notify_selector_spec__1_spec__1___redArg___lam__1(v_x_1177_);
    return v_res_1179_;
}
pub unsafe fn l_List_filterAuxM___at___00Std_Queue_filterM___at___00Std_Notify_selector_spec__1_spec__1___redArg___lam__0___boxed(
    mut v_tail_1180_: *mut LeanObject,
    mut v_x_1181_: *mut LeanObject,
    mut v_head_1182_: *mut LeanObject,
    mut v_x_1183_: *mut LeanObject,
    mut v___y_1184_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1185_: *mut LeanObject = core::ptr::null_mut();
    v_res_1185_ = l_List_filterAuxM___at___00Std_Queue_filterM___at___00Std_Notify_selector_spec__1_spec__1___redArg___lam__0(v_tail_1180_, v_x_1181_, v_head_1182_, v_x_1183_);
    return v_res_1185_;
}
pub unsafe fn l_List_filterAuxM___at___00Std_Queue_filterM___at___00Std_Notify_selector_spec__1_spec__1___redArg(
    mut v_x_1192_: *mut LeanObject,
    mut v_x_1193_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1195_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1196_: *mut LeanObject = core::ptr::null_mut();
    let mut v_head_1197_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_1198_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_1199_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_1201_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1202_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1203_: u8 = 0;
    let mut v___x_1204_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1205_: *mut LeanObject = core::ptr::null_mut();
    let mut v_finished_1206_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1208_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1209_: u8 = 0;
    let mut v_finished_1210_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1211_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_1212_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1214_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1215_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1216_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1217_: u8 = 0;
    let mut v___x_1218_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1219_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1220_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_1192_) == 0 {
                    v___x_1195_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v___x_1195_, 0, v_x_1193_);
                    v___x_1196_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_1196_, 0, v___x_1195_);
                    return v___x_1196_;
                } else {
                    v_head_1197_ = lean_ctor_get(v_x_1192_, 0);
                    lean_inc_n(v_head_1197_, 2);
                    v_tail_1198_ = lean_ctor_get(v_x_1192_, 1);
                    lean_inc(v_tail_1198_);
                    lean_dec_ref_known(v_x_1192_, 2);
                    v___f_1199_ = lean_alloc_closure(l_List_filterAuxM___at___00Std_Queue_filterM___at___00Std_Notify_selector_spec__1_spec__1___redArg___lam__0___boxed as *mut core::ffi::c_void, 5, 3);
                    lean_closure_set(v___f_1199_, 0, v_tail_1198_);
                    lean_closure_set(v___f_1199_, 1, v_x_1193_);
                    lean_closure_set(v___f_1199_, 2, v_head_1197_);
                    if lean_obj_tag(v_head_1197_) == 0 {
                        lean_dec_ref_known(v_head_1197_, 1);
                        v___x_1205_ = l_List_filterAuxM___at___00Std_Queue_filterM___at___00Std_Notify_selector_spec__1_spec__1___redArg___closed__1;
                        v_val_1201_ = v___x_1205_;
                        state = 1;
                        continue;
                    } else {
                        v_finished_1206_ = lean_ctor_get(v_head_1197_, 0);
                        v_isSharedCheck_1220_ = (!lean_is_exclusive(v_head_1197_)) as u8;
                        if v_isSharedCheck_1220_ == 0 {
                            v___x_1208_ = v_head_1197_;
                            v_isShared_1209_ = v_isSharedCheck_1220_;
                            state = 2;
                            continue;
                        } else {
                            lean_inc(v_finished_1206_);
                            lean_dec(v_head_1197_);
                            v___x_1208_ = lean_box(0);
                            v_isShared_1209_ = v_isSharedCheck_1220_;
                            state = 2;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v___x_1202_ = lean_unsigned_to_nat(0);
                v___x_1203_ = 0;
                v___x_1204_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(
                    lean_box(0),
                    lean_box(0),
                    v___x_1202_,
                    v___x_1203_,
                    v_val_1201_,
                    v___f_1199_,
                );
                return v___x_1204_;
            }
            2 => {
                v_finished_1210_ = lean_ctor_get(v_finished_1206_, 0);
                lean_inc(v_finished_1210_);
                lean_dec_ref(v_finished_1206_);
                v___x_1211_ = lean_st_ref_get(v_finished_1210_);
                lean_dec(v_finished_1210_);
                v___f_1212_ = l_List_filterAuxM___at___00Std_Queue_filterM___at___00Std_Notify_selector_spec__1_spec__1___redArg___closed__2;
                if v_isShared_1209_ == 0 {
                    lean_ctor_set(v___x_1208_, 0, v___x_1211_);
                    v___x_1214_ = v___x_1208_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_1219_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1219_, 0, v___x_1211_);
                    v___x_1214_ = v_reuseFailAlloc_1219_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_1215_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_1215_, 0, v___x_1214_);
                v___x_1216_ = lean_unsigned_to_nat(0);
                v___x_1217_ = 0;
                v___x_1218_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(
                    lean_box(0),
                    lean_box(0),
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
    mut v_tail_1221_: *mut LeanObject,
    mut v_x_1222_: *mut LeanObject,
    mut v_head_1223_: *mut LeanObject,
    mut v_x_1224_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_1226_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1228_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1229_: u8 = 0;
    let mut v___x_1231_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1232_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1233_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1234_: u8 = 0;
    let mut v_a_1235_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1236_: u8 = 0;
    let mut v___x_1237_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1238_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1239_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_1224_) == 0 {
                    lean_dec_ref(v_head_1223_);
                    lean_dec(v_x_1222_);
                    lean_dec(v_tail_1221_);
                    v_a_1226_ = lean_ctor_get(v_x_1224_, 0);
                    v_isSharedCheck_1234_ = (!lean_is_exclusive(v_x_1224_)) as u8;
                    if v_isSharedCheck_1234_ == 0 {
                        v___x_1228_ = v_x_1224_;
                        v_isShared_1229_ = v_isSharedCheck_1234_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_1226_);
                        lean_dec(v_x_1224_);
                        v___x_1228_ = lean_box(0);
                        v_isShared_1229_ = v_isSharedCheck_1234_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_1235_ = lean_ctor_get(v_x_1224_, 0);
                    lean_inc(v_a_1235_);
                    lean_dec_ref_known(v_x_1224_, 1);
                    v___x_1236_ = (lean_unbox(v_a_1235_) as u8);
                    lean_dec(v_a_1235_);
                    if v___x_1236_ == 0 {
                        lean_dec_ref(v_head_1223_);
                        v___x_1237_ = l_List_filterAuxM___at___00Std_Queue_filterM___at___00Std_Notify_selector_spec__1_spec__1___redArg(v_tail_1221_, v_x_1222_);
                        return v___x_1237_;
                    } else {
                        v___x_1238_ = lean_alloc_ctor(1, 2, (0) as u32);
                        lean_ctor_set(v___x_1238_, 0, v_head_1223_);
                        lean_ctor_set(v___x_1238_, 1, v_x_1222_);
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
                    v_reuseFailAlloc_1233_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1233_, 0, v_a_1226_);
                    v___x_1231_ = v_reuseFailAlloc_1233_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_1232_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_1232_, 0, v___x_1231_);
                return v___x_1232_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_filterAuxM___at___00Std_Queue_filterM___at___00Std_Notify_selector_spec__1_spec__1___redArg___boxed(
    mut v_x_1240_: *mut LeanObject,
    mut v_x_1241_: *mut LeanObject,
    mut v___y_1242_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1243_: *mut LeanObject = core::ptr::null_mut();
    v_res_1243_ = l_List_filterAuxM___at___00Std_Queue_filterM___at___00Std_Notify_selector_spec__1_spec__1___redArg(v_x_1240_, v_x_1241_);
    return v_res_1243_;
}
pub unsafe fn l_Std_Queue_filterM___at___00Std_Notify_selector_spec__1___lam__0(
    mut v_x_1244_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1246_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1247_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1249_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1250_: u8 = 0;
    let mut v___x_1251_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1253_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1254_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1255_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1256_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_1244_) == 0 {
                    v___x_1246_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_1246_, 0, v_x_1244_);
                    return v___x_1246_;
                } else {
                    v_a_1247_ = lean_ctor_get(v_x_1244_, 0);
                    v_isSharedCheck_1256_ = (!lean_is_exclusive(v_x_1244_)) as u8;
                    if v_isSharedCheck_1256_ == 0 {
                        v___x_1249_ = v_x_1244_;
                        v_isShared_1250_ = v_isSharedCheck_1256_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_1247_);
                        lean_dec(v_x_1244_);
                        v___x_1249_ = lean_box(0);
                        v_isShared_1250_ = v_isSharedCheck_1256_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_1251_ = l_List_reverse___redArg(v_a_1247_);
                if v_isShared_1250_ == 0 {
                    lean_ctor_set(v___x_1249_, 0, v___x_1251_);
                    v___x_1253_ = v___x_1249_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1255_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1255_, 0, v___x_1251_);
                    v___x_1253_ = v_reuseFailAlloc_1255_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_1254_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_1254_, 0, v___x_1253_);
                return v___x_1254_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Queue_filterM___at___00Std_Notify_selector_spec__1___lam__0___boxed(
    mut v_x_1257_: *mut LeanObject,
    mut v___y_1258_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1259_: *mut LeanObject = core::ptr::null_mut();
    v_res_1259_ = l_Std_Queue_filterM___at___00Std_Notify_selector_spec__1___lam__0(v_x_1257_);
    return v_res_1259_;
}
pub unsafe fn l_Std_Queue_filterM___at___00Std_Notify_selector_spec__1___lam__2(
    mut v_a_1260_: *mut LeanObject,
    mut v___x_1261_: *mut LeanObject,
    mut v_x_1262_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_1264_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1266_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1267_: u8 = 0;
    let mut v___x_1269_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1270_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1271_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1272_: u8 = 0;
    let mut v_a_1273_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1275_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1276_: u8 = 0;
    let mut v___x_1277_: u8 = 0;
    let mut v___x_1278_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1280_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1281_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1282_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1283_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1284_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1286_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1287_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1288_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1289_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_1262_) == 0 {
                    lean_dec(v___x_1261_);
                    lean_dec(v_a_1260_);
                    v_a_1264_ = lean_ctor_get(v_x_1262_, 0);
                    v_isSharedCheck_1272_ = (!lean_is_exclusive(v_x_1262_)) as u8;
                    if v_isSharedCheck_1272_ == 0 {
                        v___x_1266_ = v_x_1262_;
                        v_isShared_1267_ = v_isSharedCheck_1272_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_1264_);
                        lean_dec(v_x_1262_);
                        v___x_1266_ = lean_box(0);
                        v_isShared_1267_ = v_isSharedCheck_1272_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_1273_ = lean_ctor_get(v_x_1262_, 0);
                    v_isSharedCheck_1289_ = (!lean_is_exclusive(v_x_1262_)) as u8;
                    if v_isSharedCheck_1289_ == 0 {
                        v___x_1275_ = v_x_1262_;
                        v_isShared_1276_ = v_isSharedCheck_1289_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_1273_);
                        lean_dec(v_x_1262_);
                        v___x_1275_ = lean_box(0);
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
                    v_reuseFailAlloc_1271_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1271_, 0, v_a_1264_);
                    v___x_1269_ = v_reuseFailAlloc_1271_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_1270_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_1270_, 0, v___x_1269_);
                return v___x_1270_;
            }
            3 => {
                v___x_1277_ = l_List_isEmpty___redArg(v_a_1260_);
                if v___x_1277_ == 0 {
                    lean_dec(v___x_1261_);
                    v___x_1278_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v___x_1278_, 0, v_a_1273_);
                    lean_ctor_set(v___x_1278_, 1, v_a_1260_);
                    if v_isShared_1276_ == 0 {
                        lean_ctor_set(v___x_1275_, 0, v___x_1278_);
                        v___x_1280_ = v___x_1275_;
                        state = 4;
                        continue;
                    } else {
                        v_reuseFailAlloc_1282_ = lean_alloc_ctor(1, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_1282_, 0, v___x_1278_);
                        v___x_1280_ = v_reuseFailAlloc_1282_;
                        state = 4;
                        continue;
                    }
                } else {
                    lean_dec(v_a_1260_);
                    v___x_1283_ = l_List_reverse___redArg(v_a_1273_);
                    v___x_1284_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v___x_1284_, 0, v___x_1261_);
                    lean_ctor_set(v___x_1284_, 1, v___x_1283_);
                    if v_isShared_1276_ == 0 {
                        lean_ctor_set(v___x_1275_, 0, v___x_1284_);
                        v___x_1286_ = v___x_1275_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_1288_ = lean_alloc_ctor(1, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_1288_, 0, v___x_1284_);
                        v___x_1286_ = v_reuseFailAlloc_1288_;
                        state = 5;
                        continue;
                    }
                }
            }
            4 => {
                v___x_1281_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_1281_, 0, v___x_1280_);
                return v___x_1281_;
            }
            5 => {
                v___x_1287_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_1287_, 0, v___x_1286_);
                return v___x_1287_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Queue_filterM___at___00Std_Notify_selector_spec__1___lam__2___boxed(
    mut v_a_1290_: *mut LeanObject,
    mut v___x_1291_: *mut LeanObject,
    mut v_x_1292_: *mut LeanObject,
    mut v___y_1293_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1294_: *mut LeanObject = core::ptr::null_mut();
    v_res_1294_ = l_Std_Queue_filterM___at___00Std_Notify_selector_spec__1___lam__2(
        v_a_1290_,
        v___x_1291_,
        v_x_1292_,
    );
    return v_res_1294_;
}
pub unsafe fn l_Std_Queue_filterM___at___00Std_Notify_selector_spec__1___lam__1(
    mut v_eList_1295_: *mut LeanObject,
    mut v___x_1296_: *mut LeanObject,
    mut v___f_1297_: *mut LeanObject,
    mut v_x_1298_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_1300_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1302_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1303_: u8 = 0;
    let mut v___x_1305_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1306_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1307_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1308_: u8 = 0;
    let mut v_a_1309_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1310_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1311_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1312_: u8 = 0;
    let mut v___x_1313_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_1314_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1315_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_1298_) == 0 {
                    lean_dec_ref(v___f_1297_);
                    lean_dec(v___x_1296_);
                    lean_dec(v_eList_1295_);
                    v_a_1300_ = lean_ctor_get(v_x_1298_, 0);
                    v_isSharedCheck_1308_ = (!lean_is_exclusive(v_x_1298_)) as u8;
                    if v_isSharedCheck_1308_ == 0 {
                        v___x_1302_ = v_x_1298_;
                        v_isShared_1303_ = v_isSharedCheck_1308_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_1300_);
                        lean_dec(v_x_1298_);
                        v___x_1302_ = lean_box(0);
                        v_isShared_1303_ = v_isSharedCheck_1308_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_1309_ = lean_ctor_get(v_x_1298_, 0);
                    lean_inc(v_a_1309_);
                    lean_dec_ref_known(v_x_1298_, 1);
                    lean_inc(v___x_1296_);
                    v___x_1310_ = l_List_filterAuxM___at___00Std_Queue_filterM___at___00Std_Notify_selector_spec__1_spec__1___redArg(v_eList_1295_, v___x_1296_);
                    v___x_1311_ = lean_unsigned_to_nat(0);
                    v___x_1312_ = 0;
                    v___x_1313_ =
                        l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(
                            lean_box(0),
                            lean_box(0),
                            v___x_1311_,
                            v___x_1312_,
                            v___x_1310_,
                            v___f_1297_,
                        );
                    v___f_1314_ = lean_alloc_closure(
                        l_Std_Queue_filterM___at___00Std_Notify_selector_spec__1___lam__2___boxed
                            as *mut core::ffi::c_void,
                        4,
                        2,
                    );
                    lean_closure_set(v___f_1314_, 0, v_a_1309_);
                    lean_closure_set(v___f_1314_, 1, v___x_1296_);
                    v___x_1315_ =
                        l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(
                            lean_box(0),
                            lean_box(0),
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
                    v_reuseFailAlloc_1307_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1307_, 0, v_a_1300_);
                    v___x_1305_ = v_reuseFailAlloc_1307_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_1306_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_1306_, 0, v___x_1305_);
                return v___x_1306_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Queue_filterM___at___00Std_Notify_selector_spec__1___lam__1___boxed(
    mut v_eList_1316_: *mut LeanObject,
    mut v___x_1317_: *mut LeanObject,
    mut v___f_1318_: *mut LeanObject,
    mut v_x_1319_: *mut LeanObject,
    mut v___y_1320_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1321_: *mut LeanObject = core::ptr::null_mut();
    v_res_1321_ = l_Std_Queue_filterM___at___00Std_Notify_selector_spec__1___lam__1(
        v_eList_1316_,
        v___x_1317_,
        v___f_1318_,
        v_x_1319_,
    );
    return v_res_1321_;
}
pub unsafe fn l_Std_Queue_filterM___at___00Std_Notify_selector_spec__1(
    mut v_q_1323_: *mut LeanObject,
    mut v___y_1324_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_eList_1326_: *mut LeanObject = core::ptr::null_mut();
    let mut v_dList_1327_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1328_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1329_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_1330_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1331_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1332_: u8 = 0;
    let mut v___x_1333_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_1334_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1335_: *mut LeanObject = core::ptr::null_mut();
    v_eList_1326_ = lean_ctor_get(v_q_1323_, 0);
    lean_inc(v_eList_1326_);
    v_dList_1327_ = lean_ctor_get(v_q_1323_, 1);
    lean_inc(v_dList_1327_);
    lean_dec_ref(v_q_1323_);
    v___x_1328_ = lean_box(0);
    v___x_1329_ = l_List_filterAuxM___at___00Std_Queue_filterM___at___00Std_Notify_selector_spec__1_spec__1___redArg(v_dList_1327_, v___x_1328_);
    v___f_1330_ = l_Std_Queue_filterM___at___00Std_Notify_selector_spec__1___closed__0;
    v___x_1331_ = lean_unsigned_to_nat(0);
    v___x_1332_ = 0;
    v___x_1333_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(
        lean_box(0),
        lean_box(0),
        v___x_1331_,
        v___x_1332_,
        v___x_1329_,
        v___f_1330_,
    );
    v___f_1334_ = lean_alloc_closure(
        l_Std_Queue_filterM___at___00Std_Notify_selector_spec__1___lam__1___boxed
            as *mut core::ffi::c_void,
        5,
        3,
    );
    lean_closure_set(v___f_1334_, 0, v_eList_1326_);
    lean_closure_set(v___f_1334_, 1, v___x_1328_);
    lean_closure_set(v___f_1334_, 2, v___f_1330_);
    v___x_1335_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(
        lean_box(0),
        lean_box(0),
        v___x_1331_,
        v___x_1332_,
        v___x_1333_,
        v___f_1334_,
    );
    return v___x_1335_;
}
pub unsafe fn l_Std_Queue_filterM___at___00Std_Notify_selector_spec__1___boxed(
    mut v_q_1336_: *mut LeanObject,
    mut v___y_1337_: *mut LeanObject,
    mut v___y_1338_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1339_: *mut LeanObject = core::ptr::null_mut();
    v_res_1339_ = l_Std_Queue_filterM___at___00Std_Notify_selector_spec__1(v_q_1336_, v___y_1337_);
    lean_dec(v___y_1337_);
    return v_res_1339_;
}
pub unsafe fn l_Std_Notify_selector___lam__1(
    mut v___y_1340_: *mut LeanObject,
    mut v___f_1341_: *mut LeanObject,
    mut v_x_1342_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_1344_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1346_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1347_: u8 = 0;
    let mut v___x_1349_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1350_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1351_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1352_: u8 = 0;
    let mut v_a_1353_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1354_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1355_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1356_: u8 = 0;
    let mut v___x_1357_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_1342_) == 0 {
                    lean_dec_ref(v___f_1341_);
                    v_a_1344_ = lean_ctor_get(v_x_1342_, 0);
                    v_isSharedCheck_1352_ = (!lean_is_exclusive(v_x_1342_)) as u8;
                    if v_isSharedCheck_1352_ == 0 {
                        v___x_1346_ = v_x_1342_;
                        v_isShared_1347_ = v_isSharedCheck_1352_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_1344_);
                        lean_dec(v_x_1342_);
                        v___x_1346_ = lean_box(0);
                        v_isShared_1347_ = v_isSharedCheck_1352_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_1353_ = lean_ctor_get(v_x_1342_, 0);
                    lean_inc(v_a_1353_);
                    lean_dec_ref_known(v_x_1342_, 1);
                    v___x_1354_ = l_Std_Queue_filterM___at___00Std_Notify_selector_spec__1(
                        v_a_1353_,
                        v___y_1340_,
                    );
                    v___x_1355_ = lean_unsigned_to_nat(0);
                    v___x_1356_ = 0;
                    v___x_1357_ =
                        l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(
                            lean_box(0),
                            lean_box(0),
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
                    v_reuseFailAlloc_1351_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1351_, 0, v_a_1344_);
                    v___x_1349_ = v_reuseFailAlloc_1351_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_1350_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_1350_, 0, v___x_1349_);
                return v___x_1350_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Notify_selector___lam__1___boxed(
    mut v___y_1358_: *mut LeanObject,
    mut v___f_1359_: *mut LeanObject,
    mut v_x_1360_: *mut LeanObject,
    mut v___y_1361_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1362_: *mut LeanObject = core::ptr::null_mut();
    v_res_1362_ = l_Std_Notify_selector___lam__1(v___y_1358_, v___f_1359_, v_x_1360_);
    lean_dec(v___y_1358_);
    return v_res_1362_;
}
pub unsafe fn l_Std_Notify_selector___lam__2(mut v___y_1363_: *mut LeanObject) -> *mut LeanObject {
    let mut v___x_1365_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_1366_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_1367_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1368_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1369_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1370_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1371_: u8 = 0;
    let mut v___x_1372_: *mut LeanObject = core::ptr::null_mut();
    v___x_1365_ = lean_st_ref_get(v___y_1363_);
    lean_inc_n(v___y_1363_, 2);
    v___f_1366_ = lean_alloc_closure(
        l_Std_Notify_selector___lam__0___boxed as *mut core::ffi::c_void,
        3,
        1,
    );
    lean_closure_set(v___f_1366_, 0, v___y_1363_);
    v___f_1367_ = lean_alloc_closure(
        l_Std_Notify_selector___lam__1___boxed as *mut core::ffi::c_void,
        4,
        2,
    );
    lean_closure_set(v___f_1367_, 0, v___y_1363_);
    lean_closure_set(v___f_1367_, 1, v___f_1366_);
    v___x_1368_ = lean_alloc_ctor(1, 1, (0) as u32);
    lean_ctor_set(v___x_1368_, 0, v___x_1365_);
    v___x_1369_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_1369_, 0, v___x_1368_);
    v___x_1370_ = lean_unsigned_to_nat(0);
    v___x_1371_ = 0;
    v___x_1372_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(
        lean_box(0),
        lean_box(0),
        v___x_1370_,
        v___x_1371_,
        v___x_1369_,
        v___f_1367_,
    );
    return v___x_1372_;
}
pub unsafe fn l_Std_Notify_selector___lam__2___boxed(
    mut v___y_1373_: *mut LeanObject,
    mut v___y_1374_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1375_: *mut LeanObject = core::ptr::null_mut();
    v_res_1375_ = l_Std_Notify_selector___lam__2(v___y_1373_);
    lean_dec(v___y_1373_);
    return v_res_1375_;
}
pub unsafe fn l_Std_Notify_selector___lam__3(
    mut v_waiter_1380_: *mut LeanObject,
    mut v___y_1381_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1383_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1384_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1385_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1386_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1387_: *mut LeanObject = core::ptr::null_mut();
    v___x_1383_ = lean_st_ref_take(v___y_1381_);
    v___x_1384_ = lean_alloc_ctor(1, 1, (0) as u32);
    lean_ctor_set(v___x_1384_, 0, v_waiter_1380_);
    v___x_1385_ = l_Std_Queue_enqueue___redArg(v___x_1384_, v___x_1383_);
    v___x_1386_ = lean_st_ref_set(v___y_1381_, v___x_1385_);
    v___x_1387_ = l_Std_Notify_selector___lam__3___closed__1;
    return v___x_1387_;
}
pub unsafe fn l_Std_Notify_selector___lam__3___boxed(
    mut v_waiter_1388_: *mut LeanObject,
    mut v___y_1389_: *mut LeanObject,
    mut v___y_1390_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1391_: *mut LeanObject = core::ptr::null_mut();
    v_res_1391_ = l_Std_Notify_selector___lam__3(v_waiter_1388_, v___y_1389_);
    lean_dec(v___y_1389_);
    return v_res_1391_;
}
pub unsafe fn l_Std_Notify_selector___lam__4(
    mut v_notify_1392_: *mut LeanObject,
    mut v_waiter_1393_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_1395_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1396_: *mut LeanObject = core::ptr::null_mut();
    v___f_1395_ = lean_alloc_closure(
        l_Std_Notify_selector___lam__3___boxed as *mut core::ffi::c_void,
        3,
        1,
    );
    lean_closure_set(v___f_1395_, 0, v_waiter_1393_);
    v___x_1396_ = l_Std_Mutex_atomically___at___00Std_Notify_selector_spec__0___redArg(
        v_notify_1392_,
        v___f_1395_,
    );
    return v___x_1396_;
}
pub unsafe fn l_Std_Notify_selector___lam__4___boxed(
    mut v_notify_1397_: *mut LeanObject,
    mut v_waiter_1398_: *mut LeanObject,
    mut v___y_1399_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1400_: *mut LeanObject = core::ptr::null_mut();
    v_res_1400_ = l_Std_Notify_selector___lam__4(v_notify_1397_, v_waiter_1398_);
    return v_res_1400_;
}
pub unsafe fn l_Std_Notify_selector___lam__5(mut v___x_1401_: *mut LeanObject) -> *mut LeanObject {
    let mut v___x_1403_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1404_: *mut LeanObject = core::ptr::null_mut();
    v___x_1403_ = lean_alloc_ctor(1, 1, (0) as u32);
    lean_ctor_set(v___x_1403_, 0, v___x_1401_);
    v___x_1404_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_1404_, 0, v___x_1403_);
    return v___x_1404_;
}
pub unsafe fn l_Std_Notify_selector___lam__5___boxed(
    mut v___x_1405_: *mut LeanObject,
    mut v___y_1406_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1407_: *mut LeanObject = core::ptr::null_mut();
    v_res_1407_ = l_Std_Notify_selector___lam__5(v___x_1405_);
    return v_res_1407_;
}
pub unsafe fn l_Std_Notify_selector(mut v_notify_1411_: *mut LeanObject) -> *mut LeanObject {
    let mut v___f_1412_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_1413_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_1414_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1415_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1416_: *mut LeanObject = core::ptr::null_mut();
    v___f_1412_ = l_Std_Notify_selector___closed__0;
    lean_inc_ref(v_notify_1411_);
    v___f_1413_ = lean_alloc_closure(
        l_Std_Notify_selector___lam__4___boxed as *mut core::ffi::c_void,
        3,
        1,
    );
    lean_closure_set(v___f_1413_, 0, v_notify_1411_);
    v___f_1414_ = l_Std_Notify_selector___closed__1;
    v___x_1415_ = lean_alloc_closure(
        l_Std_Mutex_atomically___at___00Std_Notify_selector_spec__0___boxed
            as *mut core::ffi::c_void,
        5,
        4,
    );
    lean_closure_set(v___x_1415_, 0, lean_box(0));
    lean_closure_set(v___x_1415_, 1, lean_box(0));
    lean_closure_set(v___x_1415_, 2, v_notify_1411_);
    lean_closure_set(v___x_1415_, 3, v___f_1412_);
    v___x_1416_ = lean_alloc_ctor(0, 3, (0) as u32);
    lean_ctor_set(v___x_1416_, 0, v___f_1414_);
    lean_ctor_set(v___x_1416_, 1, v___f_1413_);
    lean_ctor_set(v___x_1416_, 2, v___x_1415_);
    return v___x_1416_;
}
pub unsafe fn l_List_filterAuxM___at___00Std_Queue_filterM___at___00Std_Notify_selector_spec__1_spec__1(
    mut v_x_1417_: *mut LeanObject,
    mut v_x_1418_: *mut LeanObject,
    mut v___y_1419_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1421_: *mut LeanObject = core::ptr::null_mut();
    v___x_1421_ = l_List_filterAuxM___at___00Std_Queue_filterM___at___00Std_Notify_selector_spec__1_spec__1___redArg(v_x_1417_, v_x_1418_);
    return v___x_1421_;
}
pub unsafe fn l_List_filterAuxM___at___00Std_Queue_filterM___at___00Std_Notify_selector_spec__1_spec__1___boxed(
    mut v_x_1422_: *mut LeanObject,
    mut v_x_1423_: *mut LeanObject,
    mut v___y_1424_: *mut LeanObject,
    mut v___y_1425_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1426_: *mut LeanObject = core::ptr::null_mut();
    v_res_1426_ =
        l_List_filterAuxM___at___00Std_Queue_filterM___at___00Std_Notify_selector_spec__1_spec__1(
            v_x_1422_,
            v_x_1423_,
            v___y_1424_,
        );
    lean_dec(v___y_1424_);
    return v_res_1426_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Std_Sync_Notify(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Init_Data_Queue(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Std_Sync_Mutex(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Std_Async_Select(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Std_Sync_Notify(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_meta_initialized = true;
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Std_Sync_Notify(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Init_Data_Queue(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Std_Sync_Mutex(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Std_Async_Select(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Std_Sync_Notify(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Std_Sync_Notify(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Std_Sync_Notify(builtin);
}
