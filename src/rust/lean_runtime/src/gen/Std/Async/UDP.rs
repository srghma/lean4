// Lean compiler output
// Module: Std.Async.UDP
// Imports: Std.Time Std.Internal.UV.UDP Std.Async.Select
use crate::r#gen::Init::System::IOError::{lean_io_error_to_string, lean_mk_io_user_error};
use crate::r#gen::Init::System::Promise::l_IO_Promise_isResolved___redArg;
use crate::r#gen::Std::Async::Basic::l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask;
use crate::r#gen::Std::Async::Select::{
    initialize_Std_Async_Select, runtime_initialize_Std_Async_Select,
};
use crate::r#gen::Std::Internal::UV::UDP::{
    initialize_Std_Internal_UV_UDP, runtime_initialize_Std_Internal_UV_UDP,
};
use crate::r#gen::Std::Time::{initialize_Std_Time, runtime_initialize_Std_Time};
use crate::lean_imports_rs::Init::Core::{
    lean_task_bind, lean_task_get_own, lean_task_map, lean_task_pure,
};
use crate::lean_imports_rs::Init::Prelude::{lean_array_push, lean_mk_empty_array_with_capacity};
use crate::lean_imports_rs::Init::System::IO::{lean_io_as_task, lean_io_map_task};
use crate::lean_imports_rs::Init::System::Promise::{
    lean_io_promise_resolve, lean_io_promise_result_opt,
};
use crate::lean_imports_rs::Init::System::ST::{lean_st_ref_set, lean_st_ref_take};
use crate::lean_imports_rs::Std::Internal::UV::UDP::{
    lean_uv_udp_bind, lean_uv_udp_cancel_recv, lean_uv_udp_connect, lean_uv_udp_getpeername,
    lean_uv_udp_getsockname, lean_uv_udp_new, lean_uv_udp_recv, lean_uv_udp_send,
    lean_uv_udp_set_broadcast, lean_uv_udp_set_membership, lean_uv_udp_set_multicast_interface,
    lean_uv_udp_set_multicast_loop, lean_uv_udp_set_multicast_ttl, lean_uv_udp_set_ttl,
    lean_uv_udp_wait_readable,
};
pub static l_Std_Async_UDP_Socket_sendAll___closed__0_value: crate::leanh::LeanStringObject<44> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 44,
        m_capacity: 44,
        m_length: 43,
        m_data: [
            116, 104, 101, 32, 112, 114, 111, 109, 105, 115, 101, 32, 108, 105, 110, 107, 101, 100,
            32, 116, 111, 32, 116, 104, 101, 32, 65, 115, 121, 110, 99, 32, 119, 97, 115, 32, 100,
            114, 111, 112, 112, 101, 100, 0,
        ],
    };
static mut l_Std_Async_UDP_Socket_sendAll___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Async_UDP_Socket_sendAll___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Async_UDP_Socket_sendAll___closed__1_value: crate::leanh::LeanClosureObject<1> =
    crate::leanh::LeanClosureObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1)
                as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Std_Async_UDP_Socket_sendAll___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 1,
        m_objs: [
            core::ptr::addr_of!(l_Std_Async_UDP_Socket_sendAll___closed__0_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Std_Async_UDP_Socket_sendAll___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Async_UDP_Socket_sendAll___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Async_UDP_Socket_sendAll___closed__2_value: crate::leanh::LeanClosureObject<1> =
    crate::leanh::LeanClosureObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1)
                as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Std_Async_UDP_Socket_sendAll___lam__1___boxed as *const core::ffi::c_void,
        m_arity: 3,
        m_num_fixed: 1,
        m_objs: [
            core::ptr::addr_of!(l_Std_Async_UDP_Socket_sendAll___closed__1_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Std_Async_UDP_Socket_sendAll___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Async_UDP_Socket_sendAll___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Async_UDP_Socket_recv___closed__0_value: crate::leanh::LeanClosureObject<1> =
    crate::leanh::LeanClosureObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1)
                as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Std_Async_UDP_Socket_recv___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 1,
        m_objs: [
            core::ptr::addr_of!(l_Std_Async_UDP_Socket_sendAll___closed__0_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Std_Async_UDP_Socket_recv___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Async_UDP_Socket_recv___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Async_UDP_Socket_recv___closed__1_value: crate::leanh::LeanClosureObject<1> =
    crate::leanh::LeanClosureObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1)
                as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Std_Async_UDP_Socket_recv___lam__1___boxed as *const core::ffi::c_void,
        m_arity: 3,
        m_num_fixed: 1,
        m_objs: [
            core::ptr::addr_of!(l_Std_Async_UDP_Socket_recv___closed__0_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Std_Async_UDP_Socket_recv___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Async_UDP_Socket_recv___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Async_Waiter_race___at___00Std_Async_UDP_Socket_recvSelector_spec__1___closed__0_value: crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Std_Async_Waiter_race___at___00Std_Async_UDP_Socket_recvSelector_spec__1___lam__0 as *const core::ffi::c_void, m_arity: 1, m_num_fixed: 0, m_objs: [] };
static mut l_Std_Async_Waiter_race___at___00Std_Async_UDP_Socket_recvSelector_spec__1___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Std_Async_Waiter_race___at___00Std_Async_UDP_Socket_recvSelector_spec__1___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_Std_Async_UDP_Socket_recvSelector___lam__0___closed__0_value:
    crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 1,
    },
    m_objs: [(((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject],
};
static mut l_Std_Async_UDP_Socket_recvSelector___lam__0___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Async_UDP_Socket_recvSelector___lam__0___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Async_UDP_Socket_recvSelector___lam__0___closed__1_value:
    crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 0,
    },
    m_objs: [
        core::ptr::addr_of!(l_Std_Async_UDP_Socket_recvSelector___lam__0___closed__0_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Std_Async_UDP_Socket_recvSelector___lam__0___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Async_UDP_Socket_recvSelector___lam__0___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Async_UDP_Socket_recvSelector___lam__4___closed__0_value:
    crate::leanh::LeanClosureObject<1> = crate::leanh::LeanClosureObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Std_Async_UDP_Socket_recvSelector___lam__3___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 1,
    m_objs: [(((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject],
};
static mut l_Std_Async_UDP_Socket_recvSelector___lam__4___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Async_UDP_Socket_recvSelector___lam__4___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Async_UDP_Socket_recvSelector___lam__5___closed__0_value:
    crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 1,
    },
    m_objs: [(((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject],
};
static mut l_Std_Async_UDP_Socket_recvSelector___lam__5___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Async_UDP_Socket_recvSelector___lam__5___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Async_UDP_Socket_recvSelector___lam__5___closed__1_value:
    crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 0,
    },
    m_objs: [
        core::ptr::addr_of!(l_Std_Async_UDP_Socket_recvSelector___lam__5___closed__0_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Std_Async_UDP_Socket_recvSelector___lam__5___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Async_UDP_Socket_recvSelector___lam__5___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Async_UDP_Socket_recvSelector___closed__0_value: crate::leanh::LeanClosureObject<
    0,
> = crate::leanh::LeanClosureObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Std_Async_UDP_Socket_recvSelector___lam__1___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_Async_UDP_Socket_recvSelector___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Async_UDP_Socket_recvSelector___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Async_UDP_Socket_recvSelector___closed__1_value: crate::leanh::LeanClosureObject<
    0,
> = crate::leanh::LeanClosureObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Std_Async_UDP_Socket_recvSelector___lam__0___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_Async_UDP_Socket_recvSelector___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Async_UDP_Socket_recvSelector___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub unsafe fn l_Std_Async_UDP_Membership_ctorIdx(
    mut v_x_804_: u8,
) -> *mut crate::leanh::LeanObject {
    if v_x_804_ == 0 {
        let mut v___x_805_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_805_ = crate::leanh::lean_unsigned_to_nat(0);
        return v___x_805_;
    } else {
        let mut v___x_806_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_806_ = crate::leanh::lean_unsigned_to_nat(1);
        return v___x_806_;
    }
}
pub unsafe fn l_Std_Async_UDP_Membership_ctorIdx___boxed(
    mut v_x_807_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x_boxed_808_: u8 = 0;
    let mut v_res_809_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_x_boxed_808_ = (crate::leanh::lean_unbox(v_x_807_) as u8);
    v_res_809_ = l_Std_Async_UDP_Membership_ctorIdx(v_x_boxed_808_);
    return v_res_809_;
}
pub unsafe fn l_Std_Async_UDP_Membership_toCtorIdx(
    mut v_x_810_: u8,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_811_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_811_ = l_Std_Async_UDP_Membership_ctorIdx(v_x_810_);
    return v___x_811_;
}
pub unsafe fn l_Std_Async_UDP_Membership_toCtorIdx___boxed(
    mut v_x_812_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x_4__boxed_813_: u8 = 0;
    let mut v_res_814_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_x_4__boxed_813_ = (crate::leanh::lean_unbox(v_x_812_) as u8);
    v_res_814_ = l_Std_Async_UDP_Membership_toCtorIdx(v_x_4__boxed_813_);
    return v_res_814_;
}
pub unsafe fn l_Std_Async_UDP_Membership_ctorElim___redArg(
    mut v_k_815_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_k_815_);
    return v_k_815_;
}
pub unsafe fn l_Std_Async_UDP_Membership_ctorElim___redArg___boxed(
    mut v_k_816_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_817_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_817_ = l_Std_Async_UDP_Membership_ctorElim___redArg(v_k_816_);
    crate::leanh::lean_dec(v_k_816_);
    return v_res_817_;
}
pub unsafe fn l_Std_Async_UDP_Membership_ctorElim(
    mut v_motive_818_: *mut crate::leanh::LeanObject,
    mut v_ctorIdx_819_: *mut crate::leanh::LeanObject,
    mut v_t_820_: u8,
    mut v_h_821_: *mut crate::leanh::LeanObject,
    mut v_k_822_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_k_822_);
    return v_k_822_;
}
pub unsafe fn l_Std_Async_UDP_Membership_ctorElim___boxed(
    mut v_motive_823_: *mut crate::leanh::LeanObject,
    mut v_ctorIdx_824_: *mut crate::leanh::LeanObject,
    mut v_t_825_: *mut crate::leanh::LeanObject,
    mut v_h_826_: *mut crate::leanh::LeanObject,
    mut v_k_827_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_t_boxed_828_: u8 = 0;
    let mut v_res_829_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_t_boxed_828_ = (crate::leanh::lean_unbox(v_t_825_) as u8);
    v_res_829_ = l_Std_Async_UDP_Membership_ctorElim(
        v_motive_823_,
        v_ctorIdx_824_,
        v_t_boxed_828_,
        v_h_826_,
        v_k_827_,
    );
    crate::leanh::lean_dec(v_k_827_);
    crate::leanh::lean_dec(v_ctorIdx_824_);
    return v_res_829_;
}
pub unsafe fn l_Std_Async_UDP_Membership_leaveGroup_elim___redArg(
    mut v_leaveGroup_830_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_leaveGroup_830_);
    return v_leaveGroup_830_;
}
pub unsafe fn l_Std_Async_UDP_Membership_leaveGroup_elim___redArg___boxed(
    mut v_leaveGroup_831_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_832_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_832_ = l_Std_Async_UDP_Membership_leaveGroup_elim___redArg(v_leaveGroup_831_);
    crate::leanh::lean_dec(v_leaveGroup_831_);
    return v_res_832_;
}
pub unsafe fn l_Std_Async_UDP_Membership_leaveGroup_elim(
    mut v_motive_833_: *mut crate::leanh::LeanObject,
    mut v_t_834_: u8,
    mut v_h_835_: *mut crate::leanh::LeanObject,
    mut v_leaveGroup_836_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_leaveGroup_836_);
    return v_leaveGroup_836_;
}
pub unsafe fn l_Std_Async_UDP_Membership_leaveGroup_elim___boxed(
    mut v_motive_837_: *mut crate::leanh::LeanObject,
    mut v_t_838_: *mut crate::leanh::LeanObject,
    mut v_h_839_: *mut crate::leanh::LeanObject,
    mut v_leaveGroup_840_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_t_boxed_841_: u8 = 0;
    let mut v_res_842_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_t_boxed_841_ = (crate::leanh::lean_unbox(v_t_838_) as u8);
    v_res_842_ = l_Std_Async_UDP_Membership_leaveGroup_elim(
        v_motive_837_,
        v_t_boxed_841_,
        v_h_839_,
        v_leaveGroup_840_,
    );
    crate::leanh::lean_dec(v_leaveGroup_840_);
    return v_res_842_;
}
pub unsafe fn l_Std_Async_UDP_Membership_enterGroup_elim___redArg(
    mut v_enterGroup_843_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_enterGroup_843_);
    return v_enterGroup_843_;
}
pub unsafe fn l_Std_Async_UDP_Membership_enterGroup_elim___redArg___boxed(
    mut v_enterGroup_844_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_845_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_845_ = l_Std_Async_UDP_Membership_enterGroup_elim___redArg(v_enterGroup_844_);
    crate::leanh::lean_dec(v_enterGroup_844_);
    return v_res_845_;
}
pub unsafe fn l_Std_Async_UDP_Membership_enterGroup_elim(
    mut v_motive_846_: *mut crate::leanh::LeanObject,
    mut v_t_847_: u8,
    mut v_h_848_: *mut crate::leanh::LeanObject,
    mut v_enterGroup_849_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_enterGroup_849_);
    return v_enterGroup_849_;
}
pub unsafe fn l_Std_Async_UDP_Membership_enterGroup_elim___boxed(
    mut v_motive_850_: *mut crate::leanh::LeanObject,
    mut v_t_851_: *mut crate::leanh::LeanObject,
    mut v_h_852_: *mut crate::leanh::LeanObject,
    mut v_enterGroup_853_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_t_boxed_854_: u8 = 0;
    let mut v_res_855_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_t_boxed_854_ = (crate::leanh::lean_unbox(v_t_851_) as u8);
    v_res_855_ = l_Std_Async_UDP_Membership_enterGroup_elim(
        v_motive_850_,
        v_t_boxed_854_,
        v_h_852_,
        v_enterGroup_853_,
    );
    crate::leanh::lean_dec(v_enterGroup_853_);
    return v_res_855_;
}
pub unsafe fn l_Std_Async_UDP_Socket_mk() -> *mut crate::leanh::LeanObject {
    let mut v___x_857_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_858_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_860_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_861_: u8 = 0;
    let mut v___x_863_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_864_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_865_: u8 = 0;
    let mut v_a_866_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_868_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_869_: u8 = 0;
    let mut v___x_871_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_872_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_873_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_857_ = lean_uv_udp_new();
                if crate::leanh::lean_obj_tag(v___x_857_) == 0 {
                    v_a_858_ = crate::leanh::lean_ctor_get(v___x_857_, 0);
                    v_isSharedCheck_865_ = (!crate::leanh::lean_is_exclusive(v___x_857_)) as u8;
                    if v_isSharedCheck_865_ == 0 {
                        v___x_860_ = v___x_857_;
                        v_isShared_861_ = v_isSharedCheck_865_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_858_);
                        crate::leanh::lean_dec(v___x_857_);
                        v___x_860_ = crate::leanh::lean_box(0);
                        v_isShared_861_ = v_isSharedCheck_865_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_866_ = crate::leanh::lean_ctor_get(v___x_857_, 0);
                    v_isSharedCheck_873_ = (!crate::leanh::lean_is_exclusive(v___x_857_)) as u8;
                    if v_isSharedCheck_873_ == 0 {
                        v___x_868_ = v___x_857_;
                        v_isShared_869_ = v_isSharedCheck_873_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_866_);
                        crate::leanh::lean_dec(v___x_857_);
                        v___x_868_ = crate::leanh::lean_box(0);
                        v_isShared_869_ = v_isSharedCheck_873_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_861_ == 0 {
                    v___x_863_ = v___x_860_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_864_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_864_, 0, v_a_858_);
                    v___x_863_ = v_reuseFailAlloc_864_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_863_;
            }
            3 => {
                if v_isShared_869_ == 0 {
                    v___x_871_ = v___x_868_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_872_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_872_, 0, v_a_866_);
                    v___x_871_ = v_reuseFailAlloc_872_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_871_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Async_UDP_Socket_mk___boxed(
    mut v_a_874_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_875_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_875_ = l_Std_Async_UDP_Socket_mk();
    return v_res_875_;
}
pub unsafe fn l_Std_Async_UDP_Socket_bind(
    mut v_s_876_: *mut crate::leanh::LeanObject,
    mut v_addr_877_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_879_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_879_ = lean_uv_udp_bind(v_s_876_, v_addr_877_);
    return v___x_879_;
}
pub unsafe fn l_Std_Async_UDP_Socket_bind___boxed(
    mut v_s_880_: *mut crate::leanh::LeanObject,
    mut v_addr_881_: *mut crate::leanh::LeanObject,
    mut v_a_882_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_883_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_883_ = l_Std_Async_UDP_Socket_bind(v_s_880_, v_addr_881_);
    crate::leanh::lean_dec_ref(v_addr_881_);
    crate::leanh::lean_dec(v_s_880_);
    return v_res_883_;
}
pub unsafe fn l_Std_Async_UDP_Socket_connect(
    mut v_s_884_: *mut crate::leanh::LeanObject,
    mut v_addr_885_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_887_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_887_ = lean_uv_udp_connect(v_s_884_, v_addr_885_);
    return v___x_887_;
}
pub unsafe fn l_Std_Async_UDP_Socket_connect___boxed(
    mut v_s_888_: *mut crate::leanh::LeanObject,
    mut v_addr_889_: *mut crate::leanh::LeanObject,
    mut v_a_890_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_891_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_891_ = l_Std_Async_UDP_Socket_connect(v_s_888_, v_addr_889_);
    crate::leanh::lean_dec_ref(v_addr_889_);
    crate::leanh::lean_dec(v_s_888_);
    return v_res_891_;
}
pub unsafe fn l_Std_Async_UDP_Socket_sendAll___lam__0(
    mut v___x_892_: *mut crate::leanh::LeanObject,
    mut v_x_893_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_893_) == 0 {
        let mut v___x_894_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_895_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_894_ = lean_mk_io_user_error(v___x_892_);
        v___x_895_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_895_, 0, v___x_894_);
        return v___x_895_;
    } else {
        let mut v_val_896_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec_ref(v___x_892_);
        v_val_896_ = crate::leanh::lean_ctor_get(v_x_893_, 0);
        crate::leanh::lean_inc(v_val_896_);
        return v_val_896_;
    }
}
pub unsafe fn l_Std_Async_UDP_Socket_sendAll___lam__0___boxed(
    mut v___x_897_: *mut crate::leanh::LeanObject,
    mut v_x_898_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_899_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_899_ = l_Std_Async_UDP_Socket_sendAll___lam__0(v___x_897_, v_x_898_);
    crate::leanh::lean_dec(v_x_898_);
    return v_res_899_;
}
pub unsafe fn l_Std_Async_UDP_Socket_sendAll___lam__1(
    mut v___f_900_: *mut crate::leanh::LeanObject,
    mut v_x_901_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_a_903_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_905_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_906_: u8 = 0;
    let mut v___x_908_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_909_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_910_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_911_: u8 = 0;
    let mut v_a_912_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_913_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_915_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_916_: u8 = 0;
    let mut v___x_918_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_919_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_920_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_921_: u8 = 0;
    let mut v_a_922_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_923_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_924_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_925_: u8 = 0;
    let mut v___x_926_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_927_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_901_) == 0 {
                    crate::leanh::lean_dec_ref(v___f_900_);
                    v_a_903_ = crate::leanh::lean_ctor_get(v_x_901_, 0);
                    v_isSharedCheck_911_ = (!crate::leanh::lean_is_exclusive(v_x_901_)) as u8;
                    if v_isSharedCheck_911_ == 0 {
                        v___x_905_ = v_x_901_;
                        v_isShared_906_ = v_isSharedCheck_911_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_903_);
                        crate::leanh::lean_dec(v_x_901_);
                        v___x_905_ = crate::leanh::lean_box(0);
                        v_isShared_906_ = v_isSharedCheck_911_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_912_ = crate::leanh::lean_ctor_get(v_x_901_, 0);
                    crate::leanh::lean_inc(v_a_912_);
                    crate::leanh::lean_dec_ref_known(v_x_901_, 1);
                    if crate::leanh::lean_obj_tag(v_a_912_) == 0 {
                        crate::leanh::lean_dec_ref(v___f_900_);
                        v_a_913_ = crate::leanh::lean_ctor_get(v_a_912_, 0);
                        v_isSharedCheck_921_ = (!crate::leanh::lean_is_exclusive(v_a_912_)) as u8;
                        if v_isSharedCheck_921_ == 0 {
                            v___x_915_ = v_a_912_;
                            v_isShared_916_ = v_isSharedCheck_921_;
                            state = 3;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_913_);
                            crate::leanh::lean_dec(v_a_912_);
                            v___x_915_ = crate::leanh::lean_box(0);
                            v_isShared_916_ = v_isSharedCheck_921_;
                            state = 3;
                            continue;
                        }
                    } else {
                        v_a_922_ = crate::leanh::lean_ctor_get(v_a_912_, 0);
                        crate::leanh::lean_inc(v_a_922_);
                        crate::leanh::lean_dec_ref_known(v_a_912_, 1);
                        v___x_923_ = lean_io_promise_result_opt(v_a_922_);
                        crate::leanh::lean_dec(v_a_922_);
                        v___x_924_ = crate::leanh::lean_unsigned_to_nat(0);
                        v___x_925_ = 0;
                        v___x_926_ = lean_task_map(v___f_900_, v___x_923_, v___x_924_, v___x_925_);
                        v___x_927_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_927_, 0, v___x_926_);
                        return v___x_927_;
                    }
                }
            }
            1 => {
                if v_isShared_906_ == 0 {
                    v___x_908_ = v___x_905_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_910_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_910_, 0, v_a_903_);
                    v___x_908_ = v_reuseFailAlloc_910_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_909_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_909_, 0, v___x_908_);
                return v___x_909_;
            }
            3 => {
                if v_isShared_916_ == 0 {
                    v___x_918_ = v___x_915_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_920_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_920_, 0, v_a_913_);
                    v___x_918_ = v_reuseFailAlloc_920_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_919_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_919_, 0, v___x_918_);
                return v___x_919_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Async_UDP_Socket_sendAll___lam__1___boxed(
    mut v___f_928_: *mut crate::leanh::LeanObject,
    mut v_x_929_: *mut crate::leanh::LeanObject,
    mut v___y_930_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_931_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_931_ = l_Std_Async_UDP_Socket_sendAll___lam__1(v___f_928_, v_x_929_);
    return v_res_931_;
}
pub unsafe fn l_Std_Async_UDP_Socket_sendAll(
    mut v_s_937_: *mut crate::leanh::LeanObject,
    mut v_data_938_: *mut crate::leanh::LeanObject,
    mut v_addr_939_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_941_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_943_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_944_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_945_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_946_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_947_: u8 = 0;
    let mut v___x_948_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_949_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_950_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_952_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_953_: u8 = 0;
    let mut v___x_955_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_956_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_957_: u8 = 0;
    let mut v_a_958_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_960_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_961_: u8 = 0;
    let mut v___x_963_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_964_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_965_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___f_941_ = l_Std_Async_UDP_Socket_sendAll___closed__2;
                v___x_949_ = lean_uv_udp_send(v_s_937_, v_data_938_, v_addr_939_);
                if crate::leanh::lean_obj_tag(v___x_949_) == 0 {
                    v_a_950_ = crate::leanh::lean_ctor_get(v___x_949_, 0);
                    v_isSharedCheck_957_ = (!crate::leanh::lean_is_exclusive(v___x_949_)) as u8;
                    if v_isSharedCheck_957_ == 0 {
                        v___x_952_ = v___x_949_;
                        v_isShared_953_ = v_isSharedCheck_957_;
                        state = 2;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_950_);
                        crate::leanh::lean_dec(v___x_949_);
                        v___x_952_ = crate::leanh::lean_box(0);
                        v_isShared_953_ = v_isSharedCheck_957_;
                        state = 2;
                        continue;
                    }
                } else {
                    v_a_958_ = crate::leanh::lean_ctor_get(v___x_949_, 0);
                    v_isSharedCheck_965_ = (!crate::leanh::lean_is_exclusive(v___x_949_)) as u8;
                    if v_isSharedCheck_965_ == 0 {
                        v___x_960_ = v___x_949_;
                        v_isShared_961_ = v_isSharedCheck_965_;
                        state = 4;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_958_);
                        crate::leanh::lean_dec(v___x_949_);
                        v___x_960_ = crate::leanh::lean_box(0);
                        v_isShared_961_ = v_isSharedCheck_965_;
                        state = 4;
                        continue;
                    }
                }
            }
            1 => {
                v___x_944_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_944_, 0, v_val_943_);
                v___x_945_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_945_, 0, v___x_944_);
                v___x_946_ = crate::leanh::lean_unsigned_to_nat(0);
                v___x_947_ = 0;
                v___x_948_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(
                    crate::leanh::lean_box(0),
                    crate::leanh::lean_box(0),
                    v___x_946_,
                    v___x_947_,
                    v___x_945_,
                    v___f_941_,
                );
                return v___x_948_;
            }
            2 => {
                if v_isShared_953_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_952_, 1);
                    v___x_955_ = v___x_952_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_956_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_956_, 0, v_a_950_);
                    v___x_955_ = v_reuseFailAlloc_956_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v_val_943_ = v___x_955_;
                state = 1;
                continue;
            }
            4 => {
                if v_isShared_961_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_960_, 0);
                    v___x_963_ = v___x_960_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_964_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_964_, 0, v_a_958_);
                    v___x_963_ = v_reuseFailAlloc_964_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v_val_943_ = v___x_963_;
                state = 1;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Async_UDP_Socket_sendAll___boxed(
    mut v_s_966_: *mut crate::leanh::LeanObject,
    mut v_data_967_: *mut crate::leanh::LeanObject,
    mut v_addr_968_: *mut crate::leanh::LeanObject,
    mut v_a_969_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_970_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_970_ = l_Std_Async_UDP_Socket_sendAll(v_s_966_, v_data_967_, v_addr_968_);
    crate::leanh::lean_dec(v_addr_968_);
    crate::leanh::lean_dec(v_s_966_);
    return v_res_970_;
}
pub unsafe fn l_Std_Async_UDP_Socket_send(
    mut v_s_971_: *mut crate::leanh::LeanObject,
    mut v_data_972_: *mut crate::leanh::LeanObject,
    mut v_addr_973_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_975_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_976_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_977_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_978_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_980_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_981_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_982_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_983_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_984_: u8 = 0;
    let mut v___x_985_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_986_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_987_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_989_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_990_: u8 = 0;
    let mut v___x_992_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_993_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_994_: u8 = 0;
    let mut v_a_995_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_997_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_998_: u8 = 0;
    let mut v___x_1000_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1001_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1002_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_975_ = crate::leanh::lean_unsigned_to_nat(1);
                v___x_976_ = lean_mk_empty_array_with_capacity(v___x_975_);
                v___x_977_ = lean_array_push(v___x_976_, v_data_972_);
                v___f_978_ = l_Std_Async_UDP_Socket_sendAll___closed__2;
                v___x_986_ = lean_uv_udp_send(v_s_971_, v___x_977_, v_addr_973_);
                if crate::leanh::lean_obj_tag(v___x_986_) == 0 {
                    v_a_987_ = crate::leanh::lean_ctor_get(v___x_986_, 0);
                    v_isSharedCheck_994_ = (!crate::leanh::lean_is_exclusive(v___x_986_)) as u8;
                    if v_isSharedCheck_994_ == 0 {
                        v___x_989_ = v___x_986_;
                        v_isShared_990_ = v_isSharedCheck_994_;
                        state = 2;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_987_);
                        crate::leanh::lean_dec(v___x_986_);
                        v___x_989_ = crate::leanh::lean_box(0);
                        v_isShared_990_ = v_isSharedCheck_994_;
                        state = 2;
                        continue;
                    }
                } else {
                    v_a_995_ = crate::leanh::lean_ctor_get(v___x_986_, 0);
                    v_isSharedCheck_1002_ = (!crate::leanh::lean_is_exclusive(v___x_986_)) as u8;
                    if v_isSharedCheck_1002_ == 0 {
                        v___x_997_ = v___x_986_;
                        v_isShared_998_ = v_isSharedCheck_1002_;
                        state = 4;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_995_);
                        crate::leanh::lean_dec(v___x_986_);
                        v___x_997_ = crate::leanh::lean_box(0);
                        v_isShared_998_ = v_isSharedCheck_1002_;
                        state = 4;
                        continue;
                    }
                }
            }
            1 => {
                v___x_981_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_981_, 0, v_val_980_);
                v___x_982_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_982_, 0, v___x_981_);
                v___x_983_ = crate::leanh::lean_unsigned_to_nat(0);
                v___x_984_ = 0;
                v___x_985_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(
                    crate::leanh::lean_box(0),
                    crate::leanh::lean_box(0),
                    v___x_983_,
                    v___x_984_,
                    v___x_982_,
                    v___f_978_,
                );
                return v___x_985_;
            }
            2 => {
                if v_isShared_990_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_989_, 1);
                    v___x_992_ = v___x_989_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_993_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_993_, 0, v_a_987_);
                    v___x_992_ = v_reuseFailAlloc_993_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v_val_980_ = v___x_992_;
                state = 1;
                continue;
            }
            4 => {
                if v_isShared_998_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_997_, 0);
                    v___x_1000_ = v___x_997_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_1001_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1001_, 0, v_a_995_);
                    v___x_1000_ = v_reuseFailAlloc_1001_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v_val_980_ = v___x_1000_;
                state = 1;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Async_UDP_Socket_send___boxed(
    mut v_s_1003_: *mut crate::leanh::LeanObject,
    mut v_data_1004_: *mut crate::leanh::LeanObject,
    mut v_addr_1005_: *mut crate::leanh::LeanObject,
    mut v_a_1006_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1007_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1007_ = l_Std_Async_UDP_Socket_send(v_s_1003_, v_data_1004_, v_addr_1005_);
    crate::leanh::lean_dec(v_addr_1005_);
    crate::leanh::lean_dec(v_s_1003_);
    return v_res_1007_;
}
pub unsafe fn l_Std_Async_UDP_Socket_recv___lam__0(
    mut v___x_1008_: *mut crate::leanh::LeanObject,
    mut v_x_1009_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_1009_) == 0 {
        let mut v___x_1010_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1011_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_1010_ = lean_mk_io_user_error(v___x_1008_);
        v___x_1011_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_1011_, 0, v___x_1010_);
        return v___x_1011_;
    } else {
        let mut v_val_1012_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec_ref(v___x_1008_);
        v_val_1012_ = crate::leanh::lean_ctor_get(v_x_1009_, 0);
        crate::leanh::lean_inc(v_val_1012_);
        return v_val_1012_;
    }
}
pub unsafe fn l_Std_Async_UDP_Socket_recv___lam__0___boxed(
    mut v___x_1013_: *mut crate::leanh::LeanObject,
    mut v_x_1014_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1015_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1015_ = l_Std_Async_UDP_Socket_recv___lam__0(v___x_1013_, v_x_1014_);
    crate::leanh::lean_dec(v_x_1014_);
    return v_res_1015_;
}
pub unsafe fn l_Std_Async_UDP_Socket_recv___lam__1(
    mut v___f_1016_: *mut crate::leanh::LeanObject,
    mut v_x_1017_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_a_1019_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1021_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1022_: u8 = 0;
    let mut v___x_1024_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1025_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1026_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1027_: u8 = 0;
    let mut v_a_1028_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1029_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1031_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1032_: u8 = 0;
    let mut v___x_1034_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1035_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1036_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1037_: u8 = 0;
    let mut v_a_1038_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1039_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1040_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1041_: u8 = 0;
    let mut v___x_1042_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1043_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_1017_) == 0 {
                    crate::leanh::lean_dec_ref(v___f_1016_);
                    v_a_1019_ = crate::leanh::lean_ctor_get(v_x_1017_, 0);
                    v_isSharedCheck_1027_ = (!crate::leanh::lean_is_exclusive(v_x_1017_)) as u8;
                    if v_isSharedCheck_1027_ == 0 {
                        v___x_1021_ = v_x_1017_;
                        v_isShared_1022_ = v_isSharedCheck_1027_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1019_);
                        crate::leanh::lean_dec(v_x_1017_);
                        v___x_1021_ = crate::leanh::lean_box(0);
                        v_isShared_1022_ = v_isSharedCheck_1027_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_1028_ = crate::leanh::lean_ctor_get(v_x_1017_, 0);
                    crate::leanh::lean_inc(v_a_1028_);
                    crate::leanh::lean_dec_ref_known(v_x_1017_, 1);
                    if crate::leanh::lean_obj_tag(v_a_1028_) == 0 {
                        crate::leanh::lean_dec_ref(v___f_1016_);
                        v_a_1029_ = crate::leanh::lean_ctor_get(v_a_1028_, 0);
                        v_isSharedCheck_1037_ = (!crate::leanh::lean_is_exclusive(v_a_1028_)) as u8;
                        if v_isSharedCheck_1037_ == 0 {
                            v___x_1031_ = v_a_1028_;
                            v_isShared_1032_ = v_isSharedCheck_1037_;
                            state = 3;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_1029_);
                            crate::leanh::lean_dec(v_a_1028_);
                            v___x_1031_ = crate::leanh::lean_box(0);
                            v_isShared_1032_ = v_isSharedCheck_1037_;
                            state = 3;
                            continue;
                        }
                    } else {
                        v_a_1038_ = crate::leanh::lean_ctor_get(v_a_1028_, 0);
                        crate::leanh::lean_inc(v_a_1038_);
                        crate::leanh::lean_dec_ref_known(v_a_1028_, 1);
                        v___x_1039_ = lean_io_promise_result_opt(v_a_1038_);
                        crate::leanh::lean_dec(v_a_1038_);
                        v___x_1040_ = crate::leanh::lean_unsigned_to_nat(0);
                        v___x_1041_ = 0;
                        v___x_1042_ =
                            lean_task_map(v___f_1016_, v___x_1039_, v___x_1040_, v___x_1041_);
                        v___x_1043_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_1043_, 0, v___x_1042_);
                        return v___x_1043_;
                    }
                }
            }
            1 => {
                if v_isShared_1022_ == 0 {
                    v___x_1024_ = v___x_1021_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1026_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1026_, 0, v_a_1019_);
                    v___x_1024_ = v_reuseFailAlloc_1026_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_1025_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1025_, 0, v___x_1024_);
                return v___x_1025_;
            }
            3 => {
                if v_isShared_1032_ == 0 {
                    v___x_1034_ = v___x_1031_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1036_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1036_, 0, v_a_1029_);
                    v___x_1034_ = v_reuseFailAlloc_1036_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_1035_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1035_, 0, v___x_1034_);
                return v___x_1035_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Async_UDP_Socket_recv___lam__1___boxed(
    mut v___f_1044_: *mut crate::leanh::LeanObject,
    mut v_x_1045_: *mut crate::leanh::LeanObject,
    mut v___y_1046_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1047_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1047_ = l_Std_Async_UDP_Socket_recv___lam__1(v___f_1044_, v_x_1045_);
    return v_res_1047_;
}
pub unsafe fn l_Std_Async_UDP_Socket_recv(
    mut v_s_1052_: *mut crate::leanh::LeanObject,
    mut v_size_1053_: u64,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_1055_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1057_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1058_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1059_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1060_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1061_: u8 = 0;
    let mut v___x_1062_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1063_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1064_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1066_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1067_: u8 = 0;
    let mut v___x_1069_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1070_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1071_: u8 = 0;
    let mut v_a_1072_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1074_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1075_: u8 = 0;
    let mut v___x_1077_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1078_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1079_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___f_1055_ = l_Std_Async_UDP_Socket_recv___closed__1;
                v___x_1063_ = lean_uv_udp_recv(v_s_1052_, v_size_1053_);
                if crate::leanh::lean_obj_tag(v___x_1063_) == 0 {
                    v_a_1064_ = crate::leanh::lean_ctor_get(v___x_1063_, 0);
                    v_isSharedCheck_1071_ = (!crate::leanh::lean_is_exclusive(v___x_1063_)) as u8;
                    if v_isSharedCheck_1071_ == 0 {
                        v___x_1066_ = v___x_1063_;
                        v_isShared_1067_ = v_isSharedCheck_1071_;
                        state = 2;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1064_);
                        crate::leanh::lean_dec(v___x_1063_);
                        v___x_1066_ = crate::leanh::lean_box(0);
                        v_isShared_1067_ = v_isSharedCheck_1071_;
                        state = 2;
                        continue;
                    }
                } else {
                    v_a_1072_ = crate::leanh::lean_ctor_get(v___x_1063_, 0);
                    v_isSharedCheck_1079_ = (!crate::leanh::lean_is_exclusive(v___x_1063_)) as u8;
                    if v_isSharedCheck_1079_ == 0 {
                        v___x_1074_ = v___x_1063_;
                        v_isShared_1075_ = v_isSharedCheck_1079_;
                        state = 4;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1072_);
                        crate::leanh::lean_dec(v___x_1063_);
                        v___x_1074_ = crate::leanh::lean_box(0);
                        v_isShared_1075_ = v_isSharedCheck_1079_;
                        state = 4;
                        continue;
                    }
                }
            }
            1 => {
                v___x_1058_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1058_, 0, v_val_1057_);
                v___x_1059_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1059_, 0, v___x_1058_);
                v___x_1060_ = crate::leanh::lean_unsigned_to_nat(0);
                v___x_1061_ = 0;
                v___x_1062_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(
                    crate::leanh::lean_box(0),
                    crate::leanh::lean_box(0),
                    v___x_1060_,
                    v___x_1061_,
                    v___x_1059_,
                    v___f_1055_,
                );
                return v___x_1062_;
            }
            2 => {
                if v_isShared_1067_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_1066_, 1);
                    v___x_1069_ = v___x_1066_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_1070_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1070_, 0, v_a_1064_);
                    v___x_1069_ = v_reuseFailAlloc_1070_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v_val_1057_ = v___x_1069_;
                state = 1;
                continue;
            }
            4 => {
                if v_isShared_1075_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_1074_, 0);
                    v___x_1077_ = v___x_1074_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_1078_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1078_, 0, v_a_1072_);
                    v___x_1077_ = v_reuseFailAlloc_1078_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v_val_1057_ = v___x_1077_;
                state = 1;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Async_UDP_Socket_recv___boxed(
    mut v_s_1080_: *mut crate::leanh::LeanObject,
    mut v_size_1081_: *mut crate::leanh::LeanObject,
    mut v_a_1082_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_size_boxed_1083_: u64 = 0;
    let mut v_res_1084_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_size_boxed_1083_ = crate::leanh::lean_unbox_uint64(v_size_1081_);
    crate::leanh::lean_dec_ref(v_size_1081_);
    v_res_1084_ = l_Std_Async_UDP_Socket_recv(v_s_1080_, v_size_boxed_1083_);
    crate::leanh::lean_dec(v_s_1080_);
    return v_res_1084_;
}
pub unsafe fn l_IO_ofExcept___at___00Std_Async_UDP_Socket_recvSelector_spec__0___redArg(
    mut v_e_1085_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_a_1087_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1089_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1090_: u8 = 0;
    let mut v___x_1091_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1092_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1094_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1095_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1096_: u8 = 0;
    let mut v_a_1097_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1099_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1100_: u8 = 0;
    let mut v___x_1102_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1103_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1104_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_e_1085_) == 0 {
                    v_a_1087_ = crate::leanh::lean_ctor_get(v_e_1085_, 0);
                    v_isSharedCheck_1096_ = (!crate::leanh::lean_is_exclusive(v_e_1085_)) as u8;
                    if v_isSharedCheck_1096_ == 0 {
                        v___x_1089_ = v_e_1085_;
                        v_isShared_1090_ = v_isSharedCheck_1096_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1087_);
                        crate::leanh::lean_dec(v_e_1085_);
                        v___x_1089_ = crate::leanh::lean_box(0);
                        v_isShared_1090_ = v_isSharedCheck_1096_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_1097_ = crate::leanh::lean_ctor_get(v_e_1085_, 0);
                    v_isSharedCheck_1104_ = (!crate::leanh::lean_is_exclusive(v_e_1085_)) as u8;
                    if v_isSharedCheck_1104_ == 0 {
                        v___x_1099_ = v_e_1085_;
                        v_isShared_1100_ = v_isSharedCheck_1104_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1097_);
                        crate::leanh::lean_dec(v_e_1085_);
                        v___x_1099_ = crate::leanh::lean_box(0);
                        v_isShared_1100_ = v_isSharedCheck_1104_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v___x_1091_ = lean_io_error_to_string(v_a_1087_);
                v___x_1092_ = lean_mk_io_user_error(v___x_1091_);
                if v_isShared_1090_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_1089_, 1);
                    crate::leanh::lean_ctor_set(v___x_1089_, 0, v___x_1092_);
                    v___x_1094_ = v___x_1089_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1095_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1095_, 0, v___x_1092_);
                    v___x_1094_ = v_reuseFailAlloc_1095_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1094_;
            }
            3 => {
                if v_isShared_1100_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_1099_, 0);
                    v___x_1102_ = v___x_1099_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1103_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1103_, 0, v_a_1097_);
                    v___x_1102_ = v_reuseFailAlloc_1103_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_1102_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_IO_ofExcept___at___00Std_Async_UDP_Socket_recvSelector_spec__0___redArg___boxed(
    mut v_e_1105_: *mut crate::leanh::LeanObject,
    mut v_a_1106_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1107_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1107_ =
        l_IO_ofExcept___at___00Std_Async_UDP_Socket_recvSelector_spec__0___redArg(v_e_1105_);
    return v_res_1107_;
}
pub unsafe fn l_IO_ofExcept___at___00Std_Async_UDP_Socket_recvSelector_spec__0(
    mut v_00_u03b1_1108_: *mut crate::leanh::LeanObject,
    mut v_e_1109_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1111_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1111_ =
        l_IO_ofExcept___at___00Std_Async_UDP_Socket_recvSelector_spec__0___redArg(v_e_1109_);
    return v___x_1111_;
}
pub unsafe fn l_IO_ofExcept___at___00Std_Async_UDP_Socket_recvSelector_spec__0___boxed(
    mut v_00_u03b1_1112_: *mut crate::leanh::LeanObject,
    mut v_e_1113_: *mut crate::leanh::LeanObject,
    mut v_a_1114_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1115_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1115_ = l_IO_ofExcept___at___00Std_Async_UDP_Socket_recvSelector_spec__0(
        v_00_u03b1_1112_,
        v_e_1113_,
    );
    return v_res_1115_;
}
pub unsafe fn l_Std_Async_Waiter_race___at___00Std_Async_UDP_Socket_recvSelector_spec__1___lam__0(
    mut v_x_1116_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_1116_) == 0 {
        let mut v_a_1117_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1118_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_a_1117_ = crate::leanh::lean_ctor_get(v_x_1116_, 0);
        crate::leanh::lean_inc(v_a_1117_);
        crate::leanh::lean_dec_ref_known(v_x_1116_, 1);
        v___x_1118_ = lean_task_pure(v_a_1117_);
        return v___x_1118_;
    } else {
        let mut v_a_1119_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_a_1119_ = crate::leanh::lean_ctor_get(v_x_1116_, 0);
        crate::leanh::lean_inc_ref(v_a_1119_);
        crate::leanh::lean_dec_ref_known(v_x_1116_, 1);
        return v_a_1119_;
    }
}
pub unsafe fn l_Std_Async_Waiter_race___at___00Std_Async_UDP_Socket_recvSelector_spec__1___lam__2(
    mut v___f_1120_: *mut crate::leanh::LeanObject,
    mut v___x_1121_: *mut crate::leanh::LeanObject,
    mut v_x_1122_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_a_1124_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1126_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1127_: u8 = 0;
    let mut v___x_1129_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1130_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1131_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1132_: u8 = 0;
    let mut v_a_1133_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1134_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1136_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1137_: u8 = 0;
    let mut v___x_1139_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1140_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1141_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1142_: u8 = 0;
    let mut v_a_1143_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1144_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1145_: u8 = 0;
    let mut v___x_1146_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1147_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_1122_) == 0 {
                    crate::leanh::lean_dec(v___x_1121_);
                    crate::leanh::lean_dec_ref(v___f_1120_);
                    v_a_1124_ = crate::leanh::lean_ctor_get(v_x_1122_, 0);
                    v_isSharedCheck_1132_ = (!crate::leanh::lean_is_exclusive(v_x_1122_)) as u8;
                    if v_isSharedCheck_1132_ == 0 {
                        v___x_1126_ = v_x_1122_;
                        v_isShared_1127_ = v_isSharedCheck_1132_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1124_);
                        crate::leanh::lean_dec(v_x_1122_);
                        v___x_1126_ = crate::leanh::lean_box(0);
                        v_isShared_1127_ = v_isSharedCheck_1132_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_1133_ = crate::leanh::lean_ctor_get(v_x_1122_, 0);
                    crate::leanh::lean_inc(v_a_1133_);
                    crate::leanh::lean_dec_ref_known(v_x_1122_, 1);
                    if crate::leanh::lean_obj_tag(v_a_1133_) == 0 {
                        crate::leanh::lean_dec(v___x_1121_);
                        crate::leanh::lean_dec_ref(v___f_1120_);
                        v_a_1134_ = crate::leanh::lean_ctor_get(v_a_1133_, 0);
                        v_isSharedCheck_1142_ = (!crate::leanh::lean_is_exclusive(v_a_1133_)) as u8;
                        if v_isSharedCheck_1142_ == 0 {
                            v___x_1136_ = v_a_1133_;
                            v_isShared_1137_ = v_isSharedCheck_1142_;
                            state = 3;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_1134_);
                            crate::leanh::lean_dec(v_a_1133_);
                            v___x_1136_ = crate::leanh::lean_box(0);
                            v_isShared_1137_ = v_isSharedCheck_1142_;
                            state = 3;
                            continue;
                        }
                    } else {
                        v_a_1143_ = crate::leanh::lean_ctor_get(v_a_1133_, 0);
                        crate::leanh::lean_inc(v_a_1143_);
                        crate::leanh::lean_dec_ref_known(v_a_1133_, 1);
                        v___x_1144_ = lean_io_promise_result_opt(v_a_1143_);
                        crate::leanh::lean_dec(v_a_1143_);
                        v___x_1145_ = 0;
                        v___x_1146_ =
                            lean_task_map(v___f_1120_, v___x_1144_, v___x_1121_, v___x_1145_);
                        v___x_1147_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_1147_, 0, v___x_1146_);
                        return v___x_1147_;
                    }
                }
            }
            1 => {
                if v_isShared_1127_ == 0 {
                    v___x_1129_ = v___x_1126_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1131_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1131_, 0, v_a_1124_);
                    v___x_1129_ = v_reuseFailAlloc_1131_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_1130_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1130_, 0, v___x_1129_);
                return v___x_1130_;
            }
            3 => {
                if v_isShared_1137_ == 0 {
                    v___x_1139_ = v___x_1136_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1141_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1141_, 0, v_a_1134_);
                    v___x_1139_ = v_reuseFailAlloc_1141_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_1140_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1140_, 0, v___x_1139_);
                return v___x_1140_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Async_Waiter_race___at___00Std_Async_UDP_Socket_recvSelector_spec__1___lam__2___boxed(
    mut v___f_1148_: *mut crate::leanh::LeanObject,
    mut v___x_1149_: *mut crate::leanh::LeanObject,
    mut v_x_1150_: *mut crate::leanh::LeanObject,
    mut v___y_1151_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1152_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1152_ =
        l_Std_Async_Waiter_race___at___00Std_Async_UDP_Socket_recvSelector_spec__1___lam__2(
            v___f_1148_,
            v___x_1149_,
            v_x_1150_,
        );
    return v_res_1152_;
}
pub unsafe fn l_Std_Async_Waiter_race___at___00Std_Async_UDP_Socket_recvSelector_spec__1___lam__1(
    mut v___x_1153_: *mut crate::leanh::LeanObject,
    mut v_s_1154_: *mut crate::leanh::LeanObject,
    mut v_size_1155_: u64,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_1157_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1158_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1160_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1161_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1162_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1163_: u8 = 0;
    let mut v___x_1164_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1165_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1166_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1168_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1169_: u8 = 0;
    let mut v___x_1171_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1172_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1173_: u8 = 0;
    let mut v_a_1174_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1176_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1177_: u8 = 0;
    let mut v___x_1179_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1180_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1181_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___f_1157_ = l_Std_Async_UDP_Socket_recv___closed__0;
                crate::leanh::lean_inc(v___x_1153_);
                v___f_1158_ = crate::leanh::lean_alloc_closure(l_Std_Async_Waiter_race___at___00Std_Async_UDP_Socket_recvSelector_spec__1___lam__2___boxed as *mut core::ffi::c_void, 4, 2);
                crate::leanh::lean_closure_set(v___f_1158_, 0, v___f_1157_);
                crate::leanh::lean_closure_set(v___f_1158_, 1, v___x_1153_);
                v___x_1165_ = lean_uv_udp_recv(v_s_1154_, v_size_1155_);
                if crate::leanh::lean_obj_tag(v___x_1165_) == 0 {
                    v_a_1166_ = crate::leanh::lean_ctor_get(v___x_1165_, 0);
                    v_isSharedCheck_1173_ = (!crate::leanh::lean_is_exclusive(v___x_1165_)) as u8;
                    if v_isSharedCheck_1173_ == 0 {
                        v___x_1168_ = v___x_1165_;
                        v_isShared_1169_ = v_isSharedCheck_1173_;
                        state = 2;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1166_);
                        crate::leanh::lean_dec(v___x_1165_);
                        v___x_1168_ = crate::leanh::lean_box(0);
                        v_isShared_1169_ = v_isSharedCheck_1173_;
                        state = 2;
                        continue;
                    }
                } else {
                    v_a_1174_ = crate::leanh::lean_ctor_get(v___x_1165_, 0);
                    v_isSharedCheck_1181_ = (!crate::leanh::lean_is_exclusive(v___x_1165_)) as u8;
                    if v_isSharedCheck_1181_ == 0 {
                        v___x_1176_ = v___x_1165_;
                        v_isShared_1177_ = v_isSharedCheck_1181_;
                        state = 4;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1174_);
                        crate::leanh::lean_dec(v___x_1165_);
                        v___x_1176_ = crate::leanh::lean_box(0);
                        v_isShared_1177_ = v_isSharedCheck_1181_;
                        state = 4;
                        continue;
                    }
                }
            }
            1 => {
                v___x_1161_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1161_, 0, v_val_1160_);
                v___x_1162_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1162_, 0, v___x_1161_);
                v___x_1163_ = 0;
                v___x_1164_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(
                    crate::leanh::lean_box(0),
                    crate::leanh::lean_box(0),
                    v___x_1153_,
                    v___x_1163_,
                    v___x_1162_,
                    v___f_1158_,
                );
                return v___x_1164_;
            }
            2 => {
                if v_isShared_1169_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_1168_, 1);
                    v___x_1171_ = v___x_1168_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_1172_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1172_, 0, v_a_1166_);
                    v___x_1171_ = v_reuseFailAlloc_1172_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v_val_1160_ = v___x_1171_;
                state = 1;
                continue;
            }
            4 => {
                if v_isShared_1177_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_1176_, 0);
                    v___x_1179_ = v___x_1176_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_1180_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1180_, 0, v_a_1174_);
                    v___x_1179_ = v_reuseFailAlloc_1180_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v_val_1160_ = v___x_1179_;
                state = 1;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Async_Waiter_race___at___00Std_Async_UDP_Socket_recvSelector_spec__1___lam__1___boxed(
    mut v___x_1182_: *mut crate::leanh::LeanObject,
    mut v_s_1183_: *mut crate::leanh::LeanObject,
    mut v_size_1184_: *mut crate::leanh::LeanObject,
    mut v___y_1185_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_size_boxed_1186_: u64 = 0;
    let mut v_res_1187_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_size_boxed_1186_ = crate::leanh::lean_unbox_uint64(v_size_1184_);
    crate::leanh::lean_dec_ref(v_size_1184_);
    v_res_1187_ =
        l_Std_Async_Waiter_race___at___00Std_Async_UDP_Socket_recvSelector_spec__1___lam__1(
            v___x_1182_,
            v_s_1183_,
            v_size_boxed_1186_,
        );
    crate::leanh::lean_dec(v_s_1183_);
    return v_res_1187_;
}
pub unsafe fn l_Std_Async_Waiter_race___at___00Std_Async_UDP_Socket_recvSelector_spec__1(
    mut v_s_1189_: *mut crate::leanh::LeanObject,
    mut v_size_1190_: u64,
    mut v_val_1191_: *mut crate::leanh::LeanObject,
    mut v_w_1192_: *mut crate::leanh::LeanObject,
    mut v_lose_1193_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_finished_1195_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_promise_1196_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1198_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1199_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1200_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1201_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1202_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1203_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1205_: u8 = 0;
    let mut v___x_1206_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1207_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1208_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1209_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1210_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1211_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1212_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1213_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1214_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1216_: u8 = 0;
    let mut v___x_1217_: u8 = 0;
    let mut v___x_1218_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1219_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1220_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1221_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1222_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1223_: u8 = 0;
    let mut v___x_1224_: u8 = 0;
    let mut v___x_1225_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_finished_1195_ = crate::leanh::lean_ctor_get(v_w_1192_, 0);
                v_promise_1196_ = crate::leanh::lean_ctor_get(v_w_1192_, 1);
                v___x_1202_ = lean_st_ref_take(v_finished_1195_);
                v___f_1203_ = l_Std_Async_Waiter_race___at___00Std_Async_UDP_Socket_recvSelector_spec__1___closed__0;
                v___x_1223_ = (crate::leanh::lean_unbox(v___x_1202_) as u8);
                crate::leanh::lean_dec(v___x_1202_);
                if v___x_1223_ == 0 {
                    v___x_1224_ = 1;
                    v___y_1216_ = v___x_1224_;
                    state = 3;
                    continue;
                } else {
                    v___x_1225_ = 0;
                    v___y_1216_ = v___x_1225_;
                    state = 3;
                    continue;
                }
            }
            1 => {
                v___x_1199_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1199_, 0, v_a_1198_);
                v___x_1200_ = lean_io_promise_resolve(v___x_1199_, v_promise_1196_);
                v___x_1201_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1201_, 0, v___x_1200_);
                return v___x_1201_;
            }
            2 => {
                v___x_1206_ = crate::leanh::lean_unsigned_to_nat(0);
                v___x_1207_ = crate::leanh::lean_box_uint64(v_size_1190_);
                v___f_1208_ = crate::leanh::lean_alloc_closure(l_Std_Async_Waiter_race___at___00Std_Async_UDP_Socket_recvSelector_spec__1___lam__1___boxed as *mut core::ffi::c_void, 4, 3);
                crate::leanh::lean_closure_set(v___f_1208_, 0, v___x_1206_);
                crate::leanh::lean_closure_set(v___f_1208_, 1, v_s_1189_);
                crate::leanh::lean_closure_set(v___f_1208_, 2, v___x_1207_);
                v___x_1209_ = lean_io_as_task(v___f_1208_, v___x_1206_);
                v___x_1210_ = lean_task_bind(v___x_1209_, v___f_1203_, v___x_1206_, v___y_1205_);
                v___x_1211_ = lean_task_get_own(v___x_1210_);
                if crate::leanh::lean_obj_tag(v___x_1211_) == 0 {
                    v_a_1212_ = crate::leanh::lean_ctor_get(v___x_1211_, 0);
                    crate::leanh::lean_inc(v_a_1212_);
                    crate::leanh::lean_dec_ref_known(v___x_1211_, 1);
                    v_a_1198_ = v_a_1212_;
                    state = 1;
                    continue;
                } else {
                    v___x_1213_ = lean_io_promise_resolve(v___x_1211_, v_promise_1196_);
                    v___x_1214_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1214_, 0, v___x_1213_);
                    return v___x_1214_;
                }
            }
            3 => {
                v___x_1217_ = 1;
                v___x_1218_ = crate::leanh::lean_box((v___x_1217_) as usize);
                v___x_1219_ = lean_st_ref_set(v_finished_1195_, v___x_1218_);
                if v___y_1216_ == 0 {
                    crate::leanh::lean_dec_ref(v_val_1191_);
                    crate::leanh::lean_dec(v_s_1189_);
                    v___x_1220_ =
                        crate::leanh::lean_apply_1(v_lose_1193_, crate::leanh::lean_box(0));
                    return v___x_1220_;
                } else {
                    crate::leanh::lean_dec_ref(v_lose_1193_);
                    v___x_1221_ =
                        l_IO_ofExcept___at___00Std_Async_UDP_Socket_recvSelector_spec__0___redArg(
                            v_val_1191_,
                        );
                    if crate::leanh::lean_obj_tag(v___x_1221_) == 0 {
                        crate::leanh::lean_dec_ref_known(v___x_1221_, 1);
                        v___y_1205_ = v___y_1216_;
                        state = 2;
                        continue;
                    } else {
                        if crate::leanh::lean_obj_tag(v___x_1221_) == 0 {
                            crate::leanh::lean_dec_ref_known(v___x_1221_, 1);
                            v___y_1205_ = v___y_1216_;
                            state = 2;
                            continue;
                        } else {
                            crate::leanh::lean_dec(v_s_1189_);
                            v_a_1222_ = crate::leanh::lean_ctor_get(v___x_1221_, 0);
                            crate::leanh::lean_inc(v_a_1222_);
                            crate::leanh::lean_dec_ref_known(v___x_1221_, 1);
                            v_a_1198_ = v_a_1222_;
                            state = 1;
                            continue;
                        }
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Async_Waiter_race___at___00Std_Async_UDP_Socket_recvSelector_spec__1___boxed(
    mut v_s_1226_: *mut crate::leanh::LeanObject,
    mut v_size_1227_: *mut crate::leanh::LeanObject,
    mut v_val_1228_: *mut crate::leanh::LeanObject,
    mut v_w_1229_: *mut crate::leanh::LeanObject,
    mut v_lose_1230_: *mut crate::leanh::LeanObject,
    mut v___y_1231_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_size_boxed_1232_: u64 = 0;
    let mut v_res_1233_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_size_boxed_1232_ = crate::leanh::lean_unbox_uint64(v_size_1227_);
    crate::leanh::lean_dec_ref(v_size_1227_);
    v_res_1233_ = l_Std_Async_Waiter_race___at___00Std_Async_UDP_Socket_recvSelector_spec__1(
        v_s_1226_,
        v_size_boxed_1232_,
        v_val_1228_,
        v_w_1229_,
        v_lose_1230_,
    );
    crate::leanh::lean_dec_ref(v_w_1229_);
    return v_res_1233_;
}
pub unsafe fn l_Std_Async_UDP_Socket_recvSelector___lam__1(
    mut v_x_1234_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_a_1236_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1238_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1239_: u8 = 0;
    let mut v___x_1241_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1242_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1243_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1244_: u8 = 0;
    let mut v_a_1245_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1247_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1248_: u8 = 0;
    let mut v___x_1249_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1251_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1252_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1253_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1254_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_1234_) == 0 {
                    v_a_1236_ = crate::leanh::lean_ctor_get(v_x_1234_, 0);
                    v_isSharedCheck_1244_ = (!crate::leanh::lean_is_exclusive(v_x_1234_)) as u8;
                    if v_isSharedCheck_1244_ == 0 {
                        v___x_1238_ = v_x_1234_;
                        v_isShared_1239_ = v_isSharedCheck_1244_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1236_);
                        crate::leanh::lean_dec(v_x_1234_);
                        v___x_1238_ = crate::leanh::lean_box(0);
                        v_isShared_1239_ = v_isSharedCheck_1244_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_1245_ = crate::leanh::lean_ctor_get(v_x_1234_, 0);
                    v_isSharedCheck_1254_ = (!crate::leanh::lean_is_exclusive(v_x_1234_)) as u8;
                    if v_isSharedCheck_1254_ == 0 {
                        v___x_1247_ = v_x_1234_;
                        v_isShared_1248_ = v_isSharedCheck_1254_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1245_);
                        crate::leanh::lean_dec(v_x_1234_);
                        v___x_1247_ = crate::leanh::lean_box(0);
                        v_isShared_1248_ = v_isSharedCheck_1254_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_1239_ == 0 {
                    v___x_1241_ = v___x_1238_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1243_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1243_, 0, v_a_1236_);
                    v___x_1241_ = v_reuseFailAlloc_1243_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_1242_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1242_, 0, v___x_1241_);
                return v___x_1242_;
            }
            3 => {
                v___x_1249_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1249_, 0, v_a_1245_);
                if v_isShared_1248_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1247_, 0, v___x_1249_);
                    v___x_1251_ = v___x_1247_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1253_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1253_, 0, v___x_1249_);
                    v___x_1251_ = v_reuseFailAlloc_1253_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_1252_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1252_, 0, v___x_1251_);
                return v___x_1252_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Async_UDP_Socket_recvSelector___lam__1___boxed(
    mut v_x_1255_: *mut crate::leanh::LeanObject,
    mut v___y_1256_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1257_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1257_ = l_Std_Async_UDP_Socket_recvSelector___lam__1(v_x_1255_);
    return v_res_1257_;
}
pub unsafe fn l_Std_Async_UDP_Socket_recvSelector___lam__0(
    mut v_x_1262_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_a_1264_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1266_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1267_: u8 = 0;
    let mut v___x_1269_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1270_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1271_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1272_: u8 = 0;
    let mut v___x_1273_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_1262_) == 0 {
                    v_a_1264_ = crate::leanh::lean_ctor_get(v_x_1262_, 0);
                    v_isSharedCheck_1272_ = (!crate::leanh::lean_is_exclusive(v_x_1262_)) as u8;
                    if v_isSharedCheck_1272_ == 0 {
                        v___x_1266_ = v_x_1262_;
                        v_isShared_1267_ = v_isSharedCheck_1272_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1264_);
                        crate::leanh::lean_dec(v_x_1262_);
                        v___x_1266_ = crate::leanh::lean_box(0);
                        v_isShared_1267_ = v_isSharedCheck_1272_;
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec_ref_known(v_x_1262_, 1);
                    v___x_1273_ = l_Std_Async_UDP_Socket_recvSelector___lam__0___closed__1;
                    return v___x_1273_;
                }
            }
            1 => {
                if v_isShared_1267_ == 0 {
                    v___x_1269_ = v___x_1266_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1271_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1271_, 0, v_a_1264_);
                    v___x_1269_ = v_reuseFailAlloc_1271_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_1270_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1270_, 0, v___x_1269_);
                return v___x_1270_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Async_UDP_Socket_recvSelector___lam__0___boxed(
    mut v_x_1274_: *mut crate::leanh::LeanObject,
    mut v___y_1275_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1276_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1276_ = l_Std_Async_UDP_Socket_recvSelector___lam__0(v_x_1274_);
    return v_res_1276_;
}
pub unsafe fn l_Std_Async_UDP_Socket_recvSelector___lam__2(
    mut v_s_1277_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_val_1280_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1281_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1282_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1283_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1285_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1286_: u8 = 0;
    let mut v___x_1288_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1289_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1290_: u8 = 0;
    let mut v_a_1291_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1293_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1294_: u8 = 0;
    let mut v___x_1296_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1297_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1298_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1282_ = lean_uv_udp_cancel_recv(v_s_1277_);
                if crate::leanh::lean_obj_tag(v___x_1282_) == 0 {
                    v_a_1283_ = crate::leanh::lean_ctor_get(v___x_1282_, 0);
                    v_isSharedCheck_1290_ = (!crate::leanh::lean_is_exclusive(v___x_1282_)) as u8;
                    if v_isSharedCheck_1290_ == 0 {
                        v___x_1285_ = v___x_1282_;
                        v_isShared_1286_ = v_isSharedCheck_1290_;
                        state = 2;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1283_);
                        crate::leanh::lean_dec(v___x_1282_);
                        v___x_1285_ = crate::leanh::lean_box(0);
                        v_isShared_1286_ = v_isSharedCheck_1290_;
                        state = 2;
                        continue;
                    }
                } else {
                    v_a_1291_ = crate::leanh::lean_ctor_get(v___x_1282_, 0);
                    v_isSharedCheck_1298_ = (!crate::leanh::lean_is_exclusive(v___x_1282_)) as u8;
                    if v_isSharedCheck_1298_ == 0 {
                        v___x_1293_ = v___x_1282_;
                        v_isShared_1294_ = v_isSharedCheck_1298_;
                        state = 4;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1291_);
                        crate::leanh::lean_dec(v___x_1282_);
                        v___x_1293_ = crate::leanh::lean_box(0);
                        v_isShared_1294_ = v_isSharedCheck_1298_;
                        state = 4;
                        continue;
                    }
                }
            }
            1 => {
                v___x_1281_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1281_, 0, v_val_1280_);
                return v___x_1281_;
            }
            2 => {
                if v_isShared_1286_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_1285_, 1);
                    v___x_1288_ = v___x_1285_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_1289_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1289_, 0, v_a_1283_);
                    v___x_1288_ = v_reuseFailAlloc_1289_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v_val_1280_ = v___x_1288_;
                state = 1;
                continue;
            }
            4 => {
                if v_isShared_1294_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_1293_, 0);
                    v___x_1296_ = v___x_1293_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_1297_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1297_, 0, v_a_1291_);
                    v___x_1296_ = v_reuseFailAlloc_1297_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v_val_1280_ = v___x_1296_;
                state = 1;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Async_UDP_Socket_recvSelector___lam__2___boxed(
    mut v_s_1299_: *mut crate::leanh::LeanObject,
    mut v___y_1300_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1301_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1301_ = l_Std_Async_UDP_Socket_recvSelector___lam__2(v_s_1299_);
    crate::leanh::lean_dec(v_s_1299_);
    return v_res_1301_;
}
pub unsafe fn l_Std_Async_UDP_Socket_recvSelector___lam__3(
    mut v___x_1302_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1304_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1304_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1304_, 0, v___x_1302_);
    return v___x_1304_;
}
pub unsafe fn l_Std_Async_UDP_Socket_recvSelector___lam__3___boxed(
    mut v___x_1305_: *mut crate::leanh::LeanObject,
    mut v___y_1306_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1307_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1307_ = l_Std_Async_UDP_Socket_recvSelector___lam__3(v___x_1305_);
    return v_res_1307_;
}
pub unsafe fn l_Std_Async_UDP_Socket_recvSelector___lam__4(
    mut v_s_1310_: *mut crate::leanh::LeanObject,
    mut v_size_1311_: u64,
    mut v_waiter_1312_: *mut crate::leanh::LeanObject,
    mut v_a_1313_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_a_1316_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1317_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1318_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1319_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1320_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1321_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1322_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1323_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1325_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1326_: u8 = 0;
    let mut v___x_1328_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1329_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1330_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_a_1313_) == 0 {
                    crate::leanh::lean_dec(v_s_1310_);
                    v___x_1318_ = crate::leanh::lean_box(0);
                    v_a_1316_ = v___x_1318_;
                    state = 1;
                    continue;
                } else {
                    v_val_1319_ = crate::leanh::lean_ctor_get(v_a_1313_, 0);
                    crate::leanh::lean_inc(v_val_1319_);
                    crate::leanh::lean_dec_ref_known(v_a_1313_, 1);
                    v___f_1320_ = l_Std_Async_UDP_Socket_recvSelector___lam__4___closed__0;
                    v___x_1321_ =
                        l_Std_Async_Waiter_race___at___00Std_Async_UDP_Socket_recvSelector_spec__1(
                            v_s_1310_,
                            v_size_1311_,
                            v_val_1319_,
                            v_waiter_1312_,
                            v___f_1320_,
                        );
                    if crate::leanh::lean_obj_tag(v___x_1321_) == 0 {
                        v_a_1322_ = crate::leanh::lean_ctor_get(v___x_1321_, 0);
                        crate::leanh::lean_inc(v_a_1322_);
                        crate::leanh::lean_dec_ref_known(v___x_1321_, 1);
                        v_a_1316_ = v_a_1322_;
                        state = 1;
                        continue;
                    } else {
                        v_a_1323_ = crate::leanh::lean_ctor_get(v___x_1321_, 0);
                        v_isSharedCheck_1330_ =
                            (!crate::leanh::lean_is_exclusive(v___x_1321_)) as u8;
                        if v_isSharedCheck_1330_ == 0 {
                            v___x_1325_ = v___x_1321_;
                            v_isShared_1326_ = v_isSharedCheck_1330_;
                            state = 2;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_1323_);
                            crate::leanh::lean_dec(v___x_1321_);
                            v___x_1325_ = crate::leanh::lean_box(0);
                            v_isShared_1326_ = v_isSharedCheck_1330_;
                            state = 2;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v___x_1317_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1317_, 0, v_a_1316_);
                return v___x_1317_;
            }
            2 => {
                if v_isShared_1326_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_1325_, 0);
                    v___x_1328_ = v___x_1325_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_1329_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1329_, 0, v_a_1323_);
                    v___x_1328_ = v_reuseFailAlloc_1329_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_1328_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Async_UDP_Socket_recvSelector___lam__4___boxed(
    mut v_s_1331_: *mut crate::leanh::LeanObject,
    mut v_size_1332_: *mut crate::leanh::LeanObject,
    mut v_waiter_1333_: *mut crate::leanh::LeanObject,
    mut v_a_1334_: *mut crate::leanh::LeanObject,
    mut v___y_1335_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_size_boxed_1336_: u64 = 0;
    let mut v_res_1337_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_size_boxed_1336_ = crate::leanh::lean_unbox_uint64(v_size_1332_);
    crate::leanh::lean_dec_ref(v_size_1332_);
    v_res_1337_ = l_Std_Async_UDP_Socket_recvSelector___lam__4(
        v_s_1331_,
        v_size_boxed_1336_,
        v_waiter_1333_,
        v_a_1334_,
    );
    crate::leanh::lean_dec_ref(v_waiter_1333_);
    return v_res_1337_;
}
pub unsafe fn l_Std_Async_UDP_Socket_recvSelector___lam__5(
    mut v___f_1342_: *mut crate::leanh::LeanObject,
    mut v_x_1343_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_a_1345_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1347_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1348_: u8 = 0;
    let mut v___x_1350_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1351_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1352_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1353_: u8 = 0;
    let mut v_a_1354_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1355_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1356_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1357_: u8 = 0;
    let mut v___x_1358_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1359_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_1343_) == 0 {
                    crate::leanh::lean_dec_ref(v___f_1342_);
                    v_a_1345_ = crate::leanh::lean_ctor_get(v_x_1343_, 0);
                    v_isSharedCheck_1353_ = (!crate::leanh::lean_is_exclusive(v_x_1343_)) as u8;
                    if v_isSharedCheck_1353_ == 0 {
                        v___x_1347_ = v_x_1343_;
                        v_isShared_1348_ = v_isSharedCheck_1353_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1345_);
                        crate::leanh::lean_dec(v_x_1343_);
                        v___x_1347_ = crate::leanh::lean_box(0);
                        v_isShared_1348_ = v_isSharedCheck_1353_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_1354_ = crate::leanh::lean_ctor_get(v_x_1343_, 0);
                    crate::leanh::lean_inc(v_a_1354_);
                    crate::leanh::lean_dec_ref_known(v_x_1343_, 1);
                    v___x_1355_ = lean_io_promise_result_opt(v_a_1354_);
                    crate::leanh::lean_dec(v_a_1354_);
                    v___x_1356_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___x_1357_ = 0;
                    v___x_1358_ =
                        lean_io_map_task(v___f_1342_, v___x_1355_, v___x_1356_, v___x_1357_);
                    crate::leanh::lean_dec_ref(v___x_1358_);
                    v___x_1359_ = l_Std_Async_UDP_Socket_recvSelector___lam__5___closed__1;
                    return v___x_1359_;
                }
            }
            1 => {
                if v_isShared_1348_ == 0 {
                    v___x_1350_ = v___x_1347_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1352_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1352_, 0, v_a_1345_);
                    v___x_1350_ = v_reuseFailAlloc_1352_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_1351_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1351_, 0, v___x_1350_);
                return v___x_1351_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Async_UDP_Socket_recvSelector___lam__5___boxed(
    mut v___f_1360_: *mut crate::leanh::LeanObject,
    mut v_x_1361_: *mut crate::leanh::LeanObject,
    mut v___y_1362_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1363_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1363_ = l_Std_Async_UDP_Socket_recvSelector___lam__5(v___f_1360_, v_x_1361_);
    return v_res_1363_;
}
pub unsafe fn l_Std_Async_UDP_Socket_recvSelector___lam__6(
    mut v_s_1364_: *mut crate::leanh::LeanObject,
    mut v_size_1365_: u64,
    mut v_waiter_1366_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1368_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1369_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1370_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1372_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1373_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1374_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1375_: u8 = 0;
    let mut v___x_1376_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1377_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1378_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1380_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1381_: u8 = 0;
    let mut v___x_1383_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1384_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1385_: u8 = 0;
    let mut v_a_1386_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1388_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1389_: u8 = 0;
    let mut v___x_1391_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1392_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1393_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1368_ = crate::leanh::lean_box_uint64(v_size_1365_);
                crate::leanh::lean_inc(v_s_1364_);
                v___f_1369_ = crate::leanh::lean_alloc_closure(
                    l_Std_Async_UDP_Socket_recvSelector___lam__4___boxed as *mut core::ffi::c_void,
                    5,
                    3,
                );
                crate::leanh::lean_closure_set(v___f_1369_, 0, v_s_1364_);
                crate::leanh::lean_closure_set(v___f_1369_, 1, v___x_1368_);
                crate::leanh::lean_closure_set(v___f_1369_, 2, v_waiter_1366_);
                v___f_1370_ = crate::leanh::lean_alloc_closure(
                    l_Std_Async_UDP_Socket_recvSelector___lam__5___boxed as *mut core::ffi::c_void,
                    3,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_1370_, 0, v___f_1369_);
                v___x_1377_ = lean_uv_udp_wait_readable(v_s_1364_);
                crate::leanh::lean_dec(v_s_1364_);
                if crate::leanh::lean_obj_tag(v___x_1377_) == 0 {
                    v_a_1378_ = crate::leanh::lean_ctor_get(v___x_1377_, 0);
                    v_isSharedCheck_1385_ = (!crate::leanh::lean_is_exclusive(v___x_1377_)) as u8;
                    if v_isSharedCheck_1385_ == 0 {
                        v___x_1380_ = v___x_1377_;
                        v_isShared_1381_ = v_isSharedCheck_1385_;
                        state = 2;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1378_);
                        crate::leanh::lean_dec(v___x_1377_);
                        v___x_1380_ = crate::leanh::lean_box(0);
                        v_isShared_1381_ = v_isSharedCheck_1385_;
                        state = 2;
                        continue;
                    }
                } else {
                    v_a_1386_ = crate::leanh::lean_ctor_get(v___x_1377_, 0);
                    v_isSharedCheck_1393_ = (!crate::leanh::lean_is_exclusive(v___x_1377_)) as u8;
                    if v_isSharedCheck_1393_ == 0 {
                        v___x_1388_ = v___x_1377_;
                        v_isShared_1389_ = v_isSharedCheck_1393_;
                        state = 4;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1386_);
                        crate::leanh::lean_dec(v___x_1377_);
                        v___x_1388_ = crate::leanh::lean_box(0);
                        v_isShared_1389_ = v_isSharedCheck_1393_;
                        state = 4;
                        continue;
                    }
                }
            }
            1 => {
                v___x_1373_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1373_, 0, v_val_1372_);
                v___x_1374_ = crate::leanh::lean_unsigned_to_nat(0);
                v___x_1375_ = 0;
                v___x_1376_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(
                    crate::leanh::lean_box(0),
                    crate::leanh::lean_box(0),
                    v___x_1374_,
                    v___x_1375_,
                    v___x_1373_,
                    v___f_1370_,
                );
                return v___x_1376_;
            }
            2 => {
                if v_isShared_1381_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_1380_, 1);
                    v___x_1383_ = v___x_1380_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_1384_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1384_, 0, v_a_1378_);
                    v___x_1383_ = v_reuseFailAlloc_1384_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v_val_1372_ = v___x_1383_;
                state = 1;
                continue;
            }
            4 => {
                if v_isShared_1389_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_1388_, 0);
                    v___x_1391_ = v___x_1388_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_1392_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1392_, 0, v_a_1386_);
                    v___x_1391_ = v_reuseFailAlloc_1392_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v_val_1372_ = v___x_1391_;
                state = 1;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Async_UDP_Socket_recvSelector___lam__6___boxed(
    mut v_s_1394_: *mut crate::leanh::LeanObject,
    mut v_size_1395_: *mut crate::leanh::LeanObject,
    mut v_waiter_1396_: *mut crate::leanh::LeanObject,
    mut v___y_1397_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_size_boxed_1398_: u64 = 0;
    let mut v_res_1399_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_size_boxed_1398_ = crate::leanh::lean_unbox_uint64(v_size_1395_);
    crate::leanh::lean_dec_ref(v_size_1395_);
    v_res_1399_ =
        l_Std_Async_UDP_Socket_recvSelector___lam__6(v_s_1394_, v_size_boxed_1398_, v_waiter_1396_);
    return v_res_1399_;
}
pub unsafe fn l_Std_Async_UDP_Socket_recvSelector___lam__10(
    mut v___f_1400_: *mut crate::leanh::LeanObject,
    mut v_s_1401_: *mut crate::leanh::LeanObject,
    mut v_size_1402_: u64,
    mut v___f_1403_: *mut crate::leanh::LeanObject,
    mut v___f_1404_: *mut crate::leanh::LeanObject,
    mut v_x_1405_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_a_1407_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1409_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1410_: u8 = 0;
    let mut v___x_1412_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1413_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1414_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1415_: u8 = 0;
    let mut v_a_1416_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1418_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1419_: u8 = 0;
    let mut v_val_1421_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1422_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1423_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1424_: u8 = 0;
    let mut v___x_1425_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1426_: u8 = 0;
    let mut v___x_1427_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1428_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1430_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1431_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1432_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1434_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1435_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1436_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1437_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1438_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1439_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1440_: u8 = 0;
    let mut v___x_1441_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1442_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1443_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1444_: u8 = 0;
    let mut v___x_1445_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1446_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_1405_) == 0 {
                    crate::leanh::lean_dec_ref(v___f_1404_);
                    crate::leanh::lean_dec_ref(v___f_1403_);
                    crate::leanh::lean_dec(v_s_1401_);
                    crate::leanh::lean_dec_ref(v___f_1400_);
                    v_a_1407_ = crate::leanh::lean_ctor_get(v_x_1405_, 0);
                    v_isSharedCheck_1415_ = (!crate::leanh::lean_is_exclusive(v_x_1405_)) as u8;
                    if v_isSharedCheck_1415_ == 0 {
                        v___x_1409_ = v_x_1405_;
                        v_isShared_1410_ = v_isSharedCheck_1415_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1407_);
                        crate::leanh::lean_dec(v_x_1405_);
                        v___x_1409_ = crate::leanh::lean_box(0);
                        v_isShared_1410_ = v_isSharedCheck_1415_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_1416_ = crate::leanh::lean_ctor_get(v_x_1405_, 0);
                    v_isSharedCheck_1446_ = (!crate::leanh::lean_is_exclusive(v_x_1405_)) as u8;
                    if v_isSharedCheck_1446_ == 0 {
                        v___x_1418_ = v_x_1405_;
                        v_isShared_1419_ = v_isSharedCheck_1446_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1416_);
                        crate::leanh::lean_dec(v_x_1405_);
                        v___x_1418_ = crate::leanh::lean_box(0);
                        v_isShared_1419_ = v_isSharedCheck_1446_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_1410_ == 0 {
                    v___x_1412_ = v___x_1409_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1414_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1414_, 0, v_a_1407_);
                    v___x_1412_ = v_reuseFailAlloc_1414_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_1413_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1413_, 0, v___x_1412_);
                return v___x_1413_;
            }
            3 => {
                v___x_1426_ = (crate::leanh::lean_unbox(v_a_1416_) as u8);
                if v___x_1426_ == 0 {
                    crate::leanh::lean_dec_ref(v___f_1404_);
                    crate::leanh::lean_dec_ref(v___f_1403_);
                    v___x_1427_ = lean_uv_udp_cancel_recv(v_s_1401_);
                    crate::leanh::lean_dec(v_s_1401_);
                    if crate::leanh::lean_obj_tag(v___x_1427_) == 0 {
                        v_a_1428_ = crate::leanh::lean_ctor_get(v___x_1427_, 0);
                        crate::leanh::lean_inc(v_a_1428_);
                        crate::leanh::lean_dec_ref_known(v___x_1427_, 1);
                        if v_isShared_1419_ == 0 {
                            crate::leanh::lean_ctor_set(v___x_1418_, 0, v_a_1428_);
                            v___x_1430_ = v___x_1418_;
                            state = 5;
                            continue;
                        } else {
                            v_reuseFailAlloc_1431_ =
                                crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_1431_, 0, v_a_1428_);
                            v___x_1430_ = v_reuseFailAlloc_1431_;
                            state = 5;
                            continue;
                        }
                    } else {
                        v_a_1432_ = crate::leanh::lean_ctor_get(v___x_1427_, 0);
                        crate::leanh::lean_inc(v_a_1432_);
                        crate::leanh::lean_dec_ref_known(v___x_1427_, 1);
                        if v_isShared_1419_ == 0 {
                            crate::leanh::lean_ctor_set_tag(v___x_1418_, 0);
                            crate::leanh::lean_ctor_set(v___x_1418_, 0, v_a_1432_);
                            v___x_1434_ = v___x_1418_;
                            state = 6;
                            continue;
                        } else {
                            v_reuseFailAlloc_1435_ =
                                crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_1435_, 0, v_a_1432_);
                            v___x_1434_ = v_reuseFailAlloc_1435_;
                            state = 6;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_1418_);
                    crate::leanh::lean_dec_ref(v___f_1400_);
                    v___x_1436_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___x_1437_ = crate::leanh::lean_box_uint64(v_size_1402_);
                    v___f_1438_ = crate::leanh::lean_alloc_closure(l_Std_Async_Waiter_race___at___00Std_Async_UDP_Socket_recvSelector_spec__1___lam__1___boxed as *mut core::ffi::c_void, 4, 3);
                    crate::leanh::lean_closure_set(v___f_1438_, 0, v___x_1436_);
                    crate::leanh::lean_closure_set(v___f_1438_, 1, v_s_1401_);
                    crate::leanh::lean_closure_set(v___f_1438_, 2, v___x_1437_);
                    v___x_1439_ = lean_io_as_task(v___f_1438_, v___x_1436_);
                    v___x_1440_ = (crate::leanh::lean_unbox(v_a_1416_) as u8);
                    crate::leanh::lean_dec(v_a_1416_);
                    v___x_1441_ =
                        lean_task_bind(v___x_1439_, v___f_1403_, v___x_1436_, v___x_1440_);
                    v___x_1442_ = lean_task_get_own(v___x_1441_);
                    v___x_1443_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1443_, 0, v___x_1442_);
                    v___x_1444_ = 0;
                    v___x_1445_ =
                        l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(
                            crate::leanh::lean_box(0),
                            crate::leanh::lean_box(0),
                            v___x_1436_,
                            v___x_1444_,
                            v___x_1443_,
                            v___f_1404_,
                        );
                    return v___x_1445_;
                }
            }
            4 => {
                v___x_1422_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1422_, 0, v_val_1421_);
                v___x_1423_ = crate::leanh::lean_unsigned_to_nat(0);
                v___x_1424_ = (crate::leanh::lean_unbox(v_a_1416_) as u8);
                crate::leanh::lean_dec(v_a_1416_);
                v___x_1425_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(
                    crate::leanh::lean_box(0),
                    crate::leanh::lean_box(0),
                    v___x_1423_,
                    v___x_1424_,
                    v___x_1422_,
                    v___f_1400_,
                );
                return v___x_1425_;
            }
            5 => {
                v_val_1421_ = v___x_1430_;
                state = 4;
                continue;
            }
            6 => {
                v_val_1421_ = v___x_1434_;
                state = 4;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Async_UDP_Socket_recvSelector___lam__10___boxed(
    mut v___f_1447_: *mut crate::leanh::LeanObject,
    mut v_s_1448_: *mut crate::leanh::LeanObject,
    mut v_size_1449_: *mut crate::leanh::LeanObject,
    mut v___f_1450_: *mut crate::leanh::LeanObject,
    mut v___f_1451_: *mut crate::leanh::LeanObject,
    mut v_x_1452_: *mut crate::leanh::LeanObject,
    mut v___y_1453_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_size_boxed_1454_: u64 = 0;
    let mut v_res_1455_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_size_boxed_1454_ = crate::leanh::lean_unbox_uint64(v_size_1449_);
    crate::leanh::lean_dec_ref(v_size_1449_);
    v_res_1455_ = l_Std_Async_UDP_Socket_recvSelector___lam__10(
        v___f_1447_,
        v_s_1448_,
        v_size_boxed_1454_,
        v___f_1450_,
        v___f_1451_,
        v_x_1452_,
    );
    return v_res_1455_;
}
pub unsafe fn l_Std_Async_UDP_Socket_recvSelector___lam__7(
    mut v___f_1456_: *mut crate::leanh::LeanObject,
    mut v_x_1457_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_a_1459_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1461_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1462_: u8 = 0;
    let mut v___x_1464_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1465_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1466_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1467_: u8 = 0;
    let mut v_a_1468_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1470_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1471_: u8 = 0;
    let mut v___x_1472_: u8 = 0;
    let mut v___x_1473_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1475_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1476_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1477_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1478_: u8 = 0;
    let mut v___x_1479_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1480_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1481_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_1457_) == 0 {
                    crate::leanh::lean_dec_ref(v___f_1456_);
                    v_a_1459_ = crate::leanh::lean_ctor_get(v_x_1457_, 0);
                    v_isSharedCheck_1467_ = (!crate::leanh::lean_is_exclusive(v_x_1457_)) as u8;
                    if v_isSharedCheck_1467_ == 0 {
                        v___x_1461_ = v_x_1457_;
                        v_isShared_1462_ = v_isSharedCheck_1467_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1459_);
                        crate::leanh::lean_dec(v_x_1457_);
                        v___x_1461_ = crate::leanh::lean_box(0);
                        v_isShared_1462_ = v_isSharedCheck_1467_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_1468_ = crate::leanh::lean_ctor_get(v_x_1457_, 0);
                    v_isSharedCheck_1481_ = (!crate::leanh::lean_is_exclusive(v_x_1457_)) as u8;
                    if v_isSharedCheck_1481_ == 0 {
                        v___x_1470_ = v_x_1457_;
                        v_isShared_1471_ = v_isSharedCheck_1481_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1468_);
                        crate::leanh::lean_dec(v_x_1457_);
                        v___x_1470_ = crate::leanh::lean_box(0);
                        v_isShared_1471_ = v_isSharedCheck_1481_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_1462_ == 0 {
                    v___x_1464_ = v___x_1461_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1466_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1466_, 0, v_a_1459_);
                    v___x_1464_ = v_reuseFailAlloc_1466_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_1465_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1465_, 0, v___x_1464_);
                return v___x_1465_;
            }
            3 => {
                v___x_1472_ = l_IO_Promise_isResolved___redArg(v_a_1468_);
                crate::leanh::lean_dec(v_a_1468_);
                v___x_1473_ = crate::leanh::lean_box((v___x_1472_) as usize);
                if v_isShared_1471_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1470_, 0, v___x_1473_);
                    v___x_1475_ = v___x_1470_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1480_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1480_, 0, v___x_1473_);
                    v___x_1475_ = v_reuseFailAlloc_1480_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_1476_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1476_, 0, v___x_1475_);
                v___x_1477_ = crate::leanh::lean_unsigned_to_nat(0);
                v___x_1478_ = 0;
                v___x_1479_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(
                    crate::leanh::lean_box(0),
                    crate::leanh::lean_box(0),
                    v___x_1477_,
                    v___x_1478_,
                    v___x_1476_,
                    v___f_1456_,
                );
                return v___x_1479_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Async_UDP_Socket_recvSelector___lam__7___boxed(
    mut v___f_1482_: *mut crate::leanh::LeanObject,
    mut v_x_1483_: *mut crate::leanh::LeanObject,
    mut v___y_1484_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1485_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1485_ = l_Std_Async_UDP_Socket_recvSelector___lam__7(v___f_1482_, v_x_1483_);
    return v_res_1485_;
}
pub unsafe fn l_Std_Async_UDP_Socket_recvSelector___lam__8(
    mut v___f_1486_: *mut crate::leanh::LeanObject,
    mut v_s_1487_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_val_1490_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1491_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1492_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1493_: u8 = 0;
    let mut v___x_1494_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1495_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1496_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1498_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1499_: u8 = 0;
    let mut v___x_1501_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1502_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1503_: u8 = 0;
    let mut v_a_1504_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1506_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1507_: u8 = 0;
    let mut v___x_1509_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1510_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1511_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1495_ = lean_uv_udp_wait_readable(v_s_1487_);
                if crate::leanh::lean_obj_tag(v___x_1495_) == 0 {
                    v_a_1496_ = crate::leanh::lean_ctor_get(v___x_1495_, 0);
                    v_isSharedCheck_1503_ = (!crate::leanh::lean_is_exclusive(v___x_1495_)) as u8;
                    if v_isSharedCheck_1503_ == 0 {
                        v___x_1498_ = v___x_1495_;
                        v_isShared_1499_ = v_isSharedCheck_1503_;
                        state = 2;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1496_);
                        crate::leanh::lean_dec(v___x_1495_);
                        v___x_1498_ = crate::leanh::lean_box(0);
                        v_isShared_1499_ = v_isSharedCheck_1503_;
                        state = 2;
                        continue;
                    }
                } else {
                    v_a_1504_ = crate::leanh::lean_ctor_get(v___x_1495_, 0);
                    v_isSharedCheck_1511_ = (!crate::leanh::lean_is_exclusive(v___x_1495_)) as u8;
                    if v_isSharedCheck_1511_ == 0 {
                        v___x_1506_ = v___x_1495_;
                        v_isShared_1507_ = v_isSharedCheck_1511_;
                        state = 4;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1504_);
                        crate::leanh::lean_dec(v___x_1495_);
                        v___x_1506_ = crate::leanh::lean_box(0);
                        v_isShared_1507_ = v_isSharedCheck_1511_;
                        state = 4;
                        continue;
                    }
                }
            }
            1 => {
                v___x_1491_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1491_, 0, v_val_1490_);
                v___x_1492_ = crate::leanh::lean_unsigned_to_nat(0);
                v___x_1493_ = 0;
                v___x_1494_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(
                    crate::leanh::lean_box(0),
                    crate::leanh::lean_box(0),
                    v___x_1492_,
                    v___x_1493_,
                    v___x_1491_,
                    v___f_1486_,
                );
                return v___x_1494_;
            }
            2 => {
                if v_isShared_1499_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_1498_, 1);
                    v___x_1501_ = v___x_1498_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_1502_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1502_, 0, v_a_1496_);
                    v___x_1501_ = v_reuseFailAlloc_1502_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v_val_1490_ = v___x_1501_;
                state = 1;
                continue;
            }
            4 => {
                if v_isShared_1507_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_1506_, 0);
                    v___x_1509_ = v___x_1506_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_1510_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1510_, 0, v_a_1504_);
                    v___x_1509_ = v_reuseFailAlloc_1510_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v_val_1490_ = v___x_1509_;
                state = 1;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Async_UDP_Socket_recvSelector___lam__8___boxed(
    mut v___f_1512_: *mut crate::leanh::LeanObject,
    mut v_s_1513_: *mut crate::leanh::LeanObject,
    mut v___y_1514_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1515_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1515_ = l_Std_Async_UDP_Socket_recvSelector___lam__8(v___f_1512_, v_s_1513_);
    crate::leanh::lean_dec(v_s_1513_);
    return v_res_1515_;
}
pub unsafe fn l_Std_Async_UDP_Socket_recvSelector(
    mut v_s_1518_: *mut crate::leanh::LeanObject,
    mut v_size_1519_: u64,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_1520_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1521_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1522_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1523_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1524_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1525_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1526_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1527_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1528_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1529_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1530_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_1520_ =
        l_Std_Async_Waiter_race___at___00Std_Async_UDP_Socket_recvSelector_spec__1___closed__0;
    v___f_1521_ = l_Std_Async_UDP_Socket_recvSelector___closed__0;
    v___f_1522_ = l_Std_Async_UDP_Socket_recvSelector___closed__1;
    crate::leanh::lean_inc_n(v_s_1518_, 3);
    v___f_1523_ = crate::leanh::lean_alloc_closure(
        l_Std_Async_UDP_Socket_recvSelector___lam__2___boxed as *mut core::ffi::c_void,
        2,
        1,
    );
    crate::leanh::lean_closure_set(v___f_1523_, 0, v_s_1518_);
    v___x_1524_ = crate::leanh::lean_box_uint64(v_size_1519_);
    v___f_1525_ = crate::leanh::lean_alloc_closure(
        l_Std_Async_UDP_Socket_recvSelector___lam__6___boxed as *mut core::ffi::c_void,
        4,
        2,
    );
    crate::leanh::lean_closure_set(v___f_1525_, 0, v_s_1518_);
    crate::leanh::lean_closure_set(v___f_1525_, 1, v___x_1524_);
    v___x_1526_ = crate::leanh::lean_box_uint64(v_size_1519_);
    v___f_1527_ = crate::leanh::lean_alloc_closure(
        l_Std_Async_UDP_Socket_recvSelector___lam__10___boxed as *mut core::ffi::c_void,
        7,
        5,
    );
    crate::leanh::lean_closure_set(v___f_1527_, 0, v___f_1522_);
    crate::leanh::lean_closure_set(v___f_1527_, 1, v_s_1518_);
    crate::leanh::lean_closure_set(v___f_1527_, 2, v___x_1526_);
    crate::leanh::lean_closure_set(v___f_1527_, 3, v___f_1520_);
    crate::leanh::lean_closure_set(v___f_1527_, 4, v___f_1521_);
    v___f_1528_ = crate::leanh::lean_alloc_closure(
        l_Std_Async_UDP_Socket_recvSelector___lam__7___boxed as *mut core::ffi::c_void,
        3,
        1,
    );
    crate::leanh::lean_closure_set(v___f_1528_, 0, v___f_1527_);
    v___f_1529_ = crate::leanh::lean_alloc_closure(
        l_Std_Async_UDP_Socket_recvSelector___lam__8___boxed as *mut core::ffi::c_void,
        3,
        2,
    );
    crate::leanh::lean_closure_set(v___f_1529_, 0, v___f_1528_);
    crate::leanh::lean_closure_set(v___f_1529_, 1, v_s_1518_);
    v___x_1530_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1530_, 0, v___f_1529_);
    crate::leanh::lean_ctor_set(v___x_1530_, 1, v___f_1525_);
    crate::leanh::lean_ctor_set(v___x_1530_, 2, v___f_1523_);
    return v___x_1530_;
}
pub unsafe fn l_Std_Async_UDP_Socket_recvSelector___boxed(
    mut v_s_1531_: *mut crate::leanh::LeanObject,
    mut v_size_1532_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_size_boxed_1533_: u64 = 0;
    let mut v_res_1534_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_size_boxed_1533_ = crate::leanh::lean_unbox_uint64(v_size_1532_);
    crate::leanh::lean_dec_ref(v_size_1532_);
    v_res_1534_ = l_Std_Async_UDP_Socket_recvSelector(v_s_1531_, v_size_boxed_1533_);
    return v_res_1534_;
}
pub unsafe fn l_Std_Async_UDP_Socket_getSockName(
    mut v_s_1535_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1537_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1537_ = lean_uv_udp_getsockname(v_s_1535_);
    return v___x_1537_;
}
pub unsafe fn l_Std_Async_UDP_Socket_getSockName___boxed(
    mut v_s_1538_: *mut crate::leanh::LeanObject,
    mut v_a_1539_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1540_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1540_ = l_Std_Async_UDP_Socket_getSockName(v_s_1538_);
    crate::leanh::lean_dec(v_s_1538_);
    return v_res_1540_;
}
pub unsafe fn l_Std_Async_UDP_Socket_getPeerName(
    mut v_s_1541_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1543_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1543_ = lean_uv_udp_getpeername(v_s_1541_);
    return v___x_1543_;
}
pub unsafe fn l_Std_Async_UDP_Socket_getPeerName___boxed(
    mut v_s_1544_: *mut crate::leanh::LeanObject,
    mut v_a_1545_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1546_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1546_ = l_Std_Async_UDP_Socket_getPeerName(v_s_1544_);
    crate::leanh::lean_dec(v_s_1544_);
    return v_res_1546_;
}
pub unsafe fn l_Std_Async_UDP_Socket_setBroadcast(
    mut v_s_1547_: *mut crate::leanh::LeanObject,
    mut v_enable_1548_: u8,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1550_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1550_ = lean_uv_udp_set_broadcast(v_s_1547_, v_enable_1548_);
    return v___x_1550_;
}
pub unsafe fn l_Std_Async_UDP_Socket_setBroadcast___boxed(
    mut v_s_1551_: *mut crate::leanh::LeanObject,
    mut v_enable_1552_: *mut crate::leanh::LeanObject,
    mut v_a_1553_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_enable_boxed_1554_: u8 = 0;
    let mut v_res_1555_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_enable_boxed_1554_ = (crate::leanh::lean_unbox(v_enable_1552_) as u8);
    v_res_1555_ = l_Std_Async_UDP_Socket_setBroadcast(v_s_1551_, v_enable_boxed_1554_);
    crate::leanh::lean_dec(v_s_1551_);
    return v_res_1555_;
}
pub unsafe fn l_Std_Async_UDP_Socket_setMulticastLoop(
    mut v_s_1556_: *mut crate::leanh::LeanObject,
    mut v_enable_1557_: u8,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1559_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1559_ = lean_uv_udp_set_multicast_loop(v_s_1556_, v_enable_1557_);
    return v___x_1559_;
}
pub unsafe fn l_Std_Async_UDP_Socket_setMulticastLoop___boxed(
    mut v_s_1560_: *mut crate::leanh::LeanObject,
    mut v_enable_1561_: *mut crate::leanh::LeanObject,
    mut v_a_1562_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_enable_boxed_1563_: u8 = 0;
    let mut v_res_1564_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_enable_boxed_1563_ = (crate::leanh::lean_unbox(v_enable_1561_) as u8);
    v_res_1564_ = l_Std_Async_UDP_Socket_setMulticastLoop(v_s_1560_, v_enable_boxed_1563_);
    crate::leanh::lean_dec(v_s_1560_);
    return v_res_1564_;
}
pub unsafe fn l_Std_Async_UDP_Socket_setMulticastTTL(
    mut v_s_1565_: *mut crate::leanh::LeanObject,
    mut v_ttl_1566_: u32,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1568_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1568_ = lean_uv_udp_set_multicast_ttl(v_s_1565_, v_ttl_1566_);
    return v___x_1568_;
}
pub unsafe fn l_Std_Async_UDP_Socket_setMulticastTTL___boxed(
    mut v_s_1569_: *mut crate::leanh::LeanObject,
    mut v_ttl_1570_: *mut crate::leanh::LeanObject,
    mut v_a_1571_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_ttl_boxed_1572_: u32 = 0;
    let mut v_res_1573_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_ttl_boxed_1572_ = crate::leanh::lean_unbox_uint32(v_ttl_1570_);
    crate::leanh::lean_dec(v_ttl_1570_);
    v_res_1573_ = l_Std_Async_UDP_Socket_setMulticastTTL(v_s_1569_, v_ttl_boxed_1572_);
    crate::leanh::lean_dec(v_s_1569_);
    return v_res_1573_;
}
pub unsafe fn l_Std_Async_UDP_Socket_setMembership(
    mut v_s_1574_: *mut crate::leanh::LeanObject,
    mut v_multicastAddr_1575_: *mut crate::leanh::LeanObject,
    mut v_interfaceAddr_1576_: *mut crate::leanh::LeanObject,
    mut v_membership_1577_: u8,
) -> *mut crate::leanh::LeanObject {
    if v_membership_1577_ == 0 {
        let mut v___x_1579_: u8 = 0;
        let mut v___x_1580_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_1579_ = 0;
        v___x_1580_ = lean_uv_udp_set_membership(
            v_s_1574_,
            v_multicastAddr_1575_,
            v_interfaceAddr_1576_,
            v___x_1579_,
        );
        return v___x_1580_;
    } else {
        let mut v___x_1581_: u8 = 0;
        let mut v___x_1582_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_1581_ = 1;
        v___x_1582_ = lean_uv_udp_set_membership(
            v_s_1574_,
            v_multicastAddr_1575_,
            v_interfaceAddr_1576_,
            v___x_1581_,
        );
        return v___x_1582_;
    }
}
pub unsafe fn l_Std_Async_UDP_Socket_setMembership___boxed(
    mut v_s_1583_: *mut crate::leanh::LeanObject,
    mut v_multicastAddr_1584_: *mut crate::leanh::LeanObject,
    mut v_interfaceAddr_1585_: *mut crate::leanh::LeanObject,
    mut v_membership_1586_: *mut crate::leanh::LeanObject,
    mut v_a_1587_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_membership_boxed_1588_: u8 = 0;
    let mut v_res_1589_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_membership_boxed_1588_ = (crate::leanh::lean_unbox(v_membership_1586_) as u8);
    v_res_1589_ = l_Std_Async_UDP_Socket_setMembership(
        v_s_1583_,
        v_multicastAddr_1584_,
        v_interfaceAddr_1585_,
        v_membership_boxed_1588_,
    );
    crate::leanh::lean_dec(v_interfaceAddr_1585_);
    crate::leanh::lean_dec_ref(v_multicastAddr_1584_);
    crate::leanh::lean_dec(v_s_1583_);
    return v_res_1589_;
}
pub unsafe fn l_Std_Async_UDP_Socket_setMulticastInterface(
    mut v_s_1590_: *mut crate::leanh::LeanObject,
    mut v_interfaceAddr_1591_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1593_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1593_ = lean_uv_udp_set_multicast_interface(v_s_1590_, v_interfaceAddr_1591_);
    return v___x_1593_;
}
pub unsafe fn l_Std_Async_UDP_Socket_setMulticastInterface___boxed(
    mut v_s_1594_: *mut crate::leanh::LeanObject,
    mut v_interfaceAddr_1595_: *mut crate::leanh::LeanObject,
    mut v_a_1596_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1597_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1597_ = l_Std_Async_UDP_Socket_setMulticastInterface(v_s_1594_, v_interfaceAddr_1595_);
    crate::leanh::lean_dec_ref(v_interfaceAddr_1595_);
    crate::leanh::lean_dec(v_s_1594_);
    return v_res_1597_;
}
pub unsafe fn l_Std_Async_UDP_Socket_setTTL(
    mut v_s_1598_: *mut crate::leanh::LeanObject,
    mut v_ttl_1599_: u32,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1601_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1601_ = lean_uv_udp_set_ttl(v_s_1598_, v_ttl_1599_);
    return v___x_1601_;
}
pub unsafe fn l_Std_Async_UDP_Socket_setTTL___boxed(
    mut v_s_1602_: *mut crate::leanh::LeanObject,
    mut v_ttl_1603_: *mut crate::leanh::LeanObject,
    mut v_a_1604_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_ttl_boxed_1605_: u32 = 0;
    let mut v_res_1606_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_ttl_boxed_1605_ = crate::leanh::lean_unbox_uint32(v_ttl_1603_);
    crate::leanh::lean_dec(v_ttl_1603_);
    v_res_1606_ = l_Std_Async_UDP_Socket_setTTL(v_s_1602_, v_ttl_boxed_1605_);
    crate::leanh::lean_dec(v_s_1602_);
    return v_res_1606_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Std_Async_UDP(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Std_Time(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Std_Internal_UV_UDP(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Std_Async_Select(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Std_Async_UDP(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_meta_initialized = true;
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Std_Async_UDP(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Std_Time(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Std_Internal_UV_UDP(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Std_Async_Select(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Std_Async_UDP(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Std_Async_UDP(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Std_Async_UDP(builtin);
}
