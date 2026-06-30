// Lean compiler output
// Module: Std.Http.Data.Body.Empty
// Imports: Std.Http.Data.Request Std.Http.Data.Response Std.Http.Data.Body.Any
use crate::ffi::lean_io_promise_resolve;
use crate::r#gen::Init::Prelude::{
    l_instMonadLiftT___lam__0___boxed, l_instMonadLiftTOfMonadLift___redArg___lam__0,
};
use crate::r#gen::Init::System::IO::l_IO_instMonadLiftSTRealWorldBaseIO___lam__0___boxed;
use crate::r#gen::Std::Async::Basic::{
    l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask,
    l_Std_Async_BaseAsync_lift___boxed, l_Std_Async_EAsync_instMonad,
    l_Std_Async_EAsync_instMonadLiftBaseAsync,
};
use crate::r#gen::Std::Async::Select::l_Std_Async_Waiter_race___redArg;
use crate::r#gen::Std::Http::Data::Body::Any::{
    initialize_Std_Http_Data_Body_Any, l_Std_Http_Body_Any_ofBody,
    l_Std_Http_Body_Any_ofBody___redArg, runtime_initialize_Std_Http_Data_Body_Any,
};
use crate::r#gen::Std::Http::Data::Request::{
    initialize_Std_Http_Data_Request, l_Std_Http_Request_Builder_body___redArg,
    runtime_initialize_Std_Http_Data_Request,
};
use crate::r#gen::Std::Http::Data::Response::{
    initialize_Std_Http_Data_Response, l_Std_Http_Response_Builder_body___redArg,
    runtime_initialize_Std_Http_Data_Response,
};
pub static mut l_Std_Http_Body_instInhabitedEmpty_default: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static mut l_Std_Http_Body_instInhabitedEmpty: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Std_Http_Body_instBEqEmpty___closed__0_value: leanh::LeanClosureObject<0> =
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
        m_fun: l_Std_Http_Body_instBEqEmpty_beq___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Std_Http_Body_instBEqEmpty___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Body_instBEqEmpty___closed__0_value)
        as *mut leanh::LeanObject;
pub static mut l_Std_Http_Body_instBEqEmpty: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Body_instBEqEmpty___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Std_Http_Body_Empty_recv___redArg___closed__0_value: leanh::LeanCtorObject<1> =
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
static mut l_Std_Http_Body_Empty_recv___redArg___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Body_Empty_recv___redArg___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Std_Http_Body_Empty_recv___redArg___closed__1_value: leanh::LeanCtorObject<1> =
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
            core::ptr::addr_of!(l_Std_Http_Body_Empty_recv___redArg___closed__0_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Std_Http_Body_Empty_recv___redArg___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Body_Empty_recv___redArg___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Std_Http_Body_Empty_close___redArg___closed__0_value: leanh::LeanCtorObject<1> =
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
static mut l_Std_Http_Body_Empty_close___redArg___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Body_Empty_close___redArg___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Std_Http_Body_Empty_close___redArg___closed__1_value: leanh::LeanCtorObject<1> =
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
            core::ptr::addr_of!(l_Std_Http_Body_Empty_close___redArg___closed__0_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Std_Http_Body_Empty_close___redArg___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Body_Empty_close___redArg___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Std_Http_Body_Empty_isClosed___redArg___closed__0_value: leanh::LeanCtorObject<
    1,
> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 1,
    },
    m_objs: [(((1 as usize) << 1) | 1) as *mut leanh::LeanObject],
};
static mut l_Std_Http_Body_Empty_isClosed___redArg___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Body_Empty_isClosed___redArg___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Std_Http_Body_Empty_isClosed___redArg___closed__1_value: leanh::LeanCtorObject<
    1,
> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 0,
    },
    m_objs: [
        core::ptr::addr_of!(l_Std_Http_Body_Empty_isClosed___redArg___closed__0_value)
            as *mut leanh::LeanObject,
    ],
};
static mut l_Std_Http_Body_Empty_isClosed___redArg___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Body_Empty_isClosed___redArg___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Std_Http_Body_Empty_tryRecv___redArg___closed__0_value: leanh::LeanCtorObject<
    1,
> = leanh::LeanCtorObject {
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
static mut l_Std_Http_Body_Empty_tryRecv___redArg___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Body_Empty_tryRecv___redArg___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Std_Http_Body_Empty_tryRecv___redArg___closed__1_value: leanh::LeanCtorObject<
    1,
> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Std_Http_Body_Empty_tryRecv___redArg___closed__0_value)
            as *mut leanh::LeanObject,
    ],
};
static mut l_Std_Http_Body_Empty_tryRecv___redArg___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Body_Empty_tryRecv___redArg___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Std_Http_Body_Empty_tryRecv___redArg___closed__2_value: leanh::LeanCtorObject<
    1,
> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 0,
    },
    m_objs: [
        core::ptr::addr_of!(l_Std_Http_Body_Empty_tryRecv___redArg___closed__1_value)
            as *mut leanh::LeanObject,
    ],
};
static mut l_Std_Http_Body_Empty_tryRecv___redArg___closed__2: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Body_Empty_tryRecv___redArg___closed__2_value)
        as *mut leanh::LeanObject;
pub static l_Std_Http_Body_Empty_recvSelector___lam__2___closed__0_value:
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
    m_fun: l_Std_Http_Body_Empty_recvSelector___lam__1___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 1,
    m_objs: [(((0 as usize) << 1) | 1) as *mut leanh::LeanObject],
};
static mut l_Std_Http_Body_Empty_recvSelector___lam__2___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Body_Empty_recvSelector___lam__2___closed__0_value)
        as *mut leanh::LeanObject;
static mut l_Std_Http_Body_Empty_recvSelector___closed__0_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Http_Body_Empty_recvSelector___closed__0: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_Http_Body_Empty_recvSelector___closed__1_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Http_Body_Empty_recvSelector___closed__1: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Std_Http_Body_Empty_recvSelector___closed__2_value: leanh::LeanClosureObject<
    0,
> = leanh::LeanClosureObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Std_Async_BaseAsync_lift___boxed as *const core::ffi::c_void,
    m_arity: 3,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_Http_Body_Empty_recvSelector___closed__2: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Body_Empty_recvSelector___closed__2_value)
        as *mut leanh::LeanObject;
pub static l_Std_Http_Body_Empty_recvSelector___closed__3_value: leanh::LeanClosureObject<
    0,
> = leanh::LeanClosureObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_instMonadLiftT___lam__0___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_Http_Body_Empty_recvSelector___closed__3: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Body_Empty_recvSelector___closed__3_value)
        as *mut leanh::LeanObject;
pub static l_Std_Http_Body_Empty_recvSelector___closed__4_value: leanh::LeanClosureObject<
    0,
> = leanh::LeanClosureObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_IO_instMonadLiftSTRealWorldBaseIO___lam__0___boxed as *const core::ffi::c_void,
    m_arity: 3,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_Http_Body_Empty_recvSelector___closed__4: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Body_Empty_recvSelector___closed__4_value)
        as *mut leanh::LeanObject;
pub static l_Std_Http_Body_Empty_recvSelector___closed__5_value: leanh::LeanClosureObject<
    2,
> = leanh::LeanClosureObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut leanh::LeanObject>() * 2) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_instMonadLiftTOfMonadLift___redArg___lam__0 as *const core::ffi::c_void,
    m_arity: 4,
    m_num_fixed: 2,
    m_objs: [
        core::ptr::addr_of!(l_Std_Http_Body_Empty_recvSelector___closed__3_value)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Std_Http_Body_Empty_recvSelector___closed__4_value)
            as *mut leanh::LeanObject,
    ],
};
static mut l_Std_Http_Body_Empty_recvSelector___closed__5: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Body_Empty_recvSelector___closed__5_value)
        as *mut leanh::LeanObject;
pub static l_Std_Http_Body_Empty_recvSelector___closed__6_value: leanh::LeanClosureObject<
    2,
> = leanh::LeanClosureObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut leanh::LeanObject>() * 2) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_instMonadLiftTOfMonadLift___redArg___lam__0 as *const core::ffi::c_void,
    m_arity: 4,
    m_num_fixed: 2,
    m_objs: [
        core::ptr::addr_of!(l_Std_Http_Body_Empty_recvSelector___closed__5_value)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Std_Http_Body_Empty_recvSelector___closed__2_value)
            as *mut leanh::LeanObject,
    ],
};
static mut l_Std_Http_Body_Empty_recvSelector___closed__6: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Body_Empty_recvSelector___closed__6_value)
        as *mut leanh::LeanObject;
static mut l_Std_Http_Body_Empty_recvSelector___closed__7_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Http_Body_Empty_recvSelector___closed__7: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Std_Http_Body_Empty_recvSelector___closed__8_value: leanh::LeanClosureObject<
    1,
> = leanh::LeanClosureObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Std_Http_Body_Empty_recvSelector___lam__0___boxed as *const core::ffi::c_void,
    m_arity: 3,
    m_num_fixed: 1,
    m_objs: [(((0 as usize) << 1) | 1) as *mut leanh::LeanObject],
};
static mut l_Std_Http_Body_Empty_recvSelector___closed__8: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Body_Empty_recvSelector___closed__8_value)
        as *mut leanh::LeanObject;
static mut l_Std_Http_Body_Empty_recvSelector___closed__9_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Http_Body_Empty_recvSelector___closed__9: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Std_Http_Body_Empty_recvSelector___closed__10_value: leanh::LeanClosureObject<
    1,
> = leanh::LeanClosureObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Std_Http_Body_Empty_recvSelector___lam__3___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 1,
    m_objs: [
        core::ptr::addr_of!(l_Std_Http_Body_Empty_tryRecv___redArg___closed__0_value)
            as *mut leanh::LeanObject,
    ],
};
static mut l_Std_Http_Body_Empty_recvSelector___closed__10: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Body_Empty_recvSelector___closed__10_value)
        as *mut leanh::LeanObject;
static mut l_Std_Http_Body_Empty_recvSelector___closed__11_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Http_Body_Empty_recvSelector___closed__11: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Std_Http_Body_instEmpty___lam__0___closed__0_value: leanh::LeanCtorObject<1> =
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
static mut l_Std_Http_Body_instEmpty___lam__0___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Body_instEmpty___lam__0___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Std_Http_Body_instEmpty___lam__0___closed__1_value: leanh::LeanCtorObject<1> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Std_Http_Body_instEmpty___lam__0___closed__0_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Std_Http_Body_instEmpty___lam__0___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Body_instEmpty___lam__0___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Std_Http_Body_instEmpty___lam__0___closed__2_value: leanh::LeanCtorObject<1> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Std_Http_Body_instEmpty___lam__0___closed__1_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Std_Http_Body_instEmpty___lam__0___closed__2: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Body_instEmpty___lam__0___closed__2_value)
        as *mut leanh::LeanObject;
pub static l_Std_Http_Body_instEmpty___lam__0___closed__3_value: leanh::LeanCtorObject<1> =
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
            core::ptr::addr_of!(l_Std_Http_Body_instEmpty___lam__0___closed__2_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Std_Http_Body_instEmpty___lam__0___closed__3: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Body_instEmpty___lam__0___closed__3_value)
        as *mut leanh::LeanObject;
pub static l_Std_Http_Body_instEmpty___closed__0_value: leanh::LeanClosureObject<0> =
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
        m_fun: l_Std_Http_Body_instEmpty___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Std_Http_Body_instEmpty___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Body_instEmpty___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Std_Http_Body_instEmpty___closed__1_value: leanh::LeanClosureObject<0> =
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
        m_fun: l_Std_Http_Body_instEmpty___lam__1___boxed as *const core::ffi::c_void,
        m_arity: 3,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Std_Http_Body_instEmpty___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Body_instEmpty___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Std_Http_Body_instEmpty___closed__2_value: leanh::LeanClosureObject<0> =
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
        m_fun: l_Std_Http_Body_Empty_recv___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Std_Http_Body_instEmpty___closed__2: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Body_instEmpty___closed__2_value)
        as *mut leanh::LeanObject;
pub static l_Std_Http_Body_instEmpty___closed__3_value: leanh::LeanClosureObject<0> =
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
        m_fun: l_Std_Http_Body_Empty_close___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Std_Http_Body_instEmpty___closed__3: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Body_instEmpty___closed__3_value)
        as *mut leanh::LeanObject;
pub static l_Std_Http_Body_instEmpty___closed__4_value: leanh::LeanClosureObject<0> =
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
        m_fun: l_Std_Http_Body_Empty_isClosed___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Std_Http_Body_instEmpty___closed__4: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Body_instEmpty___closed__4_value)
        as *mut leanh::LeanObject;
pub static l_Std_Http_Body_instEmpty___closed__5_value: leanh::LeanClosureObject<0> =
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
        m_fun: l_Std_Http_Body_Empty_recvSelector as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Std_Http_Body_instEmpty___closed__5: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Body_instEmpty___closed__5_value)
        as *mut leanh::LeanObject;
pub static l_Std_Http_Body_instEmpty___closed__6_value: leanh::LeanClosureObject<0> =
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
        m_fun: l_Std_Http_Body_Empty_tryRecv___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Std_Http_Body_instEmpty___closed__6: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Body_instEmpty___closed__6_value)
        as *mut leanh::LeanObject;
pub static l_Std_Http_Body_instEmpty___closed__7_value: leanh::LeanCtorObject<7> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 7
                + 0) as u16,
            other: 7,
            tag: 0,
        },
        m_objs: [
            core::ptr::addr_of!(l_Std_Http_Body_instEmpty___closed__2_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Std_Http_Body_instEmpty___closed__3_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Std_Http_Body_instEmpty___closed__4_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Std_Http_Body_instEmpty___closed__5_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Std_Http_Body_instEmpty___closed__6_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Std_Http_Body_instEmpty___closed__0_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Std_Http_Body_instEmpty___closed__1_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Std_Http_Body_instEmpty___closed__7: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Body_instEmpty___closed__7_value)
        as *mut leanh::LeanObject;
pub static mut l_Std_Http_Body_instEmpty: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Body_instEmpty___closed__7_value)
        as *mut leanh::LeanObject;
pub static l_Std_Http_Body_instCoeEmptyAny___closed__0_value: leanh::LeanClosureObject<2> =
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
        m_fun: l_Std_Http_Body_Any_ofBody as *const core::ffi::c_void,
        m_arity: 3,
        m_num_fixed: 2,
        m_objs: [
            (((0 as usize) << 1) | 1) as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Std_Http_Body_instEmpty___closed__7_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Std_Http_Body_instCoeEmptyAny___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Body_instCoeEmptyAny___closed__0_value)
        as *mut leanh::LeanObject;
pub static mut l_Std_Http_Body_instCoeEmptyAny: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Body_instCoeEmptyAny___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Std_Http_Body_instCoeResponseEmptyAny___closed__0_value:
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
    m_fun: l_Std_Http_Body_instCoeResponseEmptyAny___lam__0 as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 1,
    m_objs: [
        core::ptr::addr_of!(l_Std_Http_Body_instEmpty___closed__7_value)
            as *mut leanh::LeanObject,
    ],
};
static mut l_Std_Http_Body_instCoeResponseEmptyAny___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Body_instCoeResponseEmptyAny___closed__0_value)
        as *mut leanh::LeanObject;
pub static mut l_Std_Http_Body_instCoeResponseEmptyAny: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Body_instCoeResponseEmptyAny___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Std_Http_Body_instCoeContextAsyncResponseEmptyAny___closed__0_value:
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
    m_fun: l_Std_Http_Body_instCoeContextAsyncResponseEmptyAny___lam__0___boxed
        as *const core::ffi::c_void,
    m_arity: 3,
    m_num_fixed: 1,
    m_objs: [
        core::ptr::addr_of!(l_Std_Http_Body_instEmpty___closed__7_value)
            as *mut leanh::LeanObject,
    ],
};
static mut l_Std_Http_Body_instCoeContextAsyncResponseEmptyAny___closed__0:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Body_instCoeContextAsyncResponseEmptyAny___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Std_Http_Body_instCoeContextAsyncResponseEmptyAny___closed__1_value:
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
    m_fun: l_Std_Http_Body_instCoeContextAsyncResponseEmptyAny___lam__1___boxed
        as *const core::ffi::c_void,
    m_arity: 4,
    m_num_fixed: 1,
    m_objs: [core::ptr::addr_of!(
        l_Std_Http_Body_instCoeContextAsyncResponseEmptyAny___closed__0_value
    ) as *mut leanh::LeanObject],
};
static mut l_Std_Http_Body_instCoeContextAsyncResponseEmptyAny___closed__1:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Body_instCoeContextAsyncResponseEmptyAny___closed__1_value)
        as *mut leanh::LeanObject;
pub static mut l_Std_Http_Body_instCoeContextAsyncResponseEmptyAny: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Body_instCoeContextAsyncResponseEmptyAny___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Std_Http_Body_instCoeAsyncResponseEmptyContextAsyncAny___closed__0_value:
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
    m_fun: l_Std_Http_Body_instCoeAsyncResponseEmptyContextAsyncAny___lam__1___boxed
        as *const core::ffi::c_void,
    m_arity: 4,
    m_num_fixed: 1,
    m_objs: [core::ptr::addr_of!(
        l_Std_Http_Body_instCoeContextAsyncResponseEmptyAny___closed__0_value
    ) as *mut leanh::LeanObject],
};
static mut l_Std_Http_Body_instCoeAsyncResponseEmptyContextAsyncAny___closed__0:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Body_instCoeAsyncResponseEmptyContextAsyncAny___closed__0_value)
        as *mut leanh::LeanObject;
pub static mut l_Std_Http_Body_instCoeAsyncResponseEmptyContextAsyncAny:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Body_instCoeAsyncResponseEmptyContextAsyncAny___closed__0_value)
        as *mut leanh::LeanObject;
pub unsafe fn l_Std_Http_Body_Empty_toCtorIdx(
    mut v_x_287_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_288_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_288_ = leanh::lean_unsigned_to_nat(0);
    return v___x_288_;
}
pub unsafe fn _init_l_Std_Http_Body_instInhabitedEmpty_default() -> *mut leanh::LeanObject {
    let mut v___x_289_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_289_ = leanh::lean_box(0);
    return v___x_289_;
}
pub unsafe fn _init_l_Std_Http_Body_instInhabitedEmpty() -> *mut leanh::LeanObject {
    let mut v___x_290_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_290_ = leanh::lean_box(0);
    return v___x_290_;
}
pub unsafe fn l_Std_Http_Body_instBEqEmpty_beq(
    mut v_x_291_: *mut leanh::LeanObject,
    mut v_y_292_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_293_: u8 = 0;
    v___x_293_ = 1;
    return v___x_293_;
}
pub unsafe fn l_Std_Http_Body_instBEqEmpty_beq___boxed(
    mut v_x_294_: *mut leanh::LeanObject,
    mut v_y_295_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_296_: u8 = 0;
    let mut v_r_297_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_296_ = l_Std_Http_Body_instBEqEmpty_beq(v_x_294_, v_y_295_);
    v_r_297_ = leanh::lean_box((v_res_296_) as usize);
    return v_r_297_;
}
pub unsafe fn l_Std_Http_Body_Empty_recv___redArg() -> *mut leanh::LeanObject {
    let mut v___x_305_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_305_ = l_Std_Http_Body_Empty_recv___redArg___closed__1;
    return v___x_305_;
}
pub unsafe fn l_Std_Http_Body_Empty_recv___redArg___boxed(
    mut v_a_306_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_307_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_307_ = l_Std_Http_Body_Empty_recv___redArg();
    return v_res_307_;
}
pub unsafe fn l_Std_Http_Body_Empty_recv(
    mut v_x_308_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_310_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_310_ = l_Std_Http_Body_Empty_recv___redArg___closed__1;
    return v___x_310_;
}
pub unsafe fn l_Std_Http_Body_Empty_recv___boxed(
    mut v_x_311_: *mut leanh::LeanObject,
    mut v_a_312_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_313_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_313_ = l_Std_Http_Body_Empty_recv(v_x_311_);
    return v_res_313_;
}
pub unsafe fn l_Std_Http_Body_Empty_close___redArg() -> *mut leanh::LeanObject {
    let mut v___x_319_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_319_ = l_Std_Http_Body_Empty_close___redArg___closed__1;
    return v___x_319_;
}
pub unsafe fn l_Std_Http_Body_Empty_close___redArg___boxed(
    mut v_a_320_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_321_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_321_ = l_Std_Http_Body_Empty_close___redArg();
    return v_res_321_;
}
pub unsafe fn l_Std_Http_Body_Empty_close(
    mut v_x_322_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_324_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_324_ = l_Std_Http_Body_Empty_close___redArg___closed__1;
    return v___x_324_;
}
pub unsafe fn l_Std_Http_Body_Empty_close___boxed(
    mut v_x_325_: *mut leanh::LeanObject,
    mut v_a_326_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_327_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_327_ = l_Std_Http_Body_Empty_close(v_x_325_);
    return v_res_327_;
}
pub unsafe fn l_Std_Http_Body_Empty_isClosed___redArg() -> *mut leanh::LeanObject {
    let mut v___x_334_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_334_ = l_Std_Http_Body_Empty_isClosed___redArg___closed__1;
    return v___x_334_;
}
pub unsafe fn l_Std_Http_Body_Empty_isClosed___redArg___boxed(
    mut v_a_335_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_336_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_336_ = l_Std_Http_Body_Empty_isClosed___redArg();
    return v_res_336_;
}
pub unsafe fn l_Std_Http_Body_Empty_isClosed(
    mut v_x_337_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_339_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_339_ = l_Std_Http_Body_Empty_isClosed___redArg___closed__1;
    return v___x_339_;
}
pub unsafe fn l_Std_Http_Body_Empty_isClosed___boxed(
    mut v_x_340_: *mut leanh::LeanObject,
    mut v_a_341_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_342_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_342_ = l_Std_Http_Body_Empty_isClosed(v_x_340_);
    return v_res_342_;
}
pub unsafe fn l_Std_Http_Body_Empty_tryRecv___redArg() -> *mut leanh::LeanObject {
    let mut v___x_350_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_350_ = l_Std_Http_Body_Empty_tryRecv___redArg___closed__2;
    return v___x_350_;
}
pub unsafe fn l_Std_Http_Body_Empty_tryRecv___redArg___boxed(
    mut v_a_351_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_352_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_352_ = l_Std_Http_Body_Empty_tryRecv___redArg();
    return v_res_352_;
}
pub unsafe fn l_Std_Http_Body_Empty_tryRecv(
    mut v_x_353_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_355_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_355_ = l_Std_Http_Body_Empty_tryRecv___redArg___closed__2;
    return v___x_355_;
}
pub unsafe fn l_Std_Http_Body_Empty_tryRecv___boxed(
    mut v_x_356_: *mut leanh::LeanObject,
    mut v_a_357_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_358_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_358_ = l_Std_Http_Body_Empty_tryRecv(v_x_356_);
    return v_res_358_;
}
pub unsafe fn l_Std_Http_Body_Empty_recvSelector___lam__0(
    mut v___x_359_: *mut leanh::LeanObject,
    mut v_promise_360_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_362_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_363_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_364_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_365_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_362_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_362_, 0, v___x_359_);
    v___x_363_ = lean_io_promise_resolve(v___x_362_, v_promise_360_);
    v___x_364_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_364_, 0, v___x_363_);
    v___x_365_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_365_, 0, v___x_364_);
    return v___x_365_;
}
pub unsafe fn l_Std_Http_Body_Empty_recvSelector___lam__0___boxed(
    mut v___x_366_: *mut leanh::LeanObject,
    mut v_promise_367_: *mut leanh::LeanObject,
    mut v___y_368_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_369_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_369_ = l_Std_Http_Body_Empty_recvSelector___lam__0(v___x_366_, v_promise_367_);
    leanh::lean_dec(v_promise_367_);
    return v_res_369_;
}
pub unsafe fn l_Std_Http_Body_Empty_recvSelector___lam__1(
    mut v___x_370_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_372_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_373_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_372_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_372_, 0, v___x_370_);
    v___x_373_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_373_, 0, v___x_372_);
    return v___x_373_;
}
pub unsafe fn l_Std_Http_Body_Empty_recvSelector___lam__1___boxed(
    mut v___x_374_: *mut leanh::LeanObject,
    mut v___y_375_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_376_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_376_ = l_Std_Http_Body_Empty_recvSelector___lam__1(v___x_374_);
    return v_res_376_;
}
pub unsafe fn l_Std_Http_Body_Empty_recvSelector___lam__2(
    mut v___x_379_: *mut leanh::LeanObject,
    mut v___f_380_: *mut leanh::LeanObject,
    mut v_win_381_: *mut leanh::LeanObject,
    mut v_waiter_382_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_lose_384_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_266__overap_385_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_386_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_lose_384_ = l_Std_Http_Body_Empty_recvSelector___lam__2___closed__0;
    v___x_266__overap_385_ = l_Std_Async_Waiter_race___redArg(
        v___x_379_,
        v___f_380_,
        v_waiter_382_,
        v_lose_384_,
        v_win_381_,
    );
    v___x_386_ = leanh::lean_apply_1(v___x_266__overap_385_, leanh::lean_box(0));
    return v___x_386_;
}
pub unsafe fn l_Std_Http_Body_Empty_recvSelector___lam__2___boxed(
    mut v___x_387_: *mut leanh::LeanObject,
    mut v___f_388_: *mut leanh::LeanObject,
    mut v_win_389_: *mut leanh::LeanObject,
    mut v_waiter_390_: *mut leanh::LeanObject,
    mut v___y_391_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_392_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_392_ = l_Std_Http_Body_Empty_recvSelector___lam__2(
        v___x_387_,
        v___f_388_,
        v_win_389_,
        v_waiter_390_,
    );
    return v_res_392_;
}
pub unsafe fn l_Std_Http_Body_Empty_recvSelector___lam__3(
    mut v___x_393_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_395_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_396_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_395_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_395_, 0, v___x_393_);
    v___x_396_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_396_, 0, v___x_395_);
    return v___x_396_;
}
pub unsafe fn l_Std_Http_Body_Empty_recvSelector___lam__3___boxed(
    mut v___x_397_: *mut leanh::LeanObject,
    mut v___y_398_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_399_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_399_ = l_Std_Http_Body_Empty_recvSelector___lam__3(v___x_397_);
    return v_res_399_;
}
pub unsafe fn _init_l_Std_Http_Body_Empty_recvSelector___closed__0() -> *mut leanh::LeanObject
{
    let mut v___x_400_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_400_ = l_Std_Async_EAsync_instMonad(leanh::lean_box(0));
    return v___x_400_;
}
pub unsafe fn _init_l_Std_Http_Body_Empty_recvSelector___closed__1() -> *mut leanh::LeanObject
{
    let mut v___x_401_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_401_ = l_Std_Async_EAsync_instMonadLiftBaseAsync(leanh::lean_box(0));
    return v___x_401_;
}
pub unsafe fn _init_l_Std_Http_Body_Empty_recvSelector___closed__7() -> *mut leanh::LeanObject
{
    let mut v___x_411_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_412_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_413_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_411_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Http_Body_Empty_recvSelector___closed__1),
        core::ptr::addr_of_mut!(l_Std_Http_Body_Empty_recvSelector___closed__1_once),
        _init_l_Std_Http_Body_Empty_recvSelector___closed__1,
    );
    v___f_412_ = l_Std_Http_Body_Empty_recvSelector___closed__6;
    v___f_413_ = leanh::lean_alloc_closure(
        l_instMonadLiftTOfMonadLift___redArg___lam__0 as *mut core::ffi::c_void,
        4,
        2,
    );
    leanh::lean_closure_set(v___f_413_, 0, v___f_412_);
    leanh::lean_closure_set(v___f_413_, 1, v___x_411_);
    return v___f_413_;
}
pub unsafe fn _init_l_Std_Http_Body_Empty_recvSelector___closed__9() -> *mut leanh::LeanObject
{
    let mut v_win_416_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_417_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_418_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_419_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_win_416_ = l_Std_Http_Body_Empty_recvSelector___closed__8;
    v___f_417_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Http_Body_Empty_recvSelector___closed__7),
        core::ptr::addr_of_mut!(l_Std_Http_Body_Empty_recvSelector___closed__7_once),
        _init_l_Std_Http_Body_Empty_recvSelector___closed__7,
    );
    v___x_418_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Http_Body_Empty_recvSelector___closed__0),
        core::ptr::addr_of_mut!(l_Std_Http_Body_Empty_recvSelector___closed__0_once),
        _init_l_Std_Http_Body_Empty_recvSelector___closed__0,
    );
    v___f_419_ = leanh::lean_alloc_closure(
        l_Std_Http_Body_Empty_recvSelector___lam__2___boxed as *mut core::ffi::c_void,
        5,
        3,
    );
    leanh::lean_closure_set(v___f_419_, 0, v___x_418_);
    leanh::lean_closure_set(v___f_419_, 1, v___f_417_);
    leanh::lean_closure_set(v___f_419_, 2, v_win_416_);
    return v___f_419_;
}
pub unsafe fn _init_l_Std_Http_Body_Empty_recvSelector___closed__11()
-> *mut leanh::LeanObject {
    let mut v___f_422_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_423_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_424_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_425_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_422_ = l_Std_Http_Body_Empty_recvSelector___lam__2___closed__0;
    v___f_423_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Http_Body_Empty_recvSelector___closed__9),
        core::ptr::addr_of_mut!(l_Std_Http_Body_Empty_recvSelector___closed__9_once),
        _init_l_Std_Http_Body_Empty_recvSelector___closed__9,
    );
    v___f_424_ = l_Std_Http_Body_Empty_recvSelector___closed__10;
    v___x_425_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
    leanh::lean_ctor_set(v___x_425_, 0, v___f_424_);
    leanh::lean_ctor_set(v___x_425_, 1, v___f_423_);
    leanh::lean_ctor_set(v___x_425_, 2, v___f_422_);
    return v___x_425_;
}
pub unsafe fn l_Std_Http_Body_Empty_recvSelector(
    mut v_x_426_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_427_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_427_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Http_Body_Empty_recvSelector___closed__11),
        core::ptr::addr_of_mut!(l_Std_Http_Body_Empty_recvSelector___closed__11_once),
        _init_l_Std_Http_Body_Empty_recvSelector___closed__11,
    );
    return v___x_427_;
}
pub unsafe fn l_Std_Http_Body_instEmpty___lam__0(
    mut v_x_436_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_438_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_438_ = l_Std_Http_Body_instEmpty___lam__0___closed__3;
    return v___x_438_;
}
pub unsafe fn l_Std_Http_Body_instEmpty___lam__0___boxed(
    mut v_x_439_: *mut leanh::LeanObject,
    mut v___y_440_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_441_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_441_ = l_Std_Http_Body_instEmpty___lam__0(v_x_439_);
    return v_res_441_;
}
pub unsafe fn l_Std_Http_Body_instEmpty___lam__1(
    mut v_x_442_: *mut leanh::LeanObject,
    mut v_x_443_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_445_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_445_ = l_Std_Http_Body_Empty_close___redArg___closed__1;
    return v___x_445_;
}
pub unsafe fn l_Std_Http_Body_instEmpty___lam__1___boxed(
    mut v_x_446_: *mut leanh::LeanObject,
    mut v_x_447_: *mut leanh::LeanObject,
    mut v___y_448_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_449_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_449_ = l_Std_Http_Body_instEmpty___lam__1(v_x_446_, v_x_447_);
    leanh::lean_dec(v_x_447_);
    return v_res_449_;
}
pub unsafe fn l_Std_Http_Body_instCoeResponseEmptyAny___lam__0(
    mut v___x_469_: *mut leanh::LeanObject,
    mut v_f_470_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_line_471_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_body_472_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_extensions_473_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_475_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_476_: u8 = 0;
    let mut v___x_477_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_479_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_480_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_481_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_line_471_ = leanh::lean_ctor_get(v_f_470_, 0);
                v_body_472_ = leanh::lean_ctor_get(v_f_470_, 1);
                v_extensions_473_ = leanh::lean_ctor_get(v_f_470_, 2);
                v_isSharedCheck_481_ = (!leanh::lean_is_exclusive(v_f_470_)) as u8;
                if v_isSharedCheck_481_ == 0 {
                    v___x_475_ = v_f_470_;
                    v_isShared_476_ = v_isSharedCheck_481_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_extensions_473_);
                    leanh::lean_inc(v_body_472_);
                    leanh::lean_inc(v_line_471_);
                    leanh::lean_dec(v_f_470_);
                    v___x_475_ = leanh::lean_box(0);
                    v_isShared_476_ = v_isSharedCheck_481_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_477_ = l_Std_Http_Body_Any_ofBody___redArg(v___x_469_, v_body_472_);
                if v_isShared_476_ == 0 {
                    leanh::lean_ctor_set(v___x_475_, 1, v___x_477_);
                    v___x_479_ = v___x_475_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_480_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_480_, 0, v_line_471_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_480_, 1, v___x_477_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_480_, 2, v_extensions_473_);
                    v___x_479_ = v_reuseFailAlloc_480_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_479_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Http_Body_instCoeContextAsyncResponseEmptyAny___lam__0(
    mut v___x_485_: *mut leanh::LeanObject,
    mut v_x_486_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_a_488_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_490_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_491_: u8 = 0;
    let mut v___x_493_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_494_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_495_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_496_: u8 = 0;
    let mut v_a_497_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_499_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_500_: u8 = 0;
    let mut v_line_501_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_body_502_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_extensions_503_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_505_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_506_: u8 = 0;
    let mut v___x_507_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_509_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_511_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_512_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_513_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_514_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_515_: u8 = 0;
    let mut v_isSharedCheck_516_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_486_) == 0 {
                    leanh::lean_dec_ref(v___x_485_);
                    v_a_488_ = leanh::lean_ctor_get(v_x_486_, 0);
                    v_isSharedCheck_496_ = (!leanh::lean_is_exclusive(v_x_486_)) as u8;
                    if v_isSharedCheck_496_ == 0 {
                        v___x_490_ = v_x_486_;
                        v_isShared_491_ = v_isSharedCheck_496_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_488_);
                        leanh::lean_dec(v_x_486_);
                        v___x_490_ = leanh::lean_box(0);
                        v_isShared_491_ = v_isSharedCheck_496_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_497_ = leanh::lean_ctor_get(v_x_486_, 0);
                    v_isSharedCheck_516_ = (!leanh::lean_is_exclusive(v_x_486_)) as u8;
                    if v_isSharedCheck_516_ == 0 {
                        v___x_499_ = v_x_486_;
                        v_isShared_500_ = v_isSharedCheck_516_;
                        state = 3;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_497_);
                        leanh::lean_dec(v_x_486_);
                        v___x_499_ = leanh::lean_box(0);
                        v_isShared_500_ = v_isSharedCheck_516_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_491_ == 0 {
                    v___x_493_ = v___x_490_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_495_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_495_, 0, v_a_488_);
                    v___x_493_ = v_reuseFailAlloc_495_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_494_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_494_, 0, v___x_493_);
                return v___x_494_;
            }
            3 => {
                v_line_501_ = leanh::lean_ctor_get(v_a_497_, 0);
                v_body_502_ = leanh::lean_ctor_get(v_a_497_, 1);
                v_extensions_503_ = leanh::lean_ctor_get(v_a_497_, 2);
                v_isSharedCheck_515_ = (!leanh::lean_is_exclusive(v_a_497_)) as u8;
                if v_isSharedCheck_515_ == 0 {
                    v___x_505_ = v_a_497_;
                    v_isShared_506_ = v_isSharedCheck_515_;
                    state = 4;
                    continue;
                } else {
                    leanh::lean_inc(v_extensions_503_);
                    leanh::lean_inc(v_body_502_);
                    leanh::lean_inc(v_line_501_);
                    leanh::lean_dec(v_a_497_);
                    v___x_505_ = leanh::lean_box(0);
                    v_isShared_506_ = v_isSharedCheck_515_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_507_ = l_Std_Http_Body_Any_ofBody___redArg(v___x_485_, v_body_502_);
                if v_isShared_506_ == 0 {
                    leanh::lean_ctor_set(v___x_505_, 1, v___x_507_);
                    v___x_509_ = v___x_505_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_514_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_514_, 0, v_line_501_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_514_, 1, v___x_507_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_514_, 2, v_extensions_503_);
                    v___x_509_ = v_reuseFailAlloc_514_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                if v_isShared_500_ == 0 {
                    leanh::lean_ctor_set(v___x_499_, 0, v___x_509_);
                    v___x_511_ = v___x_499_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_513_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_513_, 0, v___x_509_);
                    v___x_511_ = v_reuseFailAlloc_513_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                v___x_512_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_512_, 0, v___x_511_);
                return v___x_512_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Http_Body_instCoeContextAsyncResponseEmptyAny___lam__0___boxed(
    mut v___x_517_: *mut leanh::LeanObject,
    mut v_x_518_: *mut leanh::LeanObject,
    mut v___y_519_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_520_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_520_ = l_Std_Http_Body_instCoeContextAsyncResponseEmptyAny___lam__0(v___x_517_, v_x_518_);
    return v_res_520_;
}
pub unsafe fn l_Std_Http_Body_instCoeContextAsyncResponseEmptyAny___lam__1(
    mut v___f_521_: *mut leanh::LeanObject,
    mut v_action_522_: *mut leanh::LeanObject,
    mut v___y_523_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_525_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_526_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_527_: u8 = 0;
    let mut v___x_528_: *mut leanh::LeanObject = core::ptr::null_mut();
    leanh::lean_inc_ref(v___y_523_);
    v___x_525_ = leanh::lean_apply_2(v_action_522_, v___y_523_, leanh::lean_box(0));
    v___x_526_ = leanh::lean_unsigned_to_nat(0);
    v___x_527_ = 0;
    v___x_528_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(
        leanh::lean_box(0),
        leanh::lean_box(0),
        v___x_526_,
        v___x_527_,
        v___x_525_,
        v___f_521_,
    );
    return v___x_528_;
}
pub unsafe fn l_Std_Http_Body_instCoeContextAsyncResponseEmptyAny___lam__1___boxed(
    mut v___f_529_: *mut leanh::LeanObject,
    mut v_action_530_: *mut leanh::LeanObject,
    mut v___y_531_: *mut leanh::LeanObject,
    mut v___y_532_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_533_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_533_ = l_Std_Http_Body_instCoeContextAsyncResponseEmptyAny___lam__1(
        v___f_529_,
        v_action_530_,
        v___y_531_,
    );
    leanh::lean_dec_ref(v___y_531_);
    return v_res_533_;
}
pub unsafe fn l_Std_Http_Body_instCoeAsyncResponseEmptyContextAsyncAny___lam__1(
    mut v___f_539_: *mut leanh::LeanObject,
    mut v_action_540_: *mut leanh::LeanObject,
    mut v___y_541_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_543_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_544_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_545_: u8 = 0;
    let mut v___x_546_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_543_ = leanh::lean_apply_1(v_action_540_, leanh::lean_box(0));
    v___x_544_ = leanh::lean_unsigned_to_nat(0);
    v___x_545_ = 0;
    v___x_546_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(
        leanh::lean_box(0),
        leanh::lean_box(0),
        v___x_544_,
        v___x_545_,
        v___x_543_,
        v___f_539_,
    );
    return v___x_546_;
}
pub unsafe fn l_Std_Http_Body_instCoeAsyncResponseEmptyContextAsyncAny___lam__1___boxed(
    mut v___f_547_: *mut leanh::LeanObject,
    mut v_action_548_: *mut leanh::LeanObject,
    mut v___y_549_: *mut leanh::LeanObject,
    mut v___y_550_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_551_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_551_ = l_Std_Http_Body_instCoeAsyncResponseEmptyContextAsyncAny___lam__1(
        v___f_547_,
        v_action_548_,
        v___y_549_,
    );
    leanh::lean_dec_ref(v___y_549_);
    return v_res_551_;
}
pub unsafe fn l_Std_Http_Request_Builder_empty(
    mut v_builder_555_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_557_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_558_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_559_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_560_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_557_ = leanh::lean_box(0);
    v___x_558_ = l_Std_Http_Request_Builder_body___redArg(v_builder_555_, v___x_557_);
    v___x_559_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_559_, 0, v___x_558_);
    v___x_560_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_560_, 0, v___x_559_);
    return v___x_560_;
}
pub unsafe fn l_Std_Http_Request_Builder_empty___boxed(
    mut v_builder_561_: *mut leanh::LeanObject,
    mut v_a_562_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_563_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_563_ = l_Std_Http_Request_Builder_empty(v_builder_561_);
    leanh::lean_dec_ref(v_builder_561_);
    return v_res_563_;
}
pub unsafe fn l_Std_Http_Response_Builder_empty(
    mut v_builder_564_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_566_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_567_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_568_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_569_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_566_ = leanh::lean_box(0);
    v___x_567_ = l_Std_Http_Response_Builder_body___redArg(v_builder_564_, v___x_566_);
    v___x_568_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_568_, 0, v___x_567_);
    v___x_569_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_569_, 0, v___x_568_);
    return v___x_569_;
}
pub unsafe fn l_Std_Http_Response_Builder_empty___boxed(
    mut v_builder_570_: *mut leanh::LeanObject,
    mut v_a_571_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_572_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_572_ = l_Std_Http_Response_Builder_empty(v_builder_570_);
    leanh::lean_dec_ref(v_builder_570_);
    return v_res_572_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Std_Http_Data_Body_Empty(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Std_Http_Data_Request(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Std_Http_Data_Response(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Std_Http_Data_Body_Any(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    l_Std_Http_Body_instInhabitedEmpty_default = _init_l_Std_Http_Body_instInhabitedEmpty_default();
    leanh::lean_mark_persistent(l_Std_Http_Body_instInhabitedEmpty_default);
    l_Std_Http_Body_instInhabitedEmpty = _init_l_Std_Http_Body_instInhabitedEmpty();
    leanh::lean_mark_persistent(l_Std_Http_Body_instInhabitedEmpty);
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Std_Http_Data_Body_Empty(
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
pub unsafe fn initialize_Std_Http_Data_Body_Empty(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Std_Http_Data_Request(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Std_Http_Data_Response(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Std_Http_Data_Body_Any(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Std_Http_Data_Body_Empty(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = meta_initialize_Std_Http_Data_Body_Empty(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return initialize_Std_Http_Data_Body_Empty(builtin);
}