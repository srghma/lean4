// Lean compiler output
// Module: Std.Http.Data.Body.Empty
// Imports: Std.Http.Data.Request Std.Http.Data.Response Std.Http.Data.Body.Any
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
use crate::lean_imports_rs::Init::System::Promise::lean_io_promise_resolve;
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_alloc_closure, lean_alloc_ctor, lean_apply_1,
    lean_apply_2, lean_box, lean_closure_set, lean_ctor_get, lean_ctor_set, lean_dec, lean_dec_ref,
    lean_inc, lean_inc_ref, lean_io_result_is_error, lean_io_result_mk_ok, lean_is_exclusive,
    lean_mark_persistent, lean_obj_once, lean_obj_tag, lean_unsigned_to_nat,
};
pub static mut l_Std_Http_Body_instInhabitedEmpty_default: *mut LeanObject = core::ptr::null_mut();
pub static mut l_Std_Http_Body_instInhabitedEmpty: *mut LeanObject = core::ptr::null_mut();
pub static l_Std_Http_Body_instBEqEmpty___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_Std_Http_Body_instBEqEmpty_beq___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Std_Http_Body_instBEqEmpty___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Http_Body_instBEqEmpty___closed__0_value) as *mut LeanObject;
pub static mut l_Std_Http_Body_instBEqEmpty: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Http_Body_instBEqEmpty___closed__0_value) as *mut LeanObject;
pub static l_Std_Http_Body_Empty_recv___redArg___closed__0_value: LeanCtorObject<1> =
    LeanCtorObject {
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
static mut l_Std_Http_Body_Empty_recv___redArg___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Http_Body_Empty_recv___redArg___closed__0_value) as *mut LeanObject;
pub static l_Std_Http_Body_Empty_recv___redArg___closed__1_value: LeanCtorObject<1> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 0,
        },
        m_objs: [
            core::ptr::addr_of!(l_Std_Http_Body_Empty_recv___redArg___closed__0_value)
                as *mut LeanObject,
        ],
    };
static mut l_Std_Http_Body_Empty_recv___redArg___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Http_Body_Empty_recv___redArg___closed__1_value) as *mut LeanObject;
pub static l_Std_Http_Body_Empty_close___redArg___closed__0_value: LeanCtorObject<1> =
    LeanCtorObject {
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
static mut l_Std_Http_Body_Empty_close___redArg___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Http_Body_Empty_close___redArg___closed__0_value) as *mut LeanObject;
pub static l_Std_Http_Body_Empty_close___redArg___closed__1_value: LeanCtorObject<1> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 0,
        },
        m_objs: [
            core::ptr::addr_of!(l_Std_Http_Body_Empty_close___redArg___closed__0_value)
                as *mut LeanObject,
        ],
    };
static mut l_Std_Http_Body_Empty_close___redArg___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Http_Body_Empty_close___redArg___closed__1_value) as *mut LeanObject;
pub static l_Std_Http_Body_Empty_isClosed___redArg___closed__0_value: LeanCtorObject<1> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 1,
        },
        m_objs: [(((1 as usize) << 1) | 1) as *mut LeanObject],
    };
static mut l_Std_Http_Body_Empty_isClosed___redArg___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Http_Body_Empty_isClosed___redArg___closed__0_value)
        as *mut LeanObject;
pub static l_Std_Http_Body_Empty_isClosed___redArg___closed__1_value: LeanCtorObject<1> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 0,
        },
        m_objs: [
            core::ptr::addr_of!(l_Std_Http_Body_Empty_isClosed___redArg___closed__0_value)
                as *mut LeanObject,
        ],
    };
static mut l_Std_Http_Body_Empty_isClosed___redArg___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Http_Body_Empty_isClosed___redArg___closed__1_value)
        as *mut LeanObject;
pub static l_Std_Http_Body_Empty_tryRecv___redArg___closed__0_value: LeanCtorObject<1> =
    LeanCtorObject {
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
static mut l_Std_Http_Body_Empty_tryRecv___redArg___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Http_Body_Empty_tryRecv___redArg___closed__0_value)
        as *mut LeanObject;
pub static l_Std_Http_Body_Empty_tryRecv___redArg___closed__1_value: LeanCtorObject<1> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Std_Http_Body_Empty_tryRecv___redArg___closed__0_value)
                as *mut LeanObject,
        ],
    };
static mut l_Std_Http_Body_Empty_tryRecv___redArg___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Http_Body_Empty_tryRecv___redArg___closed__1_value)
        as *mut LeanObject;
pub static l_Std_Http_Body_Empty_tryRecv___redArg___closed__2_value: LeanCtorObject<1> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 0,
        },
        m_objs: [
            core::ptr::addr_of!(l_Std_Http_Body_Empty_tryRecv___redArg___closed__1_value)
                as *mut LeanObject,
        ],
    };
static mut l_Std_Http_Body_Empty_tryRecv___redArg___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Http_Body_Empty_tryRecv___redArg___closed__2_value)
        as *mut LeanObject;
pub static l_Std_Http_Body_Empty_recvSelector___lam__2___closed__0_value: LeanClosureObject<1> =
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
        m_fun: l_Std_Http_Body_Empty_recvSelector___lam__1___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 1,
        m_objs: [(((0 as usize) << 1) | 1) as *mut LeanObject],
    };
static mut l_Std_Http_Body_Empty_recvSelector___lam__2___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Http_Body_Empty_recvSelector___lam__2___closed__0_value)
        as *mut LeanObject;
static mut l_Std_Http_Body_Empty_recvSelector___closed__0_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_Http_Body_Empty_recvSelector___closed__0: *mut LeanObject = core::ptr::null_mut();
static mut l_Std_Http_Body_Empty_recvSelector___closed__1_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_Http_Body_Empty_recvSelector___closed__1: *mut LeanObject = core::ptr::null_mut();
pub static l_Std_Http_Body_Empty_recvSelector___closed__2_value: LeanClosureObject<0> =
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
        m_fun: l_Std_Async_BaseAsync_lift___boxed as *const core::ffi::c_void,
        m_arity: 3,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Std_Http_Body_Empty_recvSelector___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Http_Body_Empty_recvSelector___closed__2_value) as *mut LeanObject;
pub static l_Std_Http_Body_Empty_recvSelector___closed__3_value: LeanClosureObject<0> =
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
        m_fun: l_instMonadLiftT___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Std_Http_Body_Empty_recvSelector___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Http_Body_Empty_recvSelector___closed__3_value) as *mut LeanObject;
pub static l_Std_Http_Body_Empty_recvSelector___closed__4_value: LeanClosureObject<0> =
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
        m_fun: l_IO_instMonadLiftSTRealWorldBaseIO___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 3,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Std_Http_Body_Empty_recvSelector___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Http_Body_Empty_recvSelector___closed__4_value) as *mut LeanObject;
pub static l_Std_Http_Body_Empty_recvSelector___closed__5_value: LeanClosureObject<2> =
    LeanClosureObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut LeanObject>() * 2) as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_instMonadLiftTOfMonadLift___redArg___lam__0 as *const core::ffi::c_void,
        m_arity: 4,
        m_num_fixed: 2,
        m_objs: [
            core::ptr::addr_of!(l_Std_Http_Body_Empty_recvSelector___closed__3_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Std_Http_Body_Empty_recvSelector___closed__4_value)
                as *mut LeanObject,
        ],
    };
static mut l_Std_Http_Body_Empty_recvSelector___closed__5: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Http_Body_Empty_recvSelector___closed__5_value) as *mut LeanObject;
pub static l_Std_Http_Body_Empty_recvSelector___closed__6_value: LeanClosureObject<2> =
    LeanClosureObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut LeanObject>() * 2) as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_instMonadLiftTOfMonadLift___redArg___lam__0 as *const core::ffi::c_void,
        m_arity: 4,
        m_num_fixed: 2,
        m_objs: [
            core::ptr::addr_of!(l_Std_Http_Body_Empty_recvSelector___closed__5_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Std_Http_Body_Empty_recvSelector___closed__2_value)
                as *mut LeanObject,
        ],
    };
static mut l_Std_Http_Body_Empty_recvSelector___closed__6: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Http_Body_Empty_recvSelector___closed__6_value) as *mut LeanObject;
static mut l_Std_Http_Body_Empty_recvSelector___closed__7_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_Http_Body_Empty_recvSelector___closed__7: *mut LeanObject = core::ptr::null_mut();
pub static l_Std_Http_Body_Empty_recvSelector___closed__8_value: LeanClosureObject<1> =
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
        m_fun: l_Std_Http_Body_Empty_recvSelector___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 3,
        m_num_fixed: 1,
        m_objs: [(((0 as usize) << 1) | 1) as *mut LeanObject],
    };
static mut l_Std_Http_Body_Empty_recvSelector___closed__8: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Http_Body_Empty_recvSelector___closed__8_value) as *mut LeanObject;
static mut l_Std_Http_Body_Empty_recvSelector___closed__9_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_Http_Body_Empty_recvSelector___closed__9: *mut LeanObject = core::ptr::null_mut();
pub static l_Std_Http_Body_Empty_recvSelector___closed__10_value: LeanClosureObject<1> =
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
        m_fun: l_Std_Http_Body_Empty_recvSelector___lam__3___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 1,
        m_objs: [
            core::ptr::addr_of!(l_Std_Http_Body_Empty_tryRecv___redArg___closed__0_value)
                as *mut LeanObject,
        ],
    };
static mut l_Std_Http_Body_Empty_recvSelector___closed__10: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Http_Body_Empty_recvSelector___closed__10_value) as *mut LeanObject;
static mut l_Std_Http_Body_Empty_recvSelector___closed__11_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_Http_Body_Empty_recvSelector___closed__11: *mut LeanObject = core::ptr::null_mut();
pub static l_Std_Http_Body_instEmpty___lam__0___closed__0_value: LeanCtorObject<1> =
    LeanCtorObject {
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
static mut l_Std_Http_Body_instEmpty___lam__0___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Http_Body_instEmpty___lam__0___closed__0_value) as *mut LeanObject;
pub static l_Std_Http_Body_instEmpty___lam__0___closed__1_value: LeanCtorObject<1> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Std_Http_Body_instEmpty___lam__0___closed__0_value)
                as *mut LeanObject,
        ],
    };
static mut l_Std_Http_Body_instEmpty___lam__0___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Http_Body_instEmpty___lam__0___closed__1_value) as *mut LeanObject;
pub static l_Std_Http_Body_instEmpty___lam__0___closed__2_value: LeanCtorObject<1> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Std_Http_Body_instEmpty___lam__0___closed__1_value)
                as *mut LeanObject,
        ],
    };
static mut l_Std_Http_Body_instEmpty___lam__0___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Http_Body_instEmpty___lam__0___closed__2_value) as *mut LeanObject;
pub static l_Std_Http_Body_instEmpty___lam__0___closed__3_value: LeanCtorObject<1> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 0,
        },
        m_objs: [
            core::ptr::addr_of!(l_Std_Http_Body_instEmpty___lam__0___closed__2_value)
                as *mut LeanObject,
        ],
    };
static mut l_Std_Http_Body_instEmpty___lam__0___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Http_Body_instEmpty___lam__0___closed__3_value) as *mut LeanObject;
pub static l_Std_Http_Body_instEmpty___closed__0_value: LeanClosureObject<0> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Std_Http_Body_instEmpty___lam__0___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_Http_Body_instEmpty___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Http_Body_instEmpty___closed__0_value) as *mut LeanObject;
pub static l_Std_Http_Body_instEmpty___closed__1_value: LeanClosureObject<0> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Std_Http_Body_instEmpty___lam__1___boxed as *const core::ffi::c_void,
    m_arity: 3,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_Http_Body_instEmpty___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Http_Body_instEmpty___closed__1_value) as *mut LeanObject;
pub static l_Std_Http_Body_instEmpty___closed__2_value: LeanClosureObject<0> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Std_Http_Body_Empty_recv___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_Http_Body_instEmpty___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Http_Body_instEmpty___closed__2_value) as *mut LeanObject;
pub static l_Std_Http_Body_instEmpty___closed__3_value: LeanClosureObject<0> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Std_Http_Body_Empty_close___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_Http_Body_instEmpty___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Http_Body_instEmpty___closed__3_value) as *mut LeanObject;
pub static l_Std_Http_Body_instEmpty___closed__4_value: LeanClosureObject<0> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Std_Http_Body_Empty_isClosed___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_Http_Body_instEmpty___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Http_Body_instEmpty___closed__4_value) as *mut LeanObject;
pub static l_Std_Http_Body_instEmpty___closed__5_value: LeanClosureObject<0> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Std_Http_Body_Empty_recvSelector as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_Http_Body_instEmpty___closed__5: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Http_Body_instEmpty___closed__5_value) as *mut LeanObject;
pub static l_Std_Http_Body_instEmpty___closed__6_value: LeanClosureObject<0> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Std_Http_Body_Empty_tryRecv___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_Http_Body_instEmpty___closed__6: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Http_Body_instEmpty___closed__6_value) as *mut LeanObject;
pub static l_Std_Http_Body_instEmpty___closed__7_value: LeanCtorObject<7> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 7
            + 0) as u16,
        other: 7,
        tag: 0,
    },
    m_objs: [
        core::ptr::addr_of!(l_Std_Http_Body_instEmpty___closed__2_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Std_Http_Body_instEmpty___closed__3_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Std_Http_Body_instEmpty___closed__4_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Std_Http_Body_instEmpty___closed__5_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Std_Http_Body_instEmpty___closed__6_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Std_Http_Body_instEmpty___closed__0_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Std_Http_Body_instEmpty___closed__1_value) as *mut LeanObject,
    ],
};
static mut l_Std_Http_Body_instEmpty___closed__7: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Http_Body_instEmpty___closed__7_value) as *mut LeanObject;
pub static mut l_Std_Http_Body_instEmpty: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Http_Body_instEmpty___closed__7_value) as *mut LeanObject;
pub static l_Std_Http_Body_instCoeEmptyAny___closed__0_value: LeanClosureObject<2> =
    LeanClosureObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut LeanObject>() * 2) as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Std_Http_Body_Any_ofBody as *const core::ffi::c_void,
        m_arity: 3,
        m_num_fixed: 2,
        m_objs: [
            (((0 as usize) << 1) | 1) as *mut LeanObject,
            core::ptr::addr_of!(l_Std_Http_Body_instEmpty___closed__7_value) as *mut LeanObject,
        ],
    };
static mut l_Std_Http_Body_instCoeEmptyAny___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Http_Body_instCoeEmptyAny___closed__0_value) as *mut LeanObject;
pub static mut l_Std_Http_Body_instCoeEmptyAny: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Http_Body_instCoeEmptyAny___closed__0_value) as *mut LeanObject;
pub static l_Std_Http_Body_instCoeResponseEmptyAny___closed__0_value: LeanClosureObject<1> =
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
        m_fun: l_Std_Http_Body_instCoeResponseEmptyAny___lam__0 as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 1,
        m_objs: [
            core::ptr::addr_of!(l_Std_Http_Body_instEmpty___closed__7_value) as *mut LeanObject,
        ],
    };
static mut l_Std_Http_Body_instCoeResponseEmptyAny___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Http_Body_instCoeResponseEmptyAny___closed__0_value)
        as *mut LeanObject;
pub static mut l_Std_Http_Body_instCoeResponseEmptyAny: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Http_Body_instCoeResponseEmptyAny___closed__0_value)
        as *mut LeanObject;
pub static l_Std_Http_Body_instCoeContextAsyncResponseEmptyAny___closed__0_value:
    LeanClosureObject<1> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 1) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Std_Http_Body_instCoeContextAsyncResponseEmptyAny___lam__0___boxed
        as *const core::ffi::c_void,
    m_arity: 3,
    m_num_fixed: 1,
    m_objs: [core::ptr::addr_of!(l_Std_Http_Body_instEmpty___closed__7_value) as *mut LeanObject],
};
static mut l_Std_Http_Body_instCoeContextAsyncResponseEmptyAny___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Http_Body_instCoeContextAsyncResponseEmptyAny___closed__0_value)
        as *mut LeanObject;
pub static l_Std_Http_Body_instCoeContextAsyncResponseEmptyAny___closed__1_value:
    LeanClosureObject<1> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 1) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Std_Http_Body_instCoeContextAsyncResponseEmptyAny___lam__1___boxed
        as *const core::ffi::c_void,
    m_arity: 4,
    m_num_fixed: 1,
    m_objs: [core::ptr::addr_of!(
        l_Std_Http_Body_instCoeContextAsyncResponseEmptyAny___closed__0_value
    ) as *mut LeanObject],
};
static mut l_Std_Http_Body_instCoeContextAsyncResponseEmptyAny___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Http_Body_instCoeContextAsyncResponseEmptyAny___closed__1_value)
        as *mut LeanObject;
pub static mut l_Std_Http_Body_instCoeContextAsyncResponseEmptyAny: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Http_Body_instCoeContextAsyncResponseEmptyAny___closed__1_value)
        as *mut LeanObject;
pub static l_Std_Http_Body_instCoeAsyncResponseEmptyContextAsyncAny___closed__0_value:
    LeanClosureObject<1> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 1) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Std_Http_Body_instCoeAsyncResponseEmptyContextAsyncAny___lam__1___boxed
        as *const core::ffi::c_void,
    m_arity: 4,
    m_num_fixed: 1,
    m_objs: [core::ptr::addr_of!(
        l_Std_Http_Body_instCoeContextAsyncResponseEmptyAny___closed__0_value
    ) as *mut LeanObject],
};
static mut l_Std_Http_Body_instCoeAsyncResponseEmptyContextAsyncAny___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Http_Body_instCoeAsyncResponseEmptyContextAsyncAny___closed__0_value)
        as *mut LeanObject;
pub static mut l_Std_Http_Body_instCoeAsyncResponseEmptyContextAsyncAny: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Http_Body_instCoeAsyncResponseEmptyContextAsyncAny___closed__0_value)
        as *mut LeanObject;
pub unsafe fn l_Std_Http_Body_Empty_toCtorIdx(mut v_x_287_: *mut LeanObject) -> *mut LeanObject {
    let mut v___x_288_: *mut LeanObject = core::ptr::null_mut();
    v___x_288_ = lean_unsigned_to_nat(0);
    return v___x_288_;
}
pub unsafe fn _init_l_Std_Http_Body_instInhabitedEmpty_default() -> *mut LeanObject {
    let mut v___x_289_: *mut LeanObject = core::ptr::null_mut();
    v___x_289_ = lean_box(0);
    return v___x_289_;
}
pub unsafe fn _init_l_Std_Http_Body_instInhabitedEmpty() -> *mut LeanObject {
    let mut v___x_290_: *mut LeanObject = core::ptr::null_mut();
    v___x_290_ = lean_box(0);
    return v___x_290_;
}
pub unsafe fn l_Std_Http_Body_instBEqEmpty_beq(
    mut v_x_291_: *mut LeanObject,
    mut v_y_292_: *mut LeanObject,
) -> u8 {
    let mut v___x_293_: u8 = 0;
    v___x_293_ = 1;
    return v___x_293_;
}
pub unsafe fn l_Std_Http_Body_instBEqEmpty_beq___boxed(
    mut v_x_294_: *mut LeanObject,
    mut v_y_295_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_296_: u8 = 0;
    let mut v_r_297_: *mut LeanObject = core::ptr::null_mut();
    v_res_296_ = l_Std_Http_Body_instBEqEmpty_beq(v_x_294_, v_y_295_);
    v_r_297_ = lean_box((v_res_296_) as usize);
    return v_r_297_;
}
pub unsafe fn l_Std_Http_Body_Empty_recv___redArg() -> *mut LeanObject {
    let mut v___x_305_: *mut LeanObject = core::ptr::null_mut();
    v___x_305_ = l_Std_Http_Body_Empty_recv___redArg___closed__1;
    return v___x_305_;
}
pub unsafe fn l_Std_Http_Body_Empty_recv___redArg___boxed(
    mut v_a_306_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_307_: *mut LeanObject = core::ptr::null_mut();
    v_res_307_ = l_Std_Http_Body_Empty_recv___redArg();
    return v_res_307_;
}
pub unsafe fn l_Std_Http_Body_Empty_recv(mut v_x_308_: *mut LeanObject) -> *mut LeanObject {
    let mut v___x_310_: *mut LeanObject = core::ptr::null_mut();
    v___x_310_ = l_Std_Http_Body_Empty_recv___redArg___closed__1;
    return v___x_310_;
}
pub unsafe fn l_Std_Http_Body_Empty_recv___boxed(
    mut v_x_311_: *mut LeanObject,
    mut v_a_312_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_313_: *mut LeanObject = core::ptr::null_mut();
    v_res_313_ = l_Std_Http_Body_Empty_recv(v_x_311_);
    return v_res_313_;
}
pub unsafe fn l_Std_Http_Body_Empty_close___redArg() -> *mut LeanObject {
    let mut v___x_319_: *mut LeanObject = core::ptr::null_mut();
    v___x_319_ = l_Std_Http_Body_Empty_close___redArg___closed__1;
    return v___x_319_;
}
pub unsafe fn l_Std_Http_Body_Empty_close___redArg___boxed(
    mut v_a_320_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_321_: *mut LeanObject = core::ptr::null_mut();
    v_res_321_ = l_Std_Http_Body_Empty_close___redArg();
    return v_res_321_;
}
pub unsafe fn l_Std_Http_Body_Empty_close(mut v_x_322_: *mut LeanObject) -> *mut LeanObject {
    let mut v___x_324_: *mut LeanObject = core::ptr::null_mut();
    v___x_324_ = l_Std_Http_Body_Empty_close___redArg___closed__1;
    return v___x_324_;
}
pub unsafe fn l_Std_Http_Body_Empty_close___boxed(
    mut v_x_325_: *mut LeanObject,
    mut v_a_326_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_327_: *mut LeanObject = core::ptr::null_mut();
    v_res_327_ = l_Std_Http_Body_Empty_close(v_x_325_);
    return v_res_327_;
}
pub unsafe fn l_Std_Http_Body_Empty_isClosed___redArg() -> *mut LeanObject {
    let mut v___x_334_: *mut LeanObject = core::ptr::null_mut();
    v___x_334_ = l_Std_Http_Body_Empty_isClosed___redArg___closed__1;
    return v___x_334_;
}
pub unsafe fn l_Std_Http_Body_Empty_isClosed___redArg___boxed(
    mut v_a_335_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_336_: *mut LeanObject = core::ptr::null_mut();
    v_res_336_ = l_Std_Http_Body_Empty_isClosed___redArg();
    return v_res_336_;
}
pub unsafe fn l_Std_Http_Body_Empty_isClosed(mut v_x_337_: *mut LeanObject) -> *mut LeanObject {
    let mut v___x_339_: *mut LeanObject = core::ptr::null_mut();
    v___x_339_ = l_Std_Http_Body_Empty_isClosed___redArg___closed__1;
    return v___x_339_;
}
pub unsafe fn l_Std_Http_Body_Empty_isClosed___boxed(
    mut v_x_340_: *mut LeanObject,
    mut v_a_341_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_342_: *mut LeanObject = core::ptr::null_mut();
    v_res_342_ = l_Std_Http_Body_Empty_isClosed(v_x_340_);
    return v_res_342_;
}
pub unsafe fn l_Std_Http_Body_Empty_tryRecv___redArg() -> *mut LeanObject {
    let mut v___x_350_: *mut LeanObject = core::ptr::null_mut();
    v___x_350_ = l_Std_Http_Body_Empty_tryRecv___redArg___closed__2;
    return v___x_350_;
}
pub unsafe fn l_Std_Http_Body_Empty_tryRecv___redArg___boxed(
    mut v_a_351_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_352_: *mut LeanObject = core::ptr::null_mut();
    v_res_352_ = l_Std_Http_Body_Empty_tryRecv___redArg();
    return v_res_352_;
}
pub unsafe fn l_Std_Http_Body_Empty_tryRecv(mut v_x_353_: *mut LeanObject) -> *mut LeanObject {
    let mut v___x_355_: *mut LeanObject = core::ptr::null_mut();
    v___x_355_ = l_Std_Http_Body_Empty_tryRecv___redArg___closed__2;
    return v___x_355_;
}
pub unsafe fn l_Std_Http_Body_Empty_tryRecv___boxed(
    mut v_x_356_: *mut LeanObject,
    mut v_a_357_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_358_: *mut LeanObject = core::ptr::null_mut();
    v_res_358_ = l_Std_Http_Body_Empty_tryRecv(v_x_356_);
    return v_res_358_;
}
pub unsafe fn l_Std_Http_Body_Empty_recvSelector___lam__0(
    mut v___x_359_: *mut LeanObject,
    mut v_promise_360_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_362_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_363_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_364_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_365_: *mut LeanObject = core::ptr::null_mut();
    v___x_362_ = lean_alloc_ctor(1, 1, (0) as u32);
    lean_ctor_set(v___x_362_, 0, v___x_359_);
    v___x_363_ = lean_io_promise_resolve(v___x_362_, v_promise_360_);
    v___x_364_ = lean_alloc_ctor(1, 1, (0) as u32);
    lean_ctor_set(v___x_364_, 0, v___x_363_);
    v___x_365_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_365_, 0, v___x_364_);
    return v___x_365_;
}
pub unsafe fn l_Std_Http_Body_Empty_recvSelector___lam__0___boxed(
    mut v___x_366_: *mut LeanObject,
    mut v_promise_367_: *mut LeanObject,
    mut v___y_368_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_369_: *mut LeanObject = core::ptr::null_mut();
    v_res_369_ = l_Std_Http_Body_Empty_recvSelector___lam__0(v___x_366_, v_promise_367_);
    lean_dec(v_promise_367_);
    return v_res_369_;
}
pub unsafe fn l_Std_Http_Body_Empty_recvSelector___lam__1(
    mut v___x_370_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_372_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_373_: *mut LeanObject = core::ptr::null_mut();
    v___x_372_ = lean_alloc_ctor(1, 1, (0) as u32);
    lean_ctor_set(v___x_372_, 0, v___x_370_);
    v___x_373_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_373_, 0, v___x_372_);
    return v___x_373_;
}
pub unsafe fn l_Std_Http_Body_Empty_recvSelector___lam__1___boxed(
    mut v___x_374_: *mut LeanObject,
    mut v___y_375_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_376_: *mut LeanObject = core::ptr::null_mut();
    v_res_376_ = l_Std_Http_Body_Empty_recvSelector___lam__1(v___x_374_);
    return v_res_376_;
}
pub unsafe fn l_Std_Http_Body_Empty_recvSelector___lam__2(
    mut v___x_379_: *mut LeanObject,
    mut v___f_380_: *mut LeanObject,
    mut v_win_381_: *mut LeanObject,
    mut v_waiter_382_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_lose_384_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_266__overap_385_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_386_: *mut LeanObject = core::ptr::null_mut();
    v_lose_384_ = l_Std_Http_Body_Empty_recvSelector___lam__2___closed__0;
    v___x_266__overap_385_ = l_Std_Async_Waiter_race___redArg(
        v___x_379_,
        v___f_380_,
        v_waiter_382_,
        v_lose_384_,
        v_win_381_,
    );
    v___x_386_ = lean_apply_1(v___x_266__overap_385_, lean_box(0));
    return v___x_386_;
}
pub unsafe fn l_Std_Http_Body_Empty_recvSelector___lam__2___boxed(
    mut v___x_387_: *mut LeanObject,
    mut v___f_388_: *mut LeanObject,
    mut v_win_389_: *mut LeanObject,
    mut v_waiter_390_: *mut LeanObject,
    mut v___y_391_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_392_: *mut LeanObject = core::ptr::null_mut();
    v_res_392_ = l_Std_Http_Body_Empty_recvSelector___lam__2(
        v___x_387_,
        v___f_388_,
        v_win_389_,
        v_waiter_390_,
    );
    return v_res_392_;
}
pub unsafe fn l_Std_Http_Body_Empty_recvSelector___lam__3(
    mut v___x_393_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_395_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_396_: *mut LeanObject = core::ptr::null_mut();
    v___x_395_ = lean_alloc_ctor(1, 1, (0) as u32);
    lean_ctor_set(v___x_395_, 0, v___x_393_);
    v___x_396_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_396_, 0, v___x_395_);
    return v___x_396_;
}
pub unsafe fn l_Std_Http_Body_Empty_recvSelector___lam__3___boxed(
    mut v___x_397_: *mut LeanObject,
    mut v___y_398_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_399_: *mut LeanObject = core::ptr::null_mut();
    v_res_399_ = l_Std_Http_Body_Empty_recvSelector___lam__3(v___x_397_);
    return v_res_399_;
}
pub unsafe fn _init_l_Std_Http_Body_Empty_recvSelector___closed__0() -> *mut LeanObject {
    let mut v___x_400_: *mut LeanObject = core::ptr::null_mut();
    v___x_400_ = l_Std_Async_EAsync_instMonad(lean_box(0));
    return v___x_400_;
}
pub unsafe fn _init_l_Std_Http_Body_Empty_recvSelector___closed__1() -> *mut LeanObject {
    let mut v___x_401_: *mut LeanObject = core::ptr::null_mut();
    v___x_401_ = l_Std_Async_EAsync_instMonadLiftBaseAsync(lean_box(0));
    return v___x_401_;
}
pub unsafe fn _init_l_Std_Http_Body_Empty_recvSelector___closed__7() -> *mut LeanObject {
    let mut v___x_411_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_412_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_413_: *mut LeanObject = core::ptr::null_mut();
    v___x_411_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Http_Body_Empty_recvSelector___closed__1),
        core::ptr::addr_of_mut!(l_Std_Http_Body_Empty_recvSelector___closed__1_once),
        _init_l_Std_Http_Body_Empty_recvSelector___closed__1,
    );
    v___f_412_ = l_Std_Http_Body_Empty_recvSelector___closed__6;
    v___f_413_ = lean_alloc_closure(
        l_instMonadLiftTOfMonadLift___redArg___lam__0 as *mut core::ffi::c_void,
        4,
        2,
    );
    lean_closure_set(v___f_413_, 0, v___f_412_);
    lean_closure_set(v___f_413_, 1, v___x_411_);
    return v___f_413_;
}
pub unsafe fn _init_l_Std_Http_Body_Empty_recvSelector___closed__9() -> *mut LeanObject {
    let mut v_win_416_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_417_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_418_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_419_: *mut LeanObject = core::ptr::null_mut();
    v_win_416_ = l_Std_Http_Body_Empty_recvSelector___closed__8;
    v___f_417_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Http_Body_Empty_recvSelector___closed__7),
        core::ptr::addr_of_mut!(l_Std_Http_Body_Empty_recvSelector___closed__7_once),
        _init_l_Std_Http_Body_Empty_recvSelector___closed__7,
    );
    v___x_418_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Http_Body_Empty_recvSelector___closed__0),
        core::ptr::addr_of_mut!(l_Std_Http_Body_Empty_recvSelector___closed__0_once),
        _init_l_Std_Http_Body_Empty_recvSelector___closed__0,
    );
    v___f_419_ = lean_alloc_closure(
        l_Std_Http_Body_Empty_recvSelector___lam__2___boxed as *mut core::ffi::c_void,
        5,
        3,
    );
    lean_closure_set(v___f_419_, 0, v___x_418_);
    lean_closure_set(v___f_419_, 1, v___f_417_);
    lean_closure_set(v___f_419_, 2, v_win_416_);
    return v___f_419_;
}
pub unsafe fn _init_l_Std_Http_Body_Empty_recvSelector___closed__11() -> *mut LeanObject {
    let mut v___f_422_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_423_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_424_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_425_: *mut LeanObject = core::ptr::null_mut();
    v___f_422_ = l_Std_Http_Body_Empty_recvSelector___lam__2___closed__0;
    v___f_423_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Http_Body_Empty_recvSelector___closed__9),
        core::ptr::addr_of_mut!(l_Std_Http_Body_Empty_recvSelector___closed__9_once),
        _init_l_Std_Http_Body_Empty_recvSelector___closed__9,
    );
    v___f_424_ = l_Std_Http_Body_Empty_recvSelector___closed__10;
    v___x_425_ = lean_alloc_ctor(0, 3, (0) as u32);
    lean_ctor_set(v___x_425_, 0, v___f_424_);
    lean_ctor_set(v___x_425_, 1, v___f_423_);
    lean_ctor_set(v___x_425_, 2, v___f_422_);
    return v___x_425_;
}
pub unsafe fn l_Std_Http_Body_Empty_recvSelector(mut v_x_426_: *mut LeanObject) -> *mut LeanObject {
    let mut v___x_427_: *mut LeanObject = core::ptr::null_mut();
    v___x_427_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Http_Body_Empty_recvSelector___closed__11),
        core::ptr::addr_of_mut!(l_Std_Http_Body_Empty_recvSelector___closed__11_once),
        _init_l_Std_Http_Body_Empty_recvSelector___closed__11,
    );
    return v___x_427_;
}
pub unsafe fn l_Std_Http_Body_instEmpty___lam__0(mut v_x_436_: *mut LeanObject) -> *mut LeanObject {
    let mut v___x_438_: *mut LeanObject = core::ptr::null_mut();
    v___x_438_ = l_Std_Http_Body_instEmpty___lam__0___closed__3;
    return v___x_438_;
}
pub unsafe fn l_Std_Http_Body_instEmpty___lam__0___boxed(
    mut v_x_439_: *mut LeanObject,
    mut v___y_440_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_441_: *mut LeanObject = core::ptr::null_mut();
    v_res_441_ = l_Std_Http_Body_instEmpty___lam__0(v_x_439_);
    return v_res_441_;
}
pub unsafe fn l_Std_Http_Body_instEmpty___lam__1(
    mut v_x_442_: *mut LeanObject,
    mut v_x_443_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_445_: *mut LeanObject = core::ptr::null_mut();
    v___x_445_ = l_Std_Http_Body_Empty_close___redArg___closed__1;
    return v___x_445_;
}
pub unsafe fn l_Std_Http_Body_instEmpty___lam__1___boxed(
    mut v_x_446_: *mut LeanObject,
    mut v_x_447_: *mut LeanObject,
    mut v___y_448_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_449_: *mut LeanObject = core::ptr::null_mut();
    v_res_449_ = l_Std_Http_Body_instEmpty___lam__1(v_x_446_, v_x_447_);
    lean_dec(v_x_447_);
    return v_res_449_;
}
pub unsafe fn l_Std_Http_Body_instCoeResponseEmptyAny___lam__0(
    mut v___x_469_: *mut LeanObject,
    mut v_f_470_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_line_471_: *mut LeanObject = core::ptr::null_mut();
    let mut v_body_472_: *mut LeanObject = core::ptr::null_mut();
    let mut v_extensions_473_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_475_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_476_: u8 = 0;
    let mut v___x_477_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_479_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_480_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_481_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_line_471_ = lean_ctor_get(v_f_470_, 0);
                v_body_472_ = lean_ctor_get(v_f_470_, 1);
                v_extensions_473_ = lean_ctor_get(v_f_470_, 2);
                v_isSharedCheck_481_ = (!lean_is_exclusive(v_f_470_)) as u8;
                if v_isSharedCheck_481_ == 0 {
                    v___x_475_ = v_f_470_;
                    v_isShared_476_ = v_isSharedCheck_481_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_extensions_473_);
                    lean_inc(v_body_472_);
                    lean_inc(v_line_471_);
                    lean_dec(v_f_470_);
                    v___x_475_ = lean_box(0);
                    v_isShared_476_ = v_isSharedCheck_481_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_477_ = l_Std_Http_Body_Any_ofBody___redArg(v___x_469_, v_body_472_);
                if v_isShared_476_ == 0 {
                    lean_ctor_set(v___x_475_, 1, v___x_477_);
                    v___x_479_ = v___x_475_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_480_ = lean_alloc_ctor(0, 3, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_480_, 0, v_line_471_);
                    lean_ctor_set(v_reuseFailAlloc_480_, 1, v___x_477_);
                    lean_ctor_set(v_reuseFailAlloc_480_, 2, v_extensions_473_);
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
    mut v___x_485_: *mut LeanObject,
    mut v_x_486_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_488_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_490_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_491_: u8 = 0;
    let mut v___x_493_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_494_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_495_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_496_: u8 = 0;
    let mut v_a_497_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_499_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_500_: u8 = 0;
    let mut v_line_501_: *mut LeanObject = core::ptr::null_mut();
    let mut v_body_502_: *mut LeanObject = core::ptr::null_mut();
    let mut v_extensions_503_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_505_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_506_: u8 = 0;
    let mut v___x_507_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_509_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_511_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_512_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_513_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_514_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_515_: u8 = 0;
    let mut v_isSharedCheck_516_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_486_) == 0 {
                    lean_dec_ref(v___x_485_);
                    v_a_488_ = lean_ctor_get(v_x_486_, 0);
                    v_isSharedCheck_496_ = (!lean_is_exclusive(v_x_486_)) as u8;
                    if v_isSharedCheck_496_ == 0 {
                        v___x_490_ = v_x_486_;
                        v_isShared_491_ = v_isSharedCheck_496_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_488_);
                        lean_dec(v_x_486_);
                        v___x_490_ = lean_box(0);
                        v_isShared_491_ = v_isSharedCheck_496_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_497_ = lean_ctor_get(v_x_486_, 0);
                    v_isSharedCheck_516_ = (!lean_is_exclusive(v_x_486_)) as u8;
                    if v_isSharedCheck_516_ == 0 {
                        v___x_499_ = v_x_486_;
                        v_isShared_500_ = v_isSharedCheck_516_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_497_);
                        lean_dec(v_x_486_);
                        v___x_499_ = lean_box(0);
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
                    v_reuseFailAlloc_495_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_495_, 0, v_a_488_);
                    v___x_493_ = v_reuseFailAlloc_495_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_494_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_494_, 0, v___x_493_);
                return v___x_494_;
            }
            3 => {
                v_line_501_ = lean_ctor_get(v_a_497_, 0);
                v_body_502_ = lean_ctor_get(v_a_497_, 1);
                v_extensions_503_ = lean_ctor_get(v_a_497_, 2);
                v_isSharedCheck_515_ = (!lean_is_exclusive(v_a_497_)) as u8;
                if v_isSharedCheck_515_ == 0 {
                    v___x_505_ = v_a_497_;
                    v_isShared_506_ = v_isSharedCheck_515_;
                    state = 4;
                    continue;
                } else {
                    lean_inc(v_extensions_503_);
                    lean_inc(v_body_502_);
                    lean_inc(v_line_501_);
                    lean_dec(v_a_497_);
                    v___x_505_ = lean_box(0);
                    v_isShared_506_ = v_isSharedCheck_515_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_507_ = l_Std_Http_Body_Any_ofBody___redArg(v___x_485_, v_body_502_);
                if v_isShared_506_ == 0 {
                    lean_ctor_set(v___x_505_, 1, v___x_507_);
                    v___x_509_ = v___x_505_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_514_ = lean_alloc_ctor(0, 3, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_514_, 0, v_line_501_);
                    lean_ctor_set(v_reuseFailAlloc_514_, 1, v___x_507_);
                    lean_ctor_set(v_reuseFailAlloc_514_, 2, v_extensions_503_);
                    v___x_509_ = v_reuseFailAlloc_514_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                if v_isShared_500_ == 0 {
                    lean_ctor_set(v___x_499_, 0, v___x_509_);
                    v___x_511_ = v___x_499_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_513_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_513_, 0, v___x_509_);
                    v___x_511_ = v_reuseFailAlloc_513_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                v___x_512_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_512_, 0, v___x_511_);
                return v___x_512_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Http_Body_instCoeContextAsyncResponseEmptyAny___lam__0___boxed(
    mut v___x_517_: *mut LeanObject,
    mut v_x_518_: *mut LeanObject,
    mut v___y_519_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_520_: *mut LeanObject = core::ptr::null_mut();
    v_res_520_ = l_Std_Http_Body_instCoeContextAsyncResponseEmptyAny___lam__0(v___x_517_, v_x_518_);
    return v_res_520_;
}
pub unsafe fn l_Std_Http_Body_instCoeContextAsyncResponseEmptyAny___lam__1(
    mut v___f_521_: *mut LeanObject,
    mut v_action_522_: *mut LeanObject,
    mut v___y_523_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_525_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_526_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_527_: u8 = 0;
    let mut v___x_528_: *mut LeanObject = core::ptr::null_mut();
    lean_inc_ref(v___y_523_);
    v___x_525_ = lean_apply_2(v_action_522_, v___y_523_, lean_box(0));
    v___x_526_ = lean_unsigned_to_nat(0);
    v___x_527_ = 0;
    v___x_528_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(
        lean_box(0),
        lean_box(0),
        v___x_526_,
        v___x_527_,
        v___x_525_,
        v___f_521_,
    );
    return v___x_528_;
}
pub unsafe fn l_Std_Http_Body_instCoeContextAsyncResponseEmptyAny___lam__1___boxed(
    mut v___f_529_: *mut LeanObject,
    mut v_action_530_: *mut LeanObject,
    mut v___y_531_: *mut LeanObject,
    mut v___y_532_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_533_: *mut LeanObject = core::ptr::null_mut();
    v_res_533_ = l_Std_Http_Body_instCoeContextAsyncResponseEmptyAny___lam__1(
        v___f_529_,
        v_action_530_,
        v___y_531_,
    );
    lean_dec_ref(v___y_531_);
    return v_res_533_;
}
pub unsafe fn l_Std_Http_Body_instCoeAsyncResponseEmptyContextAsyncAny___lam__1(
    mut v___f_539_: *mut LeanObject,
    mut v_action_540_: *mut LeanObject,
    mut v___y_541_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_543_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_544_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_545_: u8 = 0;
    let mut v___x_546_: *mut LeanObject = core::ptr::null_mut();
    v___x_543_ = lean_apply_1(v_action_540_, lean_box(0));
    v___x_544_ = lean_unsigned_to_nat(0);
    v___x_545_ = 0;
    v___x_546_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(
        lean_box(0),
        lean_box(0),
        v___x_544_,
        v___x_545_,
        v___x_543_,
        v___f_539_,
    );
    return v___x_546_;
}
pub unsafe fn l_Std_Http_Body_instCoeAsyncResponseEmptyContextAsyncAny___lam__1___boxed(
    mut v___f_547_: *mut LeanObject,
    mut v_action_548_: *mut LeanObject,
    mut v___y_549_: *mut LeanObject,
    mut v___y_550_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_551_: *mut LeanObject = core::ptr::null_mut();
    v_res_551_ = l_Std_Http_Body_instCoeAsyncResponseEmptyContextAsyncAny___lam__1(
        v___f_547_,
        v_action_548_,
        v___y_549_,
    );
    lean_dec_ref(v___y_549_);
    return v_res_551_;
}
pub unsafe fn l_Std_Http_Request_Builder_empty(
    mut v_builder_555_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_557_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_558_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_559_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_560_: *mut LeanObject = core::ptr::null_mut();
    v___x_557_ = lean_box(0);
    v___x_558_ = l_Std_Http_Request_Builder_body___redArg(v_builder_555_, v___x_557_);
    v___x_559_ = lean_alloc_ctor(1, 1, (0) as u32);
    lean_ctor_set(v___x_559_, 0, v___x_558_);
    v___x_560_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_560_, 0, v___x_559_);
    return v___x_560_;
}
pub unsafe fn l_Std_Http_Request_Builder_empty___boxed(
    mut v_builder_561_: *mut LeanObject,
    mut v_a_562_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_563_: *mut LeanObject = core::ptr::null_mut();
    v_res_563_ = l_Std_Http_Request_Builder_empty(v_builder_561_);
    lean_dec_ref(v_builder_561_);
    return v_res_563_;
}
pub unsafe fn l_Std_Http_Response_Builder_empty(
    mut v_builder_564_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_566_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_567_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_568_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_569_: *mut LeanObject = core::ptr::null_mut();
    v___x_566_ = lean_box(0);
    v___x_567_ = l_Std_Http_Response_Builder_body___redArg(v_builder_564_, v___x_566_);
    v___x_568_ = lean_alloc_ctor(1, 1, (0) as u32);
    lean_ctor_set(v___x_568_, 0, v___x_567_);
    v___x_569_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_569_, 0, v___x_568_);
    return v___x_569_;
}
pub unsafe fn l_Std_Http_Response_Builder_empty___boxed(
    mut v_builder_570_: *mut LeanObject,
    mut v_a_571_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_572_: *mut LeanObject = core::ptr::null_mut();
    v_res_572_ = l_Std_Http_Response_Builder_empty(v_builder_570_);
    lean_dec_ref(v_builder_570_);
    return v_res_572_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Std_Http_Data_Body_Empty(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Std_Http_Data_Request(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Std_Http_Data_Response(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Std_Http_Data_Body_Any(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    l_Std_Http_Body_instInhabitedEmpty_default = _init_l_Std_Http_Body_instInhabitedEmpty_default();
    lean_mark_persistent(l_Std_Http_Body_instInhabitedEmpty_default);
    l_Std_Http_Body_instInhabitedEmpty = _init_l_Std_Http_Body_instInhabitedEmpty();
    lean_mark_persistent(l_Std_Http_Body_instInhabitedEmpty);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Std_Http_Data_Body_Empty(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_meta_initialized = true;
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Std_Http_Data_Body_Empty(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Std_Http_Data_Request(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Std_Http_Data_Response(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Std_Http_Data_Body_Any(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Std_Http_Data_Body_Empty(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Std_Http_Data_Body_Empty(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Std_Http_Data_Body_Empty(builtin);
}
