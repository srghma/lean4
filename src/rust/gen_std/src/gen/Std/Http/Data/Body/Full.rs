// Lean compiler output
// Module: Std.Http.Data.Body.Full
// Imports: Std.Sync Std.Http.Data.Request Std.Http.Data.Response Std.Http.Data.Body.Any Init.Data.ByteArray
use crate::ffi::{
    lean_byte_array_size, lean_io_basemutex_lock, lean_io_basemutex_unlock,
    lean_io_promise_resolve, lean_st_ref_get, lean_st_ref_set, lean_st_ref_take,
    lean_string_to_utf8, lean_task_map,
};
use crate::r#gen::Init::Data::ByteArray::Basic::l_ByteArray_isEmpty;
use crate::r#gen::Init::Data::ByteArray::{
    initialize_Init_Data_ByteArray, runtime_initialize_Init_Data_ByteArray,
};
use crate::r#gen::Std::Async::Basic::{
    l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask,
    l_Std_Async_EAsync_tryFinally_x27___redArg,
};
use crate::r#gen::Std::Http::Data::Body::Any::{
    initialize_Std_Http_Data_Body_Any, l_Std_Http_Body_Any_ofBody,
    l_Std_Http_Body_Any_ofBody___redArg, runtime_initialize_Std_Http_Data_Body_Any,
};
use crate::r#gen::Std::Http::Data::Chunk::l_Std_Http_Chunk_ofByteArray;
use crate::r#gen::Std::Http::Data::Headers::Name::l_Std_Http_Header_Name_contentType;
use crate::r#gen::Std::Http::Data::Headers::Value::l_Std_Http_Header_Value_ofString_x21;
use crate::r#gen::Std::Http::Data::Request::{
    initialize_Std_Http_Data_Request, l_Std_Http_Request_Builder_body___redArg,
    l_Std_Http_Request_Builder_header, runtime_initialize_Std_Http_Data_Request,
};
use crate::r#gen::Std::Http::Data::Response::{
    initialize_Std_Http_Data_Response, l_Std_Http_Response_Builder_body___redArg,
    l_Std_Http_Response_Builder_header, runtime_initialize_Std_Http_Data_Response,
};
use crate::r#gen::Std::Sync::Mutex::l_Std_Mutex_new___redArg;
use crate::r#gen::Std::Sync::{initialize_Std_Sync, runtime_initialize_Std_Sync};
pub static l___private_Std_Http_Data_Body_Full_0__Std_Http_Body_Full_takeChunk___lam__0___closed__0_value: leanh::LeanCtorObject<1> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject] };
static mut l___private_Std_Http_Data_Body_Full_0__Std_Http_Body_Full_takeChunk___lam__0___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Std_Http_Data_Body_Full_0__Std_Http_Body_Full_takeChunk___lam__0___closed__0_value) as *mut leanh::LeanObject;
pub static l___private_Std_Http_Data_Body_Full_0__Std_Http_Body_Full_takeChunk___lam__0___closed__1_value: leanh::LeanCtorObject<1> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Std_Http_Data_Body_Full_0__Std_Http_Body_Full_takeChunk___lam__0___closed__0_value) as *mut leanh::LeanObject] };
static mut l___private_Std_Http_Data_Body_Full_0__Std_Http_Body_Full_takeChunk___lam__0___closed__1: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Std_Http_Data_Body_Full_0__Std_Http_Body_Full_takeChunk___lam__0___closed__1_value) as *mut leanh::LeanObject;
pub static l_Std_Http_Body_Full_ofByteArray___closed__0_value: leanh::LeanClosureObject<0> =
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
        m_fun: l_Std_Http_Body_Full_ofByteArray___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Std_Http_Body_Full_ofByteArray___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Body_Full_ofByteArray___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Std_Mutex_atomically___at___00Std_Http_Body_Full_recv_spec__0___redArg___closed__0_value: leanh::LeanClosureObject<0> = leanh::LeanClosureObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Std_Mutex_atomically___at___00Std_Http_Body_Full_recv_spec__0___redArg___lam__3 as *const core::ffi::c_void, m_arity: 1, m_num_fixed: 0, m_objs: [] };
static mut l_Std_Mutex_atomically___at___00Std_Http_Body_Full_recv_spec__0___redArg___closed__0:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Std_Mutex_atomically___at___00Std_Http_Body_Full_recv_spec__0___redArg___closed__0_value
) as *mut leanh::LeanObject;
pub static l_Std_Http_Body_Full_close___closed__0_value: leanh::LeanClosureObject<1> =
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
        m_fun: l_Std_Http_Body_Full_close___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 3,
        m_num_fixed: 1,
        m_objs: [(((0 as usize) << 1) | 1) as *mut leanh::LeanObject],
    };
static mut l_Std_Http_Body_Full_close___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Body_Full_close___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Std_Http_Body_Full_isClosed___closed__0_value: leanh::LeanClosureObject<0> =
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
        m_fun: l_Std_Http_Body_Full_isClosed___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Std_Http_Body_Full_isClosed___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Body_Full_isClosed___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Std_Http_Body_Full_isClosed___closed__1_value: leanh::LeanClosureObject<1> =
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
        m_fun: l_Std_Http_Body_Full_isClosed___lam__1___boxed as *const core::ffi::c_void,
        m_arity: 3,
        m_num_fixed: 1,
        m_objs: [
            core::ptr::addr_of!(l_Std_Http_Body_Full_isClosed___closed__0_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Std_Http_Body_Full_isClosed___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Body_Full_isClosed___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Std_Http_Body_Full_getKnownSize___lam__0___closed__0_value:
    leanh::LeanCtorObject<1> = leanh::LeanCtorObject {
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
static mut l_Std_Http_Body_Full_getKnownSize___lam__0___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Body_Full_getKnownSize___lam__0___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Std_Http_Body_Full_getKnownSize___lam__0___closed__1_value:
    leanh::LeanCtorObject<1> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Std_Http_Body_Full_getKnownSize___lam__0___closed__0_value)
            as *mut leanh::LeanObject,
    ],
};
static mut l_Std_Http_Body_Full_getKnownSize___lam__0___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Body_Full_getKnownSize___lam__0___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Std_Http_Body_Full_getKnownSize___lam__0___closed__2_value:
    leanh::LeanCtorObject<1> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Std_Http_Body_Full_getKnownSize___lam__0___closed__1_value)
            as *mut leanh::LeanObject,
    ],
};
static mut l_Std_Http_Body_Full_getKnownSize___lam__0___closed__2: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Body_Full_getKnownSize___lam__0___closed__2_value)
        as *mut leanh::LeanObject;
pub static l_Std_Http_Body_Full_getKnownSize___lam__0___closed__3_value:
    leanh::LeanCtorObject<1> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 0,
    },
    m_objs: [
        core::ptr::addr_of!(l_Std_Http_Body_Full_getKnownSize___lam__0___closed__2_value)
            as *mut leanh::LeanObject,
    ],
};
static mut l_Std_Http_Body_Full_getKnownSize___lam__0___closed__3: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Body_Full_getKnownSize___lam__0___closed__3_value)
        as *mut leanh::LeanObject;
pub static l_Std_Http_Body_Full_getKnownSize___closed__0_value: leanh::LeanClosureObject<0> =
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
        m_fun: l_Std_Http_Body_Full_getKnownSize___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Std_Http_Body_Full_getKnownSize___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Body_Full_getKnownSize___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Std_Http_Body_Full_getKnownSize___closed__1_value: leanh::LeanClosureObject<1> =
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
        m_fun: l_Std_Http_Body_Full_getKnownSize___lam__1___boxed as *const core::ffi::c_void,
        m_arity: 3,
        m_num_fixed: 1,
        m_objs: [
            core::ptr::addr_of!(l_Std_Http_Body_Full_getKnownSize___closed__0_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Std_Http_Body_Full_getKnownSize___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Body_Full_getKnownSize___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Std_Http_Body_Full_tryRecv___closed__0_value: leanh::LeanClosureObject<0> =
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
        m_fun: l_Std_Http_Body_Full_tryRecv___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Std_Http_Body_Full_tryRecv___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Body_Full_tryRecv___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Std_Http_Body_Full_recvSelector___lam__1___closed__0_value:
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
    m_fun: l_Std_Http_Body_Full_recvSelector___lam__0___boxed as *const core::ffi::c_void,
    m_arity: 3,
    m_num_fixed: 1,
    m_objs: [(((0 as usize) << 1) | 1) as *mut leanh::LeanObject],
};
static mut l_Std_Http_Body_Full_recvSelector___lam__1___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Body_Full_recvSelector___lam__1___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Std_Http_Body_Full_recvSelector___closed__0_value: leanh::LeanClosureObject<1> =
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
        m_fun: l_Std_Http_Body_Full_recvSelector___lam__2___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 1,
        m_objs: [(((0 as usize) << 1) | 1) as *mut leanh::LeanObject],
    };
static mut l_Std_Http_Body_Full_recvSelector___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Body_Full_recvSelector___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Std_Http_Body_instFull___lam__0___closed__0_value: leanh::LeanCtorObject<1> =
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
static mut l_Std_Http_Body_instFull___lam__0___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Body_instFull___lam__0___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Std_Http_Body_instFull___lam__0___closed__1_value: leanh::LeanCtorObject<1> =
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
            core::ptr::addr_of!(l_Std_Http_Body_instFull___lam__0___closed__0_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Std_Http_Body_instFull___lam__0___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Body_instFull___lam__0___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Std_Http_Body_instFull___closed__0_value: leanh::LeanClosureObject<0> =
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
        m_fun: l_Std_Http_Body_instFull___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 3,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Std_Http_Body_instFull___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Body_instFull___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Std_Http_Body_instFull___closed__1_value: leanh::LeanClosureObject<0> =
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
        m_fun: l_Std_Http_Body_Full_recv___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Std_Http_Body_instFull___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Body_instFull___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Std_Http_Body_instFull___closed__2_value: leanh::LeanClosureObject<0> =
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
        m_fun: l_Std_Http_Body_Full_close___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Std_Http_Body_instFull___closed__2: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Body_instFull___closed__2_value)
        as *mut leanh::LeanObject;
pub static l_Std_Http_Body_instFull___closed__3_value: leanh::LeanClosureObject<0> =
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
        m_fun: l_Std_Http_Body_Full_isClosed___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Std_Http_Body_instFull___closed__3: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Body_instFull___closed__3_value)
        as *mut leanh::LeanObject;
pub static l_Std_Http_Body_instFull___closed__4_value: leanh::LeanClosureObject<0> =
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
        m_fun: l_Std_Http_Body_Full_recvSelector as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Std_Http_Body_instFull___closed__4: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Body_instFull___closed__4_value)
        as *mut leanh::LeanObject;
pub static l_Std_Http_Body_instFull___closed__5_value: leanh::LeanClosureObject<0> =
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
        m_fun: l_Std_Http_Body_Full_tryRecv___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Std_Http_Body_instFull___closed__5: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Body_instFull___closed__5_value)
        as *mut leanh::LeanObject;
pub static l_Std_Http_Body_instFull___closed__6_value: leanh::LeanClosureObject<0> =
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
        m_fun: l_Std_Http_Body_Full_getKnownSize___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Std_Http_Body_instFull___closed__6: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Body_instFull___closed__6_value)
        as *mut leanh::LeanObject;
pub static l_Std_Http_Body_instFull___closed__7_value: leanh::LeanCtorObject<7> =
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
            core::ptr::addr_of!(l_Std_Http_Body_instFull___closed__1_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Std_Http_Body_instFull___closed__2_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Std_Http_Body_instFull___closed__3_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Std_Http_Body_instFull___closed__4_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Std_Http_Body_instFull___closed__5_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Std_Http_Body_instFull___closed__6_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Std_Http_Body_instFull___closed__0_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Std_Http_Body_instFull___closed__7: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Body_instFull___closed__7_value)
        as *mut leanh::LeanObject;
pub static mut l_Std_Http_Body_instFull: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Body_instFull___closed__7_value)
        as *mut leanh::LeanObject;
pub static l_Std_Http_Body_instCoeFullAny___closed__0_value: leanh::LeanClosureObject<2> =
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
            core::ptr::addr_of!(l_Std_Http_Body_instFull___closed__7_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Std_Http_Body_instCoeFullAny___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Body_instCoeFullAny___closed__0_value)
        as *mut leanh::LeanObject;
pub static mut l_Std_Http_Body_instCoeFullAny: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Body_instCoeFullAny___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Std_Http_Body_instCoeResponseFullAny___closed__0_value:
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
    m_fun: l_Std_Http_Body_instCoeResponseFullAny___lam__0 as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 1,
    m_objs: [
        core::ptr::addr_of!(l_Std_Http_Body_instFull___closed__7_value)
            as *mut leanh::LeanObject,
    ],
};
static mut l_Std_Http_Body_instCoeResponseFullAny___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Body_instCoeResponseFullAny___closed__0_value)
        as *mut leanh::LeanObject;
pub static mut l_Std_Http_Body_instCoeResponseFullAny: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Body_instCoeResponseFullAny___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Std_Http_Body_instCoeContextAsyncResponseFullAny___closed__0_value:
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
    m_fun: l_Std_Http_Body_instCoeContextAsyncResponseFullAny___lam__0___boxed
        as *const core::ffi::c_void,
    m_arity: 3,
    m_num_fixed: 1,
    m_objs: [
        core::ptr::addr_of!(l_Std_Http_Body_instFull___closed__7_value)
            as *mut leanh::LeanObject,
    ],
};
static mut l_Std_Http_Body_instCoeContextAsyncResponseFullAny___closed__0:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Body_instCoeContextAsyncResponseFullAny___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Std_Http_Body_instCoeContextAsyncResponseFullAny___closed__1_value:
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
    m_fun: l_Std_Http_Body_instCoeContextAsyncResponseFullAny___lam__1___boxed
        as *const core::ffi::c_void,
    m_arity: 4,
    m_num_fixed: 1,
    m_objs: [core::ptr::addr_of!(
        l_Std_Http_Body_instCoeContextAsyncResponseFullAny___closed__0_value
    ) as *mut leanh::LeanObject],
};
static mut l_Std_Http_Body_instCoeContextAsyncResponseFullAny___closed__1:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Body_instCoeContextAsyncResponseFullAny___closed__1_value)
        as *mut leanh::LeanObject;
pub static mut l_Std_Http_Body_instCoeContextAsyncResponseFullAny: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Body_instCoeContextAsyncResponseFullAny___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Std_Http_Body_instCoeAsyncResponseFullContextAsyncAny___closed__0_value:
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
    m_fun: l_Std_Http_Body_instCoeAsyncResponseFullContextAsyncAny___lam__1___boxed
        as *const core::ffi::c_void,
    m_arity: 4,
    m_num_fixed: 1,
    m_objs: [core::ptr::addr_of!(
        l_Std_Http_Body_instCoeContextAsyncResponseFullAny___closed__0_value
    ) as *mut leanh::LeanObject],
};
static mut l_Std_Http_Body_instCoeAsyncResponseFullContextAsyncAny___closed__0:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Body_instCoeAsyncResponseFullContextAsyncAny___closed__0_value)
        as *mut leanh::LeanObject;
pub static mut l_Std_Http_Body_instCoeAsyncResponseFullContextAsyncAny:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Body_instCoeAsyncResponseFullContextAsyncAny___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Std_Http_Request_Builder_bytes___closed__0_value: leanh::LeanStringObject<25> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 25,
        m_capacity: 25,
        m_length: 24,
        m_data: [
            97, 112, 112, 108, 105, 99, 97, 116, 105, 111, 110, 47, 111, 99, 116, 101, 116, 45,
            115, 116, 114, 101, 97, 109, 0,
        ],
    };
static mut l_Std_Http_Request_Builder_bytes___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Request_Builder_bytes___closed__0_value)
        as *mut leanh::LeanObject;
static mut l_Std_Http_Request_Builder_bytes___closed__1_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Http_Request_Builder_bytes___closed__1: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Std_Http_Request_Builder_text___closed__0_value: leanh::LeanStringObject<26> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 26,
        m_capacity: 26,
        m_length: 25,
        m_data: [
            116, 101, 120, 116, 47, 112, 108, 97, 105, 110, 59, 32, 99, 104, 97, 114, 115, 101,
            116, 61, 117, 116, 102, 45, 56, 0,
        ],
    };
static mut l_Std_Http_Request_Builder_text___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Request_Builder_text___closed__0_value)
        as *mut leanh::LeanObject;
static mut l_Std_Http_Request_Builder_text___closed__1_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Http_Request_Builder_text___closed__1: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Std_Http_Request_Builder_json___closed__0_value: leanh::LeanStringObject<17> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 17,
        m_capacity: 17,
        m_length: 16,
        m_data: [
            97, 112, 112, 108, 105, 99, 97, 116, 105, 111, 110, 47, 106, 115, 111, 110, 0,
        ],
    };
static mut l_Std_Http_Request_Builder_json___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Request_Builder_json___closed__0_value)
        as *mut leanh::LeanObject;
static mut l_Std_Http_Request_Builder_json___closed__1_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Http_Request_Builder_json___closed__1: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Std_Http_Request_Builder_html___closed__0_value: leanh::LeanStringObject<25> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 25,
        m_capacity: 25,
        m_length: 24,
        m_data: [
            116, 101, 120, 116, 47, 104, 116, 109, 108, 59, 32, 99, 104, 97, 114, 115, 101, 116,
            61, 117, 116, 102, 45, 56, 0,
        ],
    };
static mut l_Std_Http_Request_Builder_html___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Http_Request_Builder_html___closed__0_value)
        as *mut leanh::LeanObject;
static mut l_Std_Http_Request_Builder_html___closed__1_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Http_Request_Builder_html___closed__1: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub unsafe fn l___private_Std_Http_Data_Body_Full_0__Std_Http_Body_Full_takeChunk___lam__0(
    mut v_val_854_: *mut leanh::LeanObject,
    mut v_x_855_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_a_857_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_859_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_860_: u8 = 0;
    let mut v___x_862_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_863_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_864_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_865_: u8 = 0;
    let mut v___x_867_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_868_: u8 = 0;
    let mut v___x_869_: u8 = 0;
    let mut v___x_870_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_871_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_873_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_874_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_875_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_876_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_877_: u8 = 0;
    let mut v_unused_878_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_855_) == 0 {
                    leanh::lean_dec_ref(v_val_854_);
                    v_a_857_ = leanh::lean_ctor_get(v_x_855_, 0);
                    v_isSharedCheck_865_ = (!leanh::lean_is_exclusive(v_x_855_)) as u8;
                    if v_isSharedCheck_865_ == 0 {
                        v___x_859_ = v_x_855_;
                        v_isShared_860_ = v_isSharedCheck_865_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_857_);
                        leanh::lean_dec(v_x_855_);
                        v___x_859_ = leanh::lean_box(0);
                        v_isShared_860_ = v_isSharedCheck_865_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_isSharedCheck_877_ = (!leanh::lean_is_exclusive(v_x_855_)) as u8;
                    if v_isSharedCheck_877_ == 0 {
                        v_unused_878_ = leanh::lean_ctor_get(v_x_855_, 0);
                        leanh::lean_dec(v_unused_878_);
                        v___x_867_ = v_x_855_;
                        v_isShared_868_ = v_isSharedCheck_877_;
                        state = 3;
                        continue;
                    } else {
                        leanh::lean_dec(v_x_855_);
                        v___x_867_ = leanh::lean_box(0);
                        v_isShared_868_ = v_isSharedCheck_877_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_860_ == 0 {
                    v___x_862_ = v___x_859_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_864_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_864_, 0, v_a_857_);
                    v___x_862_ = v_reuseFailAlloc_864_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_863_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_863_, 0, v___x_862_);
                return v___x_863_;
            }
            3 => {
                v___x_869_ = l_ByteArray_isEmpty(v_val_854_);
                if v___x_869_ == 0 {
                    v___x_870_ = l_Std_Http_Chunk_ofByteArray(v_val_854_);
                    v___x_871_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_871_, 0, v___x_870_);
                    if v_isShared_868_ == 0 {
                        leanh::lean_ctor_set(v___x_867_, 0, v___x_871_);
                        v___x_873_ = v___x_867_;
                        state = 4;
                        continue;
                    } else {
                        v_reuseFailAlloc_875_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_875_, 0, v___x_871_);
                        v___x_873_ = v_reuseFailAlloc_875_;
                        state = 4;
                        continue;
                    }
                } else {
                    leanh::lean_del_object(v___x_867_);
                    leanh::lean_dec_ref(v_val_854_);
                    v___x_876_ = l___private_Std_Http_Data_Body_Full_0__Std_Http_Body_Full_takeChunk___lam__0___closed__1;
                    return v___x_876_;
                }
            }
            4 => {
                v___x_874_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_874_, 0, v___x_873_);
                return v___x_874_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Std_Http_Data_Body_Full_0__Std_Http_Body_Full_takeChunk___lam__0___boxed(
    mut v_val_879_: *mut leanh::LeanObject,
    mut v_x_880_: *mut leanh::LeanObject,
    mut v___y_881_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_882_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_882_ = l___private_Std_Http_Data_Body_Full_0__Std_Http_Body_Full_takeChunk___lam__0(
        v_val_879_, v_x_880_,
    );
    return v_res_882_;
}
pub unsafe fn l___private_Std_Http_Data_Body_Full_0__Std_Http_Body_Full_takeChunk___lam__1(
    mut v_a_883_: *mut leanh::LeanObject,
    mut v_x_884_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_a_886_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_888_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_889_: u8 = 0;
    let mut v___x_891_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_892_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_893_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_894_: u8 = 0;
    let mut v_a_895_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_897_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_898_: u8 = 0;
    let mut v___x_899_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_900_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_902_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_903_: u8 = 0;
    let mut v___x_904_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_905_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_906_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_908_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_910_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_911_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_912_: u8 = 0;
    let mut v___x_913_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_914_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_915_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_916_: u8 = 0;
    let mut v_isSharedCheck_917_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_884_) == 0 {
                    v_a_886_ = leanh::lean_ctor_get(v_x_884_, 0);
                    v_isSharedCheck_894_ = (!leanh::lean_is_exclusive(v_x_884_)) as u8;
                    if v_isSharedCheck_894_ == 0 {
                        v___x_888_ = v_x_884_;
                        v_isShared_889_ = v_isSharedCheck_894_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_886_);
                        leanh::lean_dec(v_x_884_);
                        v___x_888_ = leanh::lean_box(0);
                        v_isShared_889_ = v_isSharedCheck_894_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_895_ = leanh::lean_ctor_get(v_x_884_, 0);
                    v_isSharedCheck_917_ = (!leanh::lean_is_exclusive(v_x_884_)) as u8;
                    if v_isSharedCheck_917_ == 0 {
                        v___x_897_ = v_x_884_;
                        v_isShared_898_ = v_isSharedCheck_917_;
                        state = 3;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_895_);
                        leanh::lean_dec(v_x_884_);
                        v___x_897_ = leanh::lean_box(0);
                        v_isShared_898_ = v_isSharedCheck_917_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_889_ == 0 {
                    v___x_891_ = v___x_888_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_893_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_893_, 0, v_a_886_);
                    v___x_891_ = v_reuseFailAlloc_893_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_892_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_892_, 0, v___x_891_);
                return v___x_892_;
            }
            3 => {
                if leanh::lean_obj_tag(v_a_895_) == 0 {
                    leanh::lean_del_object(v___x_897_);
                    v___x_899_ = l___private_Std_Http_Data_Body_Full_0__Std_Http_Body_Full_takeChunk___lam__0___closed__1;
                    return v___x_899_;
                } else {
                    v_val_900_ = leanh::lean_ctor_get(v_a_895_, 0);
                    v_isSharedCheck_916_ = (!leanh::lean_is_exclusive(v_a_895_)) as u8;
                    if v_isSharedCheck_916_ == 0 {
                        v___x_902_ = v_a_895_;
                        v_isShared_903_ = v_isSharedCheck_916_;
                        state = 4;
                        continue;
                    } else {
                        leanh::lean_inc(v_val_900_);
                        leanh::lean_dec(v_a_895_);
                        v___x_902_ = leanh::lean_box(0);
                        v_isShared_903_ = v_isSharedCheck_916_;
                        state = 4;
                        continue;
                    }
                }
            }
            4 => {
                v___x_904_ = leanh::lean_box(0);
                v___x_905_ = lean_st_ref_set(v_a_883_, v___x_904_);
                v___f_906_ = leanh::lean_alloc_closure(l___private_Std_Http_Data_Body_Full_0__Std_Http_Body_Full_takeChunk___lam__0___boxed as *mut core::ffi::c_void, 3, 1);
                leanh::lean_closure_set(v___f_906_, 0, v_val_900_);
                if v_isShared_898_ == 0 {
                    leanh::lean_ctor_set(v___x_897_, 0, v___x_905_);
                    v___x_908_ = v___x_897_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_915_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_915_, 0, v___x_905_);
                    v___x_908_ = v_reuseFailAlloc_915_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                if v_isShared_903_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_902_, 0);
                    leanh::lean_ctor_set(v___x_902_, 0, v___x_908_);
                    v___x_910_ = v___x_902_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_914_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_914_, 0, v___x_908_);
                    v___x_910_ = v_reuseFailAlloc_914_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                v___x_911_ = leanh::lean_unsigned_to_nat(0);
                v___x_912_ = 0;
                v___x_913_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(
                    leanh::lean_box(0),
                    leanh::lean_box(0),
                    v___x_911_,
                    v___x_912_,
                    v___x_910_,
                    v___f_906_,
                );
                return v___x_913_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Std_Http_Data_Body_Full_0__Std_Http_Body_Full_takeChunk___lam__1___boxed(
    mut v_a_918_: *mut leanh::LeanObject,
    mut v_x_919_: *mut leanh::LeanObject,
    mut v___y_920_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_921_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_921_ = l___private_Std_Http_Data_Body_Full_0__Std_Http_Body_Full_takeChunk___lam__1(
        v_a_918_, v_x_919_,
    );
    leanh::lean_dec(v_a_918_);
    return v_res_921_;
}
pub unsafe fn l___private_Std_Http_Data_Body_Full_0__Std_Http_Body_Full_takeChunk(
    mut v_a_922_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_924_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_925_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_926_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_927_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_928_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_929_: u8 = 0;
    let mut v___x_930_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_924_ = lean_st_ref_get(v_a_922_);
    leanh::lean_inc(v_a_922_);
    v___f_925_ = leanh::lean_alloc_closure(
        l___private_Std_Http_Data_Body_Full_0__Std_Http_Body_Full_takeChunk___lam__1___boxed
            as *mut core::ffi::c_void,
        3,
        1,
    );
    leanh::lean_closure_set(v___f_925_, 0, v_a_922_);
    v___x_926_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_926_, 0, v___x_924_);
    v___x_927_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_927_, 0, v___x_926_);
    v___x_928_ = leanh::lean_unsigned_to_nat(0);
    v___x_929_ = 0;
    v___x_930_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(
        leanh::lean_box(0),
        leanh::lean_box(0),
        v___x_928_,
        v___x_929_,
        v___x_927_,
        v___f_925_,
    );
    return v___x_930_;
}
pub unsafe fn l___private_Std_Http_Data_Body_Full_0__Std_Http_Body_Full_takeChunk___boxed(
    mut v_a_931_: *mut leanh::LeanObject,
    mut v_a_932_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_933_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_933_ = l___private_Std_Http_Data_Body_Full_0__Std_Http_Body_Full_takeChunk(v_a_931_);
    leanh::lean_dec(v_a_931_);
    return v_res_933_;
}
pub unsafe fn l_Std_Http_Body_Full_ofByteArray___lam__0(
    mut v_x_934_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_a_936_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_938_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_939_: u8 = 0;
    let mut v___x_941_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_942_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_943_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_944_: u8 = 0;
    let mut v_a_945_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_947_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_948_: u8 = 0;
    let mut v___x_950_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_951_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_952_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_953_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_934_) == 0 {
                    v_a_936_ = leanh::lean_ctor_get(v_x_934_, 0);
                    v_isSharedCheck_944_ = (!leanh::lean_is_exclusive(v_x_934_)) as u8;
                    if v_isSharedCheck_944_ == 0 {
                        v___x_938_ = v_x_934_;
                        v_isShared_939_ = v_isSharedCheck_944_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_936_);
                        leanh::lean_dec(v_x_934_);
                        v___x_938_ = leanh::lean_box(0);
                        v_isShared_939_ = v_isSharedCheck_944_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_945_ = leanh::lean_ctor_get(v_x_934_, 0);
                    v_isSharedCheck_953_ = (!leanh::lean_is_exclusive(v_x_934_)) as u8;
                    if v_isSharedCheck_953_ == 0 {
                        v___x_947_ = v_x_934_;
                        v_isShared_948_ = v_isSharedCheck_953_;
                        state = 3;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_945_);
                        leanh::lean_dec(v_x_934_);
                        v___x_947_ = leanh::lean_box(0);
                        v_isShared_948_ = v_isSharedCheck_953_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_939_ == 0 {
                    v___x_941_ = v___x_938_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_943_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_943_, 0, v_a_936_);
                    v___x_941_ = v_reuseFailAlloc_943_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_942_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_942_, 0, v___x_941_);
                return v___x_942_;
            }
            3 => {
                if v_isShared_948_ == 0 {
                    v___x_950_ = v___x_947_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_952_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_952_, 0, v_a_945_);
                    v___x_950_ = v_reuseFailAlloc_952_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_951_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_951_, 0, v___x_950_);
                return v___x_951_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Http_Body_Full_ofByteArray___lam__0___boxed(
    mut v_x_954_: *mut leanh::LeanObject,
    mut v___y_955_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_956_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_956_ = l_Std_Http_Body_Full_ofByteArray___lam__0(v_x_954_);
    return v_res_956_;
}
pub unsafe fn l_Std_Http_Body_Full_ofByteArray(
    mut v_data_958_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_960_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_961_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_962_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_963_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_964_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_965_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_966_: u8 = 0;
    let mut v___x_967_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_960_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_960_, 0, v_data_958_);
    v___x_961_ = l_Std_Mutex_new___redArg(v___x_960_);
    v___f_962_ = l_Std_Http_Body_Full_ofByteArray___closed__0;
    v___x_963_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_963_, 0, v___x_961_);
    v___x_964_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_964_, 0, v___x_963_);
    v___x_965_ = leanh::lean_unsigned_to_nat(0);
    v___x_966_ = 0;
    v___x_967_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(
        leanh::lean_box(0),
        leanh::lean_box(0),
        v___x_965_,
        v___x_966_,
        v___x_964_,
        v___f_962_,
    );
    return v___x_967_;
}
pub unsafe fn l_Std_Http_Body_Full_ofByteArray___boxed(
    mut v_data_968_: *mut leanh::LeanObject,
    mut v_a_969_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_970_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_970_ = l_Std_Http_Body_Full_ofByteArray(v_data_968_);
    return v_res_970_;
}
pub unsafe fn l_Std_Http_Body_Full_ofString(
    mut v_data_971_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_973_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_974_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_975_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_976_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_977_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_978_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_979_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_980_: u8 = 0;
    let mut v___x_981_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_973_ = lean_string_to_utf8(v_data_971_);
    v___x_974_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_974_, 0, v___x_973_);
    v___x_975_ = l_Std_Mutex_new___redArg(v___x_974_);
    v___f_976_ = l_Std_Http_Body_Full_ofByteArray___closed__0;
    v___x_977_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_977_, 0, v___x_975_);
    v___x_978_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_978_, 0, v___x_977_);
    v___x_979_ = leanh::lean_unsigned_to_nat(0);
    v___x_980_ = 0;
    v___x_981_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(
        leanh::lean_box(0),
        leanh::lean_box(0),
        v___x_979_,
        v___x_980_,
        v___x_978_,
        v___f_976_,
    );
    return v___x_981_;
}
pub unsafe fn l_Std_Http_Body_Full_ofString___boxed(
    mut v_data_982_: *mut leanh::LeanObject,
    mut v_a_983_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_984_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_984_ = l_Std_Http_Body_Full_ofString(v_data_982_);
    leanh::lean_dec_ref(v_data_982_);
    return v_res_984_;
}
pub unsafe fn l_Std_Mutex_atomically___at___00Std_Http_Body_Full_recv_spec__0___redArg___lam__0(
    mut v_mutex_985_: *mut leanh::LeanObject,
    mut v_x_986_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_988_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_989_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_990_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_988_ = lean_io_basemutex_unlock(v_mutex_985_);
    v___x_989_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_989_, 0, v___x_988_);
    v___x_990_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_990_, 0, v___x_989_);
    return v___x_990_;
}
pub unsafe fn l_Std_Mutex_atomically___at___00Std_Http_Body_Full_recv_spec__0___redArg___lam__0___boxed(
    mut v_mutex_991_: *mut leanh::LeanObject,
    mut v_x_992_: *mut leanh::LeanObject,
    mut v___y_993_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_994_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_994_ = l_Std_Mutex_atomically___at___00Std_Http_Body_Full_recv_spec__0___redArg___lam__0(
        v_mutex_991_,
        v_x_992_,
    );
    leanh::lean_dec(v_x_992_);
    leanh::lean_dec(v_mutex_991_);
    return v_res_994_;
}
pub unsafe fn l_Std_Mutex_atomically___at___00Std_Http_Body_Full_recv_spec__0___redArg___lam__1(
    mut v_k_995_: *mut leanh::LeanObject,
    mut v_ref_996_: *mut leanh::LeanObject,
    mut v_x_997_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_a_999_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1001_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1002_: u8 = 0;
    let mut v___x_1004_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1005_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1006_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1007_: u8 = 0;
    let mut v___x_1008_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_997_) == 0 {
                    leanh::lean_dec(v_ref_996_);
                    leanh::lean_dec_ref(v_k_995_);
                    v_a_999_ = leanh::lean_ctor_get(v_x_997_, 0);
                    v_isSharedCheck_1007_ = (!leanh::lean_is_exclusive(v_x_997_)) as u8;
                    if v_isSharedCheck_1007_ == 0 {
                        v___x_1001_ = v_x_997_;
                        v_isShared_1002_ = v_isSharedCheck_1007_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_999_);
                        leanh::lean_dec(v_x_997_);
                        v___x_1001_ = leanh::lean_box(0);
                        v_isShared_1002_ = v_isSharedCheck_1007_;
                        state = 1;
                        continue;
                    }
                } else {
                    leanh::lean_dec_ref_known(v_x_997_, 1);
                    v___x_1008_ =
                        leanh::lean_apply_2(v_k_995_, v_ref_996_, leanh::lean_box(0));
                    return v___x_1008_;
                }
            }
            1 => {
                if v_isShared_1002_ == 0 {
                    v___x_1004_ = v___x_1001_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1006_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1006_, 0, v_a_999_);
                    v___x_1004_ = v_reuseFailAlloc_1006_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_1005_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_1005_, 0, v___x_1004_);
                return v___x_1005_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Mutex_atomically___at___00Std_Http_Body_Full_recv_spec__0___redArg___lam__1___boxed(
    mut v_k_1009_: *mut leanh::LeanObject,
    mut v_ref_1010_: *mut leanh::LeanObject,
    mut v_x_1011_: *mut leanh::LeanObject,
    mut v___y_1012_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1013_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1013_ = l_Std_Mutex_atomically___at___00Std_Http_Body_Full_recv_spec__0___redArg___lam__1(
        v_k_1009_,
        v_ref_1010_,
        v_x_1011_,
    );
    return v_res_1013_;
}
pub unsafe fn l_Std_Mutex_atomically___at___00Std_Http_Body_Full_recv_spec__0___redArg___lam__2(
    mut v_mutex_1014_: *mut leanh::LeanObject,
    mut v___f_1015_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1017_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1018_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1019_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1020_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1021_: u8 = 0;
    let mut v___x_1022_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1017_ = lean_io_basemutex_lock(v_mutex_1014_);
    v___x_1018_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_1018_, 0, v___x_1017_);
    v___x_1019_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_1019_, 0, v___x_1018_);
    v___x_1020_ = leanh::lean_unsigned_to_nat(0);
    v___x_1021_ = 0;
    v___x_1022_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(
        leanh::lean_box(0),
        leanh::lean_box(0),
        v___x_1020_,
        v___x_1021_,
        v___x_1019_,
        v___f_1015_,
    );
    return v___x_1022_;
}
pub unsafe fn l_Std_Mutex_atomically___at___00Std_Http_Body_Full_recv_spec__0___redArg___lam__2___boxed(
    mut v_mutex_1023_: *mut leanh::LeanObject,
    mut v___f_1024_: *mut leanh::LeanObject,
    mut v___y_1025_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1026_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1026_ = l_Std_Mutex_atomically___at___00Std_Http_Body_Full_recv_spec__0___redArg___lam__2(
        v_mutex_1023_,
        v___f_1024_,
    );
    leanh::lean_dec(v_mutex_1023_);
    return v_res_1026_;
}
pub unsafe fn l_Std_Mutex_atomically___at___00Std_Http_Body_Full_recv_spec__0___redArg___lam__3(
    mut v___y_1027_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_a_1028_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1030_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1031_: u8 = 0;
    let mut v___x_1033_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1034_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1035_: u8 = 0;
    let mut v_a_1036_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1038_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1039_: u8 = 0;
    let mut v_fst_1040_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1042_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1043_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1044_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v___y_1027_) == 0 {
                    v_a_1028_ = leanh::lean_ctor_get(v___y_1027_, 0);
                    v_isSharedCheck_1035_ = (!leanh::lean_is_exclusive(v___y_1027_)) as u8;
                    if v_isSharedCheck_1035_ == 0 {
                        v___x_1030_ = v___y_1027_;
                        v_isShared_1031_ = v_isSharedCheck_1035_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_1028_);
                        leanh::lean_dec(v___y_1027_);
                        v___x_1030_ = leanh::lean_box(0);
                        v_isShared_1031_ = v_isSharedCheck_1035_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_1036_ = leanh::lean_ctor_get(v___y_1027_, 0);
                    v_isSharedCheck_1044_ = (!leanh::lean_is_exclusive(v___y_1027_)) as u8;
                    if v_isSharedCheck_1044_ == 0 {
                        v___x_1038_ = v___y_1027_;
                        v_isShared_1039_ = v_isSharedCheck_1044_;
                        state = 3;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_1036_);
                        leanh::lean_dec(v___y_1027_);
                        v___x_1038_ = leanh::lean_box(0);
                        v_isShared_1039_ = v_isSharedCheck_1044_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_1031_ == 0 {
                    v___x_1033_ = v___x_1030_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1034_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1034_, 0, v_a_1028_);
                    v___x_1033_ = v_reuseFailAlloc_1034_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1033_;
            }
            3 => {
                v_fst_1040_ = leanh::lean_ctor_get(v_a_1036_, 0);
                leanh::lean_inc(v_fst_1040_);
                leanh::lean_dec(v_a_1036_);
                if v_isShared_1039_ == 0 {
                    leanh::lean_ctor_set(v___x_1038_, 0, v_fst_1040_);
                    v___x_1042_ = v___x_1038_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1043_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1043_, 0, v_fst_1040_);
                    v___x_1042_ = v_reuseFailAlloc_1043_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_1042_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Mutex_atomically___at___00Std_Http_Body_Full_recv_spec__0___redArg(
    mut v_mutex_1046_: *mut leanh::LeanObject,
    mut v_k_1047_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_ref_1049_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_mutex_1050_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1051_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1052_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1053_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1054_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1055_: u8 = 0;
    let mut v___x_1056_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1058_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1059_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1060_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1061_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1063_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1064_: u8 = 0;
    let mut v___x_1066_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1067_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1068_: u8 = 0;
    let mut v_a_1069_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1071_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1072_: u8 = 0;
    let mut v_fst_1073_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1075_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1076_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1077_: u8 = 0;
    let mut v_a_1078_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1080_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1081_: u8 = 0;
    let mut v___f_1082_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1083_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1085_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1086_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1087_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ref_1049_ = leanh::lean_ctor_get(v_mutex_1046_, 0);
                leanh::lean_inc(v_ref_1049_);
                v_mutex_1050_ = leanh::lean_ctor_get(v_mutex_1046_, 1);
                leanh::lean_inc_n(v_mutex_1050_, 2);
                leanh::lean_dec_ref(v_mutex_1046_);
                v___f_1051_ = leanh::lean_alloc_closure(l_Std_Mutex_atomically___at___00Std_Http_Body_Full_recv_spec__0___redArg___lam__0___boxed as *mut core::ffi::c_void, 3, 1);
                leanh::lean_closure_set(v___f_1051_, 0, v_mutex_1050_);
                v___f_1052_ = leanh::lean_alloc_closure(l_Std_Mutex_atomically___at___00Std_Http_Body_Full_recv_spec__0___redArg___lam__1___boxed as *mut core::ffi::c_void, 4, 2);
                leanh::lean_closure_set(v___f_1052_, 0, v_k_1047_);
                leanh::lean_closure_set(v___f_1052_, 1, v_ref_1049_);
                v___f_1053_ = leanh::lean_alloc_closure(l_Std_Mutex_atomically___at___00Std_Http_Body_Full_recv_spec__0___redArg___lam__2___boxed as *mut core::ffi::c_void, 3, 2);
                leanh::lean_closure_set(v___f_1053_, 0, v_mutex_1050_);
                leanh::lean_closure_set(v___f_1053_, 1, v___f_1052_);
                v___x_1054_ = leanh::lean_unsigned_to_nat(0);
                v___x_1055_ = 0;
                v___x_1056_ = l_Std_Async_EAsync_tryFinally_x27___redArg(
                    v___f_1053_,
                    v___f_1051_,
                    v___x_1054_,
                    v___x_1055_,
                );
                if leanh::lean_obj_tag(v___x_1056_) == 0 {
                    v_a_1060_ = leanh::lean_ctor_get(v___x_1056_, 0);
                    leanh::lean_inc(v_a_1060_);
                    leanh::lean_dec_ref_known(v___x_1056_, 1);
                    if leanh::lean_obj_tag(v_a_1060_) == 0 {
                        v_a_1061_ = leanh::lean_ctor_get(v_a_1060_, 0);
                        v_isSharedCheck_1068_ = (!leanh::lean_is_exclusive(v_a_1060_)) as u8;
                        if v_isSharedCheck_1068_ == 0 {
                            v___x_1063_ = v_a_1060_;
                            v_isShared_1064_ = v_isSharedCheck_1068_;
                            state = 2;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_1061_);
                            leanh::lean_dec(v_a_1060_);
                            v___x_1063_ = leanh::lean_box(0);
                            v_isShared_1064_ = v_isSharedCheck_1068_;
                            state = 2;
                            continue;
                        }
                    } else {
                        v_a_1069_ = leanh::lean_ctor_get(v_a_1060_, 0);
                        v_isSharedCheck_1077_ = (!leanh::lean_is_exclusive(v_a_1060_)) as u8;
                        if v_isSharedCheck_1077_ == 0 {
                            v___x_1071_ = v_a_1060_;
                            v_isShared_1072_ = v_isSharedCheck_1077_;
                            state = 4;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_1069_);
                            leanh::lean_dec(v_a_1060_);
                            v___x_1071_ = leanh::lean_box(0);
                            v_isShared_1072_ = v_isSharedCheck_1077_;
                            state = 4;
                            continue;
                        }
                    }
                } else {
                    v_a_1078_ = leanh::lean_ctor_get(v___x_1056_, 0);
                    v_isSharedCheck_1087_ = (!leanh::lean_is_exclusive(v___x_1056_)) as u8;
                    if v_isSharedCheck_1087_ == 0 {
                        v___x_1080_ = v___x_1056_;
                        v_isShared_1081_ = v_isSharedCheck_1087_;
                        state = 6;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_1078_);
                        leanh::lean_dec(v___x_1056_);
                        v___x_1080_ = leanh::lean_box(0);
                        v_isShared_1081_ = v_isSharedCheck_1087_;
                        state = 6;
                        continue;
                    }
                }
            }
            1 => {
                v___x_1059_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_1059_, 0, v___y_1058_);
                return v___x_1059_;
            }
            2 => {
                if v_isShared_1064_ == 0 {
                    v___x_1066_ = v___x_1063_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_1067_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1067_, 0, v_a_1061_);
                    v___x_1066_ = v_reuseFailAlloc_1067_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___y_1058_ = v___x_1066_;
                state = 1;
                continue;
            }
            4 => {
                v_fst_1073_ = leanh::lean_ctor_get(v_a_1069_, 0);
                leanh::lean_inc(v_fst_1073_);
                leanh::lean_dec(v_a_1069_);
                if v_isShared_1072_ == 0 {
                    leanh::lean_ctor_set(v___x_1071_, 0, v_fst_1073_);
                    v___x_1075_ = v___x_1071_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_1076_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1076_, 0, v_fst_1073_);
                    v___x_1075_ = v_reuseFailAlloc_1076_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v___y_1058_ = v___x_1075_;
                state = 1;
                continue;
            }
            6 => {
                v___f_1082_ = l_Std_Mutex_atomically___at___00Std_Http_Body_Full_recv_spec__0___redArg___closed__0;
                v___x_1083_ = lean_task_map(v___f_1082_, v_a_1078_, v___x_1054_, v___x_1055_);
                if v_isShared_1081_ == 0 {
                    leanh::lean_ctor_set(v___x_1080_, 0, v___x_1083_);
                    v___x_1085_ = v___x_1080_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_1086_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1086_, 0, v___x_1083_);
                    v___x_1085_ = v_reuseFailAlloc_1086_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_1085_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Mutex_atomically___at___00Std_Http_Body_Full_recv_spec__0___redArg___boxed(
    mut v_mutex_1088_: *mut leanh::LeanObject,
    mut v_k_1089_: *mut leanh::LeanObject,
    mut v___y_1090_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1091_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1091_ = l_Std_Mutex_atomically___at___00Std_Http_Body_Full_recv_spec__0___redArg(
        v_mutex_1088_,
        v_k_1089_,
    );
    return v_res_1091_;
}
pub unsafe fn l_Std_Mutex_atomically___at___00Std_Http_Body_Full_recv_spec__0(
    mut v_00_u03b1_1092_: *mut leanh::LeanObject,
    mut v_00_u03b2_1093_: *mut leanh::LeanObject,
    mut v_mutex_1094_: *mut leanh::LeanObject,
    mut v_k_1095_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1097_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1097_ = l_Std_Mutex_atomically___at___00Std_Http_Body_Full_recv_spec__0___redArg(
        v_mutex_1094_,
        v_k_1095_,
    );
    return v___x_1097_;
}
pub unsafe fn l_Std_Mutex_atomically___at___00Std_Http_Body_Full_recv_spec__0___boxed(
    mut v_00_u03b1_1098_: *mut leanh::LeanObject,
    mut v_00_u03b2_1099_: *mut leanh::LeanObject,
    mut v_mutex_1100_: *mut leanh::LeanObject,
    mut v_k_1101_: *mut leanh::LeanObject,
    mut v___y_1102_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1103_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1103_ = l_Std_Mutex_atomically___at___00Std_Http_Body_Full_recv_spec__0(
        v_00_u03b1_1098_,
        v_00_u03b2_1099_,
        v_mutex_1100_,
        v_k_1101_,
    );
    return v_res_1103_;
}
pub unsafe fn l_Std_Http_Body_Full_recv(
    mut v_full_1104_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1106_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1107_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1106_ = leanh::lean_alloc_closure(
        l___private_Std_Http_Data_Body_Full_0__Std_Http_Body_Full_takeChunk___boxed
            as *mut core::ffi::c_void,
        2,
        0,
    );
    v___x_1107_ = l_Std_Mutex_atomically___at___00Std_Http_Body_Full_recv_spec__0___redArg(
        v_full_1104_,
        v___x_1106_,
    );
    return v___x_1107_;
}
pub unsafe fn l_Std_Http_Body_Full_recv___boxed(
    mut v_full_1108_: *mut leanh::LeanObject,
    mut v_a_1109_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1110_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1110_ = l_Std_Http_Body_Full_recv(v_full_1108_);
    return v_res_1110_;
}
pub unsafe fn l_Std_Http_Body_Full_close___lam__0(
    mut v___x_1111_: *mut leanh::LeanObject,
    mut v___y_1112_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1114_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1115_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1116_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1114_ = lean_st_ref_set(v___y_1112_, v___x_1111_);
    v___x_1115_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_1115_, 0, v___x_1114_);
    v___x_1116_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_1116_, 0, v___x_1115_);
    return v___x_1116_;
}
pub unsafe fn l_Std_Http_Body_Full_close___lam__0___boxed(
    mut v___x_1117_: *mut leanh::LeanObject,
    mut v___y_1118_: *mut leanh::LeanObject,
    mut v___y_1119_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1120_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1120_ = l_Std_Http_Body_Full_close___lam__0(v___x_1117_, v___y_1118_);
    leanh::lean_dec(v___y_1118_);
    return v_res_1120_;
}
pub unsafe fn l_Std_Http_Body_Full_close(
    mut v_full_1123_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_1125_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1126_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_1125_ = l_Std_Http_Body_Full_close___closed__0;
    v___x_1126_ = l_Std_Mutex_atomically___at___00Std_Http_Body_Full_recv_spec__0___redArg(
        v_full_1123_,
        v___f_1125_,
    );
    return v___x_1126_;
}
pub unsafe fn l_Std_Http_Body_Full_close___boxed(
    mut v_full_1127_: *mut leanh::LeanObject,
    mut v_a_1128_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1129_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1129_ = l_Std_Http_Body_Full_close(v_full_1127_);
    return v_res_1129_;
}
pub unsafe fn l_Std_Http_Body_Full_isClosed___lam__0(
    mut v_x_1130_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___y_1133_: u8 = 0;
    let mut v___x_1134_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1135_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1136_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1137_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1139_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1140_: u8 = 0;
    let mut v___x_1142_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1143_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1144_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1145_: u8 = 0;
    let mut v_a_1146_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1147_: u8 = 0;
    let mut v___x_1148_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_1130_) == 0 {
                    v_a_1137_ = leanh::lean_ctor_get(v_x_1130_, 0);
                    v_isSharedCheck_1145_ = (!leanh::lean_is_exclusive(v_x_1130_)) as u8;
                    if v_isSharedCheck_1145_ == 0 {
                        v___x_1139_ = v_x_1130_;
                        v_isShared_1140_ = v_isSharedCheck_1145_;
                        state = 2;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_1137_);
                        leanh::lean_dec(v_x_1130_);
                        v___x_1139_ = leanh::lean_box(0);
                        v_isShared_1140_ = v_isSharedCheck_1145_;
                        state = 2;
                        continue;
                    }
                } else {
                    v_a_1146_ = leanh::lean_ctor_get(v_x_1130_, 0);
                    leanh::lean_inc(v_a_1146_);
                    leanh::lean_dec_ref_known(v_x_1130_, 1);
                    if leanh::lean_obj_tag(v_a_1146_) == 0 {
                        v___x_1147_ = 1;
                        v___y_1133_ = v___x_1147_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_dec_ref_known(v_a_1146_, 1);
                        v___x_1148_ = 0;
                        v___y_1133_ = v___x_1148_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_1134_ = leanh::lean_box((v___y_1133_) as usize);
                v___x_1135_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_1135_, 0, v___x_1134_);
                v___x_1136_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_1136_, 0, v___x_1135_);
                return v___x_1136_;
            }
            2 => {
                if v_isShared_1140_ == 0 {
                    v___x_1142_ = v___x_1139_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_1144_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1144_, 0, v_a_1137_);
                    v___x_1142_ = v_reuseFailAlloc_1144_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_1143_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_1143_, 0, v___x_1142_);
                return v___x_1143_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Http_Body_Full_isClosed___lam__0___boxed(
    mut v_x_1149_: *mut leanh::LeanObject,
    mut v___y_1150_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1151_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1151_ = l_Std_Http_Body_Full_isClosed___lam__0(v_x_1149_);
    return v_res_1151_;
}
pub unsafe fn l_Std_Http_Body_Full_isClosed___lam__1(
    mut v___f_1152_: *mut leanh::LeanObject,
    mut v___y_1153_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1155_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1156_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1157_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1158_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1159_: u8 = 0;
    let mut v___x_1160_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1155_ = lean_st_ref_get(v___y_1153_);
    v___x_1156_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_1156_, 0, v___x_1155_);
    v___x_1157_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_1157_, 0, v___x_1156_);
    v___x_1158_ = leanh::lean_unsigned_to_nat(0);
    v___x_1159_ = 0;
    v___x_1160_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(
        leanh::lean_box(0),
        leanh::lean_box(0),
        v___x_1158_,
        v___x_1159_,
        v___x_1157_,
        v___f_1152_,
    );
    return v___x_1160_;
}
pub unsafe fn l_Std_Http_Body_Full_isClosed___lam__1___boxed(
    mut v___f_1161_: *mut leanh::LeanObject,
    mut v___y_1162_: *mut leanh::LeanObject,
    mut v___y_1163_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1164_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1164_ = l_Std_Http_Body_Full_isClosed___lam__1(v___f_1161_, v___y_1162_);
    leanh::lean_dec(v___y_1162_);
    return v_res_1164_;
}
pub unsafe fn l_Std_Http_Body_Full_isClosed(
    mut v_full_1168_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_1170_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1171_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_1170_ = l_Std_Http_Body_Full_isClosed___closed__1;
    v___x_1171_ = l_Std_Mutex_atomically___at___00Std_Http_Body_Full_recv_spec__0___redArg(
        v_full_1168_,
        v___f_1170_,
    );
    return v___x_1171_;
}
pub unsafe fn l_Std_Http_Body_Full_isClosed___boxed(
    mut v_full_1172_: *mut leanh::LeanObject,
    mut v_a_1173_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1174_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1174_ = l_Std_Http_Body_Full_isClosed(v_full_1172_);
    return v_res_1174_;
}
pub unsafe fn l_Std_Http_Body_Full_getKnownSize___lam__0(
    mut v_x_1183_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_a_1185_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1187_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1188_: u8 = 0;
    let mut v___x_1190_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1191_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1192_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1193_: u8 = 0;
    let mut v_a_1194_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1196_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1197_: u8 = 0;
    let mut v___x_1198_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1199_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1201_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1202_: u8 = 0;
    let mut v___x_1203_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1204_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1206_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1208_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1209_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1210_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1211_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1212_: u8 = 0;
    let mut v_isSharedCheck_1213_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_1183_) == 0 {
                    v_a_1185_ = leanh::lean_ctor_get(v_x_1183_, 0);
                    v_isSharedCheck_1193_ = (!leanh::lean_is_exclusive(v_x_1183_)) as u8;
                    if v_isSharedCheck_1193_ == 0 {
                        v___x_1187_ = v_x_1183_;
                        v_isShared_1188_ = v_isSharedCheck_1193_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_1185_);
                        leanh::lean_dec(v_x_1183_);
                        v___x_1187_ = leanh::lean_box(0);
                        v_isShared_1188_ = v_isSharedCheck_1193_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_1194_ = leanh::lean_ctor_get(v_x_1183_, 0);
                    v_isSharedCheck_1213_ = (!leanh::lean_is_exclusive(v_x_1183_)) as u8;
                    if v_isSharedCheck_1213_ == 0 {
                        v___x_1196_ = v_x_1183_;
                        v_isShared_1197_ = v_isSharedCheck_1213_;
                        state = 3;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_1194_);
                        leanh::lean_dec(v_x_1183_);
                        v___x_1196_ = leanh::lean_box(0);
                        v_isShared_1197_ = v_isSharedCheck_1213_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_1188_ == 0 {
                    v___x_1190_ = v___x_1187_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1192_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1192_, 0, v_a_1185_);
                    v___x_1190_ = v_reuseFailAlloc_1192_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_1191_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_1191_, 0, v___x_1190_);
                return v___x_1191_;
            }
            3 => {
                if leanh::lean_obj_tag(v_a_1194_) == 0 {
                    leanh::lean_del_object(v___x_1196_);
                    v___x_1198_ = l_Std_Http_Body_Full_getKnownSize___lam__0___closed__3;
                    return v___x_1198_;
                } else {
                    v_val_1199_ = leanh::lean_ctor_get(v_a_1194_, 0);
                    v_isSharedCheck_1212_ = (!leanh::lean_is_exclusive(v_a_1194_)) as u8;
                    if v_isSharedCheck_1212_ == 0 {
                        v___x_1201_ = v_a_1194_;
                        v_isShared_1202_ = v_isSharedCheck_1212_;
                        state = 4;
                        continue;
                    } else {
                        leanh::lean_inc(v_val_1199_);
                        leanh::lean_dec(v_a_1194_);
                        v___x_1201_ = leanh::lean_box(0);
                        v_isShared_1202_ = v_isSharedCheck_1212_;
                        state = 4;
                        continue;
                    }
                }
            }
            4 => {
                v___x_1203_ = lean_byte_array_size(v_val_1199_);
                leanh::lean_dec(v_val_1199_);
                v___x_1204_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_1204_, 0, v___x_1203_);
                if v_isShared_1202_ == 0 {
                    leanh::lean_ctor_set(v___x_1201_, 0, v___x_1204_);
                    v___x_1206_ = v___x_1201_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_1211_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1211_, 0, v___x_1204_);
                    v___x_1206_ = v_reuseFailAlloc_1211_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                if v_isShared_1197_ == 0 {
                    leanh::lean_ctor_set(v___x_1196_, 0, v___x_1206_);
                    v___x_1208_ = v___x_1196_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_1210_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1210_, 0, v___x_1206_);
                    v___x_1208_ = v_reuseFailAlloc_1210_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                v___x_1209_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_1209_, 0, v___x_1208_);
                return v___x_1209_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Http_Body_Full_getKnownSize___lam__0___boxed(
    mut v_x_1214_: *mut leanh::LeanObject,
    mut v___y_1215_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1216_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1216_ = l_Std_Http_Body_Full_getKnownSize___lam__0(v_x_1214_);
    return v_res_1216_;
}
pub unsafe fn l_Std_Http_Body_Full_getKnownSize___lam__1(
    mut v___f_1217_: *mut leanh::LeanObject,
    mut v___y_1218_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1220_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1221_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1222_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1223_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1224_: u8 = 0;
    let mut v___x_1225_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1220_ = lean_st_ref_get(v___y_1218_);
    v___x_1221_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_1221_, 0, v___x_1220_);
    v___x_1222_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_1222_, 0, v___x_1221_);
    v___x_1223_ = leanh::lean_unsigned_to_nat(0);
    v___x_1224_ = 0;
    v___x_1225_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(
        leanh::lean_box(0),
        leanh::lean_box(0),
        v___x_1223_,
        v___x_1224_,
        v___x_1222_,
        v___f_1217_,
    );
    return v___x_1225_;
}
pub unsafe fn l_Std_Http_Body_Full_getKnownSize___lam__1___boxed(
    mut v___f_1226_: *mut leanh::LeanObject,
    mut v___y_1227_: *mut leanh::LeanObject,
    mut v___y_1228_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1229_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1229_ = l_Std_Http_Body_Full_getKnownSize___lam__1(v___f_1226_, v___y_1227_);
    leanh::lean_dec(v___y_1227_);
    return v_res_1229_;
}
pub unsafe fn l_Std_Http_Body_Full_getKnownSize(
    mut v_full_1233_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_1235_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1236_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_1235_ = l_Std_Http_Body_Full_getKnownSize___closed__1;
    v___x_1236_ = l_Std_Mutex_atomically___at___00Std_Http_Body_Full_recv_spec__0___redArg(
        v_full_1233_,
        v___f_1235_,
    );
    return v___x_1236_;
}
pub unsafe fn l_Std_Http_Body_Full_getKnownSize___boxed(
    mut v_full_1237_: *mut leanh::LeanObject,
    mut v_a_1238_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1239_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1239_ = l_Std_Http_Body_Full_getKnownSize(v_full_1237_);
    return v_res_1239_;
}
pub unsafe fn l_Std_Http_Body_Full_tryRecv___lam__0(
    mut v_x_1240_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_a_1242_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1244_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1245_: u8 = 0;
    let mut v___x_1247_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1248_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1249_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1250_: u8 = 0;
    let mut v_a_1251_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1253_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1254_: u8 = 0;
    let mut v___x_1255_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1257_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1258_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1259_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1260_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_1240_) == 0 {
                    v_a_1242_ = leanh::lean_ctor_get(v_x_1240_, 0);
                    v_isSharedCheck_1250_ = (!leanh::lean_is_exclusive(v_x_1240_)) as u8;
                    if v_isSharedCheck_1250_ == 0 {
                        v___x_1244_ = v_x_1240_;
                        v_isShared_1245_ = v_isSharedCheck_1250_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_1242_);
                        leanh::lean_dec(v_x_1240_);
                        v___x_1244_ = leanh::lean_box(0);
                        v_isShared_1245_ = v_isSharedCheck_1250_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_1251_ = leanh::lean_ctor_get(v_x_1240_, 0);
                    v_isSharedCheck_1260_ = (!leanh::lean_is_exclusive(v_x_1240_)) as u8;
                    if v_isSharedCheck_1260_ == 0 {
                        v___x_1253_ = v_x_1240_;
                        v_isShared_1254_ = v_isSharedCheck_1260_;
                        state = 3;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_1251_);
                        leanh::lean_dec(v_x_1240_);
                        v___x_1253_ = leanh::lean_box(0);
                        v_isShared_1254_ = v_isSharedCheck_1260_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_1245_ == 0 {
                    v___x_1247_ = v___x_1244_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1249_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1249_, 0, v_a_1242_);
                    v___x_1247_ = v_reuseFailAlloc_1249_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_1248_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_1248_, 0, v___x_1247_);
                return v___x_1248_;
            }
            3 => {
                v___x_1255_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_1255_, 0, v_a_1251_);
                if v_isShared_1254_ == 0 {
                    leanh::lean_ctor_set(v___x_1253_, 0, v___x_1255_);
                    v___x_1257_ = v___x_1253_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1259_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1259_, 0, v___x_1255_);
                    v___x_1257_ = v_reuseFailAlloc_1259_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_1258_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_1258_, 0, v___x_1257_);
                return v___x_1258_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Http_Body_Full_tryRecv___lam__0___boxed(
    mut v_x_1261_: *mut leanh::LeanObject,
    mut v___y_1262_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1263_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1263_ = l_Std_Http_Body_Full_tryRecv___lam__0(v_x_1261_);
    return v_res_1263_;
}
pub unsafe fn l_Std_Http_Body_Full_tryRecv(
    mut v_full_1265_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1267_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1268_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1269_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1270_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1271_: u8 = 0;
    let mut v___x_1272_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1267_ = leanh::lean_alloc_closure(
        l___private_Std_Http_Data_Body_Full_0__Std_Http_Body_Full_takeChunk___boxed
            as *mut core::ffi::c_void,
        2,
        0,
    );
    v___x_1268_ = l_Std_Mutex_atomically___at___00Std_Http_Body_Full_recv_spec__0___redArg(
        v_full_1265_,
        v___x_1267_,
    );
    v___f_1269_ = l_Std_Http_Body_Full_tryRecv___closed__0;
    v___x_1270_ = leanh::lean_unsigned_to_nat(0);
    v___x_1271_ = 0;
    v___x_1272_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(
        leanh::lean_box(0),
        leanh::lean_box(0),
        v___x_1270_,
        v___x_1271_,
        v___x_1268_,
        v___f_1269_,
    );
    return v___x_1272_;
}
pub unsafe fn l_Std_Http_Body_Full_tryRecv___boxed(
    mut v_full_1273_: *mut leanh::LeanObject,
    mut v_a_1274_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1275_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1275_ = l_Std_Http_Body_Full_tryRecv(v_full_1273_);
    return v_res_1275_;
}
pub unsafe fn l_Std_Async_Waiter_race___at___00Std_Http_Body_Full_recvSelector_spec__0___lam__0(
    mut v_promise_1276_: *mut leanh::LeanObject,
    mut v_x_1277_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_a_1279_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1281_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1282_: u8 = 0;
    let mut v___x_1284_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1285_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1286_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1287_: u8 = 0;
    let mut v___x_1288_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1289_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1290_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_1277_) == 0 {
                    v_a_1279_ = leanh::lean_ctor_get(v_x_1277_, 0);
                    v_isSharedCheck_1287_ = (!leanh::lean_is_exclusive(v_x_1277_)) as u8;
                    if v_isSharedCheck_1287_ == 0 {
                        v___x_1281_ = v_x_1277_;
                        v_isShared_1282_ = v_isSharedCheck_1287_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_1279_);
                        leanh::lean_dec(v_x_1277_);
                        v___x_1281_ = leanh::lean_box(0);
                        v_isShared_1282_ = v_isSharedCheck_1287_;
                        state = 1;
                        continue;
                    }
                } else {
                    v___x_1288_ = lean_io_promise_resolve(v_x_1277_, v_promise_1276_);
                    v___x_1289_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_1289_, 0, v___x_1288_);
                    v___x_1290_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_1290_, 0, v___x_1289_);
                    return v___x_1290_;
                }
            }
            1 => {
                if v_isShared_1282_ == 0 {
                    v___x_1284_ = v___x_1281_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1286_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1286_, 0, v_a_1279_);
                    v___x_1284_ = v_reuseFailAlloc_1286_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_1285_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_1285_, 0, v___x_1284_);
                return v___x_1285_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Async_Waiter_race___at___00Std_Http_Body_Full_recvSelector_spec__0___lam__0___boxed(
    mut v_promise_1291_: *mut leanh::LeanObject,
    mut v_x_1292_: *mut leanh::LeanObject,
    mut v___y_1293_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1294_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1294_ = l_Std_Async_Waiter_race___at___00Std_Http_Body_Full_recvSelector_spec__0___lam__0(
        v_promise_1291_,
        v_x_1292_,
    );
    leanh::lean_dec(v_promise_1291_);
    return v_res_1294_;
}
pub unsafe fn l_Std_Async_Waiter_race___at___00Std_Http_Body_Full_recvSelector_spec__0___lam__1(
    mut v_lose_1295_: *mut leanh::LeanObject,
    mut v___y_1296_: *mut leanh::LeanObject,
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
    let mut v___x_1310_: u8 = 0;
    let mut v___x_1311_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1312_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1313_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1314_: u8 = 0;
    let mut v___x_1315_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_1298_) == 0 {
                    leanh::lean_dec_ref(v___f_1297_);
                    leanh::lean_dec_ref(v_lose_1295_);
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
                    v___x_1310_ = (leanh::lean_unbox(v_a_1309_) as u8);
                    leanh::lean_dec(v_a_1309_);
                    if v___x_1310_ == 0 {
                        leanh::lean_dec_ref(v___f_1297_);
                        leanh::lean_inc(v___y_1296_);
                        v___x_1311_ = leanh::lean_apply_2(
                            v_lose_1295_,
                            v___y_1296_,
                            leanh::lean_box(0),
                        );
                        return v___x_1311_;
                    } else {
                        leanh::lean_dec_ref(v_lose_1295_);
                        v___x_1312_ =
                            l___private_Std_Http_Data_Body_Full_0__Std_Http_Body_Full_takeChunk(
                                v___y_1296_,
                            );
                        v___x_1313_ = leanh::lean_unsigned_to_nat(0);
                        v___x_1314_ = 0;
                        v___x_1315_ =
                            l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(
                                leanh::lean_box(0),
                                leanh::lean_box(0),
                                v___x_1313_,
                                v___x_1314_,
                                v___x_1312_,
                                v___f_1297_,
                            );
                        return v___x_1315_;
                    }
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
pub unsafe fn l_Std_Async_Waiter_race___at___00Std_Http_Body_Full_recvSelector_spec__0___lam__1___boxed(
    mut v_lose_1316_: *mut leanh::LeanObject,
    mut v___y_1317_: *mut leanh::LeanObject,
    mut v___f_1318_: *mut leanh::LeanObject,
    mut v_x_1319_: *mut leanh::LeanObject,
    mut v___y_1320_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1321_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1321_ = l_Std_Async_Waiter_race___at___00Std_Http_Body_Full_recvSelector_spec__0___lam__1(
        v_lose_1316_,
        v___y_1317_,
        v___f_1318_,
        v_x_1319_,
    );
    leanh::lean_dec(v___y_1317_);
    return v_res_1321_;
}
pub unsafe fn l_Std_Async_Waiter_race___at___00Std_Http_Body_Full_recvSelector_spec__0(
    mut v_w_1322_: *mut leanh::LeanObject,
    mut v_lose_1323_: *mut leanh::LeanObject,
    mut v___y_1324_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_finished_1326_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_promise_1327_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1328_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1329_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1330_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1332_: u8 = 0;
    let mut v___x_1333_: u8 = 0;
    let mut v___x_1334_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1335_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1336_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1337_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1338_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1339_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1340_: u8 = 0;
    let mut v___x_1341_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1342_: u8 = 0;
    let mut v___x_1343_: u8 = 0;
    let mut v___x_1344_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_finished_1326_ = leanh::lean_ctor_get(v_w_1322_, 0);
                leanh::lean_inc(v_finished_1326_);
                v_promise_1327_ = leanh::lean_ctor_get(v_w_1322_, 1);
                leanh::lean_inc(v_promise_1327_);
                leanh::lean_dec_ref(v_w_1322_);
                v___x_1328_ = lean_st_ref_take(v_finished_1326_);
                v___f_1329_ = leanh::lean_alloc_closure(l_Std_Async_Waiter_race___at___00Std_Http_Body_Full_recvSelector_spec__0___lam__0___boxed as *mut core::ffi::c_void, 3, 1);
                leanh::lean_closure_set(v___f_1329_, 0, v_promise_1327_);
                leanh::lean_inc(v___y_1324_);
                v___f_1330_ = leanh::lean_alloc_closure(l_Std_Async_Waiter_race___at___00Std_Http_Body_Full_recvSelector_spec__0___lam__1___boxed as *mut core::ffi::c_void, 5, 3);
                leanh::lean_closure_set(v___f_1330_, 0, v_lose_1323_);
                leanh::lean_closure_set(v___f_1330_, 1, v___y_1324_);
                leanh::lean_closure_set(v___f_1330_, 2, v___f_1329_);
                v___x_1342_ = (leanh::lean_unbox(v___x_1328_) as u8);
                leanh::lean_dec(v___x_1328_);
                if v___x_1342_ == 0 {
                    v___x_1343_ = 1;
                    v___y_1332_ = v___x_1343_;
                    state = 1;
                    continue;
                } else {
                    v___x_1344_ = 0;
                    v___y_1332_ = v___x_1344_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_1333_ = 1;
                v___x_1334_ = leanh::lean_box((v___x_1333_) as usize);
                v___x_1335_ = lean_st_ref_set(v_finished_1326_, v___x_1334_);
                leanh::lean_dec(v_finished_1326_);
                v___x_1336_ = leanh::lean_box((v___y_1332_) as usize);
                v___x_1337_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_1337_, 0, v___x_1336_);
                v___x_1338_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_1338_, 0, v___x_1337_);
                v___x_1339_ = leanh::lean_unsigned_to_nat(0);
                v___x_1340_ = 0;
                v___x_1341_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(
                    leanh::lean_box(0),
                    leanh::lean_box(0),
                    v___x_1339_,
                    v___x_1340_,
                    v___x_1338_,
                    v___f_1330_,
                );
                return v___x_1341_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Async_Waiter_race___at___00Std_Http_Body_Full_recvSelector_spec__0___boxed(
    mut v_w_1345_: *mut leanh::LeanObject,
    mut v_lose_1346_: *mut leanh::LeanObject,
    mut v___y_1347_: *mut leanh::LeanObject,
    mut v___y_1348_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1349_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1349_ = l_Std_Async_Waiter_race___at___00Std_Http_Body_Full_recvSelector_spec__0(
        v_w_1345_,
        v_lose_1346_,
        v___y_1347_,
    );
    leanh::lean_dec(v___y_1347_);
    return v_res_1349_;
}
pub unsafe fn l_Std_Http_Body_Full_recvSelector___lam__0(
    mut v___x_1350_: *mut leanh::LeanObject,
    mut v___y_1351_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1353_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1354_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1353_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_1353_, 0, v___x_1350_);
    v___x_1354_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_1354_, 0, v___x_1353_);
    return v___x_1354_;
}
pub unsafe fn l_Std_Http_Body_Full_recvSelector___lam__0___boxed(
    mut v___x_1355_: *mut leanh::LeanObject,
    mut v___y_1356_: *mut leanh::LeanObject,
    mut v___y_1357_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1358_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1358_ = l_Std_Http_Body_Full_recvSelector___lam__0(v___x_1355_, v___y_1356_);
    leanh::lean_dec(v___y_1356_);
    return v_res_1358_;
}
pub unsafe fn l_Std_Http_Body_Full_recvSelector___lam__1(
    mut v_full_1361_: *mut leanh::LeanObject,
    mut v_waiter_1362_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_lose_1364_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1365_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1366_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_lose_1364_ = l_Std_Http_Body_Full_recvSelector___lam__1___closed__0;
    v___x_1365_ = leanh::lean_alloc_closure(
        l_Std_Async_Waiter_race___at___00Std_Http_Body_Full_recvSelector_spec__0___boxed
            as *mut core::ffi::c_void,
        4,
        2,
    );
    leanh::lean_closure_set(v___x_1365_, 0, v_waiter_1362_);
    leanh::lean_closure_set(v___x_1365_, 1, v_lose_1364_);
    v___x_1366_ = l_Std_Mutex_atomically___at___00Std_Http_Body_Full_recv_spec__0___redArg(
        v_full_1361_,
        v___x_1365_,
    );
    return v___x_1366_;
}
pub unsafe fn l_Std_Http_Body_Full_recvSelector___lam__1___boxed(
    mut v_full_1367_: *mut leanh::LeanObject,
    mut v_waiter_1368_: *mut leanh::LeanObject,
    mut v___y_1369_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1370_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1370_ = l_Std_Http_Body_Full_recvSelector___lam__1(v_full_1367_, v_waiter_1368_);
    return v_res_1370_;
}
pub unsafe fn l_Std_Http_Body_Full_recvSelector___lam__3(
    mut v_full_1371_: *mut leanh::LeanObject,
    mut v___x_1372_: *mut leanh::LeanObject,
    mut v___f_1373_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1375_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1376_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1377_: u8 = 0;
    let mut v___x_1378_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1375_ = l_Std_Mutex_atomically___at___00Std_Http_Body_Full_recv_spec__0___redArg(
        v_full_1371_,
        v___x_1372_,
    );
    v___x_1376_ = leanh::lean_unsigned_to_nat(0);
    v___x_1377_ = 0;
    v___x_1378_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(
        leanh::lean_box(0),
        leanh::lean_box(0),
        v___x_1376_,
        v___x_1377_,
        v___x_1375_,
        v___f_1373_,
    );
    return v___x_1378_;
}
pub unsafe fn l_Std_Http_Body_Full_recvSelector___lam__3___boxed(
    mut v_full_1379_: *mut leanh::LeanObject,
    mut v___x_1380_: *mut leanh::LeanObject,
    mut v___f_1381_: *mut leanh::LeanObject,
    mut v___y_1382_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1383_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1383_ =
        l_Std_Http_Body_Full_recvSelector___lam__3(v_full_1379_, v___x_1380_, v___f_1381_);
    return v_res_1383_;
}
pub unsafe fn l_Std_Http_Body_Full_recvSelector___lam__2(
    mut v___x_1384_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1386_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1387_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1386_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_1386_, 0, v___x_1384_);
    v___x_1387_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_1387_, 0, v___x_1386_);
    return v___x_1387_;
}
pub unsafe fn l_Std_Http_Body_Full_recvSelector___lam__2___boxed(
    mut v___x_1388_: *mut leanh::LeanObject,
    mut v___y_1389_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1390_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1390_ = l_Std_Http_Body_Full_recvSelector___lam__2(v___x_1388_);
    return v_res_1390_;
}
pub unsafe fn l_Std_Http_Body_Full_recvSelector(
    mut v_full_1393_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_1394_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1395_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1396_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1397_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1398_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1399_: *mut leanh::LeanObject = core::ptr::null_mut();
    leanh::lean_inc_ref(v_full_1393_);
    v___f_1394_ = leanh::lean_alloc_closure(
        l_Std_Http_Body_Full_recvSelector___lam__1___boxed as *mut core::ffi::c_void,
        3,
        1,
    );
    leanh::lean_closure_set(v___f_1394_, 0, v_full_1393_);
    v___f_1395_ = l_Std_Http_Body_Full_tryRecv___closed__0;
    v___x_1396_ = leanh::lean_alloc_closure(
        l___private_Std_Http_Data_Body_Full_0__Std_Http_Body_Full_takeChunk___boxed
            as *mut core::ffi::c_void,
        2,
        0,
    );
    v___f_1397_ = leanh::lean_alloc_closure(
        l_Std_Http_Body_Full_recvSelector___lam__3___boxed as *mut core::ffi::c_void,
        4,
        3,
    );
    leanh::lean_closure_set(v___f_1397_, 0, v_full_1393_);
    leanh::lean_closure_set(v___f_1397_, 1, v___x_1396_);
    leanh::lean_closure_set(v___f_1397_, 2, v___f_1395_);
    v___f_1398_ = l_Std_Http_Body_Full_recvSelector___closed__0;
    v___x_1399_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
    leanh::lean_ctor_set(v___x_1399_, 0, v___f_1397_);
    leanh::lean_ctor_set(v___x_1399_, 1, v___f_1394_);
    leanh::lean_ctor_set(v___x_1399_, 2, v___f_1398_);
    return v___x_1399_;
}
pub unsafe fn l_Std_Http_Body_instFull___lam__0(
    mut v_x_1404_: *mut leanh::LeanObject,
    mut v_x_1405_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1407_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1407_ = l_Std_Http_Body_instFull___lam__0___closed__1;
    return v___x_1407_;
}
pub unsafe fn l_Std_Http_Body_instFull___lam__0___boxed(
    mut v_x_1408_: *mut leanh::LeanObject,
    mut v_x_1409_: *mut leanh::LeanObject,
    mut v___y_1410_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1411_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1411_ = l_Std_Http_Body_instFull___lam__0(v_x_1408_, v_x_1409_);
    leanh::lean_dec(v_x_1409_);
    leanh::lean_dec_ref(v_x_1408_);
    return v_res_1411_;
}
pub unsafe fn l_Std_Http_Body_instCoeResponseFullAny___lam__0(
    mut v___x_1431_: *mut leanh::LeanObject,
    mut v_f_1432_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_line_1433_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_body_1434_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_extensions_1435_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1437_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1438_: u8 = 0;
    let mut v___x_1439_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1441_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1442_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1443_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_line_1433_ = leanh::lean_ctor_get(v_f_1432_, 0);
                v_body_1434_ = leanh::lean_ctor_get(v_f_1432_, 1);
                v_extensions_1435_ = leanh::lean_ctor_get(v_f_1432_, 2);
                v_isSharedCheck_1443_ = (!leanh::lean_is_exclusive(v_f_1432_)) as u8;
                if v_isSharedCheck_1443_ == 0 {
                    v___x_1437_ = v_f_1432_;
                    v_isShared_1438_ = v_isSharedCheck_1443_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_extensions_1435_);
                    leanh::lean_inc(v_body_1434_);
                    leanh::lean_inc(v_line_1433_);
                    leanh::lean_dec(v_f_1432_);
                    v___x_1437_ = leanh::lean_box(0);
                    v_isShared_1438_ = v_isSharedCheck_1443_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_1439_ = l_Std_Http_Body_Any_ofBody___redArg(v___x_1431_, v_body_1434_);
                if v_isShared_1438_ == 0 {
                    leanh::lean_ctor_set(v___x_1437_, 1, v___x_1439_);
                    v___x_1441_ = v___x_1437_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1442_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1442_, 0, v_line_1433_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1442_, 1, v___x_1439_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1442_, 2, v_extensions_1435_);
                    v___x_1441_ = v_reuseFailAlloc_1442_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1441_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Http_Body_instCoeContextAsyncResponseFullAny___lam__0(
    mut v___x_1447_: *mut leanh::LeanObject,
    mut v_x_1448_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_a_1450_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1452_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1453_: u8 = 0;
    let mut v___x_1455_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1456_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1457_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1458_: u8 = 0;
    let mut v_a_1459_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1461_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1462_: u8 = 0;
    let mut v_line_1463_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_body_1464_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_extensions_1465_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1467_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1468_: u8 = 0;
    let mut v___x_1469_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1471_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1473_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1474_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1475_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1476_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1477_: u8 = 0;
    let mut v_isSharedCheck_1478_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_1448_) == 0 {
                    leanh::lean_dec_ref(v___x_1447_);
                    v_a_1450_ = leanh::lean_ctor_get(v_x_1448_, 0);
                    v_isSharedCheck_1458_ = (!leanh::lean_is_exclusive(v_x_1448_)) as u8;
                    if v_isSharedCheck_1458_ == 0 {
                        v___x_1452_ = v_x_1448_;
                        v_isShared_1453_ = v_isSharedCheck_1458_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_1450_);
                        leanh::lean_dec(v_x_1448_);
                        v___x_1452_ = leanh::lean_box(0);
                        v_isShared_1453_ = v_isSharedCheck_1458_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_1459_ = leanh::lean_ctor_get(v_x_1448_, 0);
                    v_isSharedCheck_1478_ = (!leanh::lean_is_exclusive(v_x_1448_)) as u8;
                    if v_isSharedCheck_1478_ == 0 {
                        v___x_1461_ = v_x_1448_;
                        v_isShared_1462_ = v_isSharedCheck_1478_;
                        state = 3;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_1459_);
                        leanh::lean_dec(v_x_1448_);
                        v___x_1461_ = leanh::lean_box(0);
                        v_isShared_1462_ = v_isSharedCheck_1478_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_1453_ == 0 {
                    v___x_1455_ = v___x_1452_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1457_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1457_, 0, v_a_1450_);
                    v___x_1455_ = v_reuseFailAlloc_1457_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_1456_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_1456_, 0, v___x_1455_);
                return v___x_1456_;
            }
            3 => {
                v_line_1463_ = leanh::lean_ctor_get(v_a_1459_, 0);
                v_body_1464_ = leanh::lean_ctor_get(v_a_1459_, 1);
                v_extensions_1465_ = leanh::lean_ctor_get(v_a_1459_, 2);
                v_isSharedCheck_1477_ = (!leanh::lean_is_exclusive(v_a_1459_)) as u8;
                if v_isSharedCheck_1477_ == 0 {
                    v___x_1467_ = v_a_1459_;
                    v_isShared_1468_ = v_isSharedCheck_1477_;
                    state = 4;
                    continue;
                } else {
                    leanh::lean_inc(v_extensions_1465_);
                    leanh::lean_inc(v_body_1464_);
                    leanh::lean_inc(v_line_1463_);
                    leanh::lean_dec(v_a_1459_);
                    v___x_1467_ = leanh::lean_box(0);
                    v_isShared_1468_ = v_isSharedCheck_1477_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_1469_ = l_Std_Http_Body_Any_ofBody___redArg(v___x_1447_, v_body_1464_);
                if v_isShared_1468_ == 0 {
                    leanh::lean_ctor_set(v___x_1467_, 1, v___x_1469_);
                    v___x_1471_ = v___x_1467_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_1476_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1476_, 0, v_line_1463_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1476_, 1, v___x_1469_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1476_, 2, v_extensions_1465_);
                    v___x_1471_ = v_reuseFailAlloc_1476_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                if v_isShared_1462_ == 0 {
                    leanh::lean_ctor_set(v___x_1461_, 0, v___x_1471_);
                    v___x_1473_ = v___x_1461_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_1475_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1475_, 0, v___x_1471_);
                    v___x_1473_ = v_reuseFailAlloc_1475_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                v___x_1474_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_1474_, 0, v___x_1473_);
                return v___x_1474_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Http_Body_instCoeContextAsyncResponseFullAny___lam__0___boxed(
    mut v___x_1479_: *mut leanh::LeanObject,
    mut v_x_1480_: *mut leanh::LeanObject,
    mut v___y_1481_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1482_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1482_ =
        l_Std_Http_Body_instCoeContextAsyncResponseFullAny___lam__0(v___x_1479_, v_x_1480_);
    return v_res_1482_;
}
pub unsafe fn l_Std_Http_Body_instCoeContextAsyncResponseFullAny___lam__1(
    mut v___f_1483_: *mut leanh::LeanObject,
    mut v_action_1484_: *mut leanh::LeanObject,
    mut v___y_1485_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1487_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1488_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1489_: u8 = 0;
    let mut v___x_1490_: *mut leanh::LeanObject = core::ptr::null_mut();
    leanh::lean_inc_ref(v___y_1485_);
    v___x_1487_ =
        leanh::lean_apply_2(v_action_1484_, v___y_1485_, leanh::lean_box(0));
    v___x_1488_ = leanh::lean_unsigned_to_nat(0);
    v___x_1489_ = 0;
    v___x_1490_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(
        leanh::lean_box(0),
        leanh::lean_box(0),
        v___x_1488_,
        v___x_1489_,
        v___x_1487_,
        v___f_1483_,
    );
    return v___x_1490_;
}
pub unsafe fn l_Std_Http_Body_instCoeContextAsyncResponseFullAny___lam__1___boxed(
    mut v___f_1491_: *mut leanh::LeanObject,
    mut v_action_1492_: *mut leanh::LeanObject,
    mut v___y_1493_: *mut leanh::LeanObject,
    mut v___y_1494_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1495_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1495_ = l_Std_Http_Body_instCoeContextAsyncResponseFullAny___lam__1(
        v___f_1491_,
        v_action_1492_,
        v___y_1493_,
    );
    leanh::lean_dec_ref(v___y_1493_);
    return v_res_1495_;
}
pub unsafe fn l_Std_Http_Body_instCoeAsyncResponseFullContextAsyncAny___lam__1(
    mut v___f_1501_: *mut leanh::LeanObject,
    mut v_action_1502_: *mut leanh::LeanObject,
    mut v___y_1503_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1505_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1506_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1507_: u8 = 0;
    let mut v___x_1508_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1505_ = leanh::lean_apply_1(v_action_1502_, leanh::lean_box(0));
    v___x_1506_ = leanh::lean_unsigned_to_nat(0);
    v___x_1507_ = 0;
    v___x_1508_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(
        leanh::lean_box(0),
        leanh::lean_box(0),
        v___x_1506_,
        v___x_1507_,
        v___x_1505_,
        v___f_1501_,
    );
    return v___x_1508_;
}
pub unsafe fn l_Std_Http_Body_instCoeAsyncResponseFullContextAsyncAny___lam__1___boxed(
    mut v___f_1509_: *mut leanh::LeanObject,
    mut v_action_1510_: *mut leanh::LeanObject,
    mut v___y_1511_: *mut leanh::LeanObject,
    mut v___y_1512_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1513_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1513_ = l_Std_Http_Body_instCoeAsyncResponseFullContextAsyncAny___lam__1(
        v___f_1509_,
        v_action_1510_,
        v___y_1511_,
    );
    leanh::lean_dec_ref(v___y_1511_);
    return v_res_1513_;
}
pub unsafe fn l_Std_Http_Request_Builder_fromBytes___lam__0(
    mut v_builder_1517_: *mut leanh::LeanObject,
    mut v_x_1518_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_a_1520_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1522_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1523_: u8 = 0;
    let mut v___x_1525_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1526_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1527_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1528_: u8 = 0;
    let mut v_a_1529_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1531_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1532_: u8 = 0;
    let mut v___x_1533_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1535_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1536_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1537_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1538_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_1518_) == 0 {
                    v_a_1520_ = leanh::lean_ctor_get(v_x_1518_, 0);
                    v_isSharedCheck_1528_ = (!leanh::lean_is_exclusive(v_x_1518_)) as u8;
                    if v_isSharedCheck_1528_ == 0 {
                        v___x_1522_ = v_x_1518_;
                        v_isShared_1523_ = v_isSharedCheck_1528_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_1520_);
                        leanh::lean_dec(v_x_1518_);
                        v___x_1522_ = leanh::lean_box(0);
                        v_isShared_1523_ = v_isSharedCheck_1528_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_1529_ = leanh::lean_ctor_get(v_x_1518_, 0);
                    v_isSharedCheck_1538_ = (!leanh::lean_is_exclusive(v_x_1518_)) as u8;
                    if v_isSharedCheck_1538_ == 0 {
                        v___x_1531_ = v_x_1518_;
                        v_isShared_1532_ = v_isSharedCheck_1538_;
                        state = 3;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_1529_);
                        leanh::lean_dec(v_x_1518_);
                        v___x_1531_ = leanh::lean_box(0);
                        v_isShared_1532_ = v_isSharedCheck_1538_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_1523_ == 0 {
                    v___x_1525_ = v___x_1522_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1527_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1527_, 0, v_a_1520_);
                    v___x_1525_ = v_reuseFailAlloc_1527_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_1526_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_1526_, 0, v___x_1525_);
                return v___x_1526_;
            }
            3 => {
                v___x_1533_ = l_Std_Http_Request_Builder_body___redArg(v_builder_1517_, v_a_1529_);
                if v_isShared_1532_ == 0 {
                    leanh::lean_ctor_set(v___x_1531_, 0, v___x_1533_);
                    v___x_1535_ = v___x_1531_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1537_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1537_, 0, v___x_1533_);
                    v___x_1535_ = v_reuseFailAlloc_1537_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_1536_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_1536_, 0, v___x_1535_);
                return v___x_1536_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Http_Request_Builder_fromBytes___lam__0___boxed(
    mut v_builder_1539_: *mut leanh::LeanObject,
    mut v_x_1540_: *mut leanh::LeanObject,
    mut v___y_1541_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1542_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1542_ = l_Std_Http_Request_Builder_fromBytes___lam__0(v_builder_1539_, v_x_1540_);
    leanh::lean_dec_ref(v_builder_1539_);
    return v_res_1542_;
}
pub unsafe fn l_Std_Http_Request_Builder_fromBytes(
    mut v_builder_1543_: *mut leanh::LeanObject,
    mut v_content_1544_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1546_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1547_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1548_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1549_: u8 = 0;
    let mut v___x_1550_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1546_ = l_Std_Http_Body_Full_ofByteArray(v_content_1544_);
    v___f_1547_ = leanh::lean_alloc_closure(
        l_Std_Http_Request_Builder_fromBytes___lam__0___boxed as *mut core::ffi::c_void,
        3,
        1,
    );
    leanh::lean_closure_set(v___f_1547_, 0, v_builder_1543_);
    v___x_1548_ = leanh::lean_unsigned_to_nat(0);
    v___x_1549_ = 0;
    v___x_1550_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(
        leanh::lean_box(0),
        leanh::lean_box(0),
        v___x_1548_,
        v___x_1549_,
        v___x_1546_,
        v___f_1547_,
    );
    return v___x_1550_;
}
pub unsafe fn l_Std_Http_Request_Builder_fromBytes___boxed(
    mut v_builder_1551_: *mut leanh::LeanObject,
    mut v_content_1552_: *mut leanh::LeanObject,
    mut v_a_1553_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1554_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1554_ = l_Std_Http_Request_Builder_fromBytes(v_builder_1551_, v_content_1552_);
    return v_res_1554_;
}
pub unsafe fn _init_l_Std_Http_Request_Builder_bytes___closed__1() -> *mut leanh::LeanObject
{
    let mut v___x_1556_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1557_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1556_ = l_Std_Http_Request_Builder_bytes___closed__0;
    v___x_1557_ = l_Std_Http_Header_Value_ofString_x21(v___x_1556_);
    return v___x_1557_;
}
pub unsafe fn l_Std_Http_Request_Builder_bytes(
    mut v_builder_1558_: *mut leanh::LeanObject,
    mut v_content_1559_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1561_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1562_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1563_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1564_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1561_ = l_Std_Http_Header_Name_contentType;
    v___x_1562_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Http_Request_Builder_bytes___closed__1),
        core::ptr::addr_of_mut!(l_Std_Http_Request_Builder_bytes___closed__1_once),
        _init_l_Std_Http_Request_Builder_bytes___closed__1,
    );
    v___x_1563_ = l_Std_Http_Request_Builder_header(v_builder_1558_, v___x_1561_, v___x_1562_);
    v___x_1564_ = l_Std_Http_Request_Builder_fromBytes(v___x_1563_, v_content_1559_);
    return v___x_1564_;
}
pub unsafe fn l_Std_Http_Request_Builder_bytes___boxed(
    mut v_builder_1565_: *mut leanh::LeanObject,
    mut v_content_1566_: *mut leanh::LeanObject,
    mut v_a_1567_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1568_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1568_ = l_Std_Http_Request_Builder_bytes(v_builder_1565_, v_content_1566_);
    return v_res_1568_;
}
pub unsafe fn _init_l_Std_Http_Request_Builder_text___closed__1() -> *mut leanh::LeanObject {
    let mut v___x_1570_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1571_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1570_ = l_Std_Http_Request_Builder_text___closed__0;
    v___x_1571_ = l_Std_Http_Header_Value_ofString_x21(v___x_1570_);
    return v___x_1571_;
}
pub unsafe fn l_Std_Http_Request_Builder_text(
    mut v_builder_1572_: *mut leanh::LeanObject,
    mut v_content_1573_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1575_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1576_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1577_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1578_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1579_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1575_ = l_Std_Http_Header_Name_contentType;
    v___x_1576_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Http_Request_Builder_text___closed__1),
        core::ptr::addr_of_mut!(l_Std_Http_Request_Builder_text___closed__1_once),
        _init_l_Std_Http_Request_Builder_text___closed__1,
    );
    v___x_1577_ = l_Std_Http_Request_Builder_header(v_builder_1572_, v___x_1575_, v___x_1576_);
    v___x_1578_ = lean_string_to_utf8(v_content_1573_);
    v___x_1579_ = l_Std_Http_Request_Builder_fromBytes(v___x_1577_, v___x_1578_);
    return v___x_1579_;
}
pub unsafe fn l_Std_Http_Request_Builder_text___boxed(
    mut v_builder_1580_: *mut leanh::LeanObject,
    mut v_content_1581_: *mut leanh::LeanObject,
    mut v_a_1582_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1583_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1583_ = l_Std_Http_Request_Builder_text(v_builder_1580_, v_content_1581_);
    leanh::lean_dec_ref(v_content_1581_);
    return v_res_1583_;
}
pub unsafe fn _init_l_Std_Http_Request_Builder_json___closed__1() -> *mut leanh::LeanObject {
    let mut v___x_1585_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1586_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1585_ = l_Std_Http_Request_Builder_json___closed__0;
    v___x_1586_ = l_Std_Http_Header_Value_ofString_x21(v___x_1585_);
    return v___x_1586_;
}
pub unsafe fn l_Std_Http_Request_Builder_json(
    mut v_builder_1587_: *mut leanh::LeanObject,
    mut v_content_1588_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1590_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1591_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1592_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1593_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1594_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1590_ = l_Std_Http_Header_Name_contentType;
    v___x_1591_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Http_Request_Builder_json___closed__1),
        core::ptr::addr_of_mut!(l_Std_Http_Request_Builder_json___closed__1_once),
        _init_l_Std_Http_Request_Builder_json___closed__1,
    );
    v___x_1592_ = l_Std_Http_Request_Builder_header(v_builder_1587_, v___x_1590_, v___x_1591_);
    v___x_1593_ = lean_string_to_utf8(v_content_1588_);
    v___x_1594_ = l_Std_Http_Request_Builder_fromBytes(v___x_1592_, v___x_1593_);
    return v___x_1594_;
}
pub unsafe fn l_Std_Http_Request_Builder_json___boxed(
    mut v_builder_1595_: *mut leanh::LeanObject,
    mut v_content_1596_: *mut leanh::LeanObject,
    mut v_a_1597_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1598_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1598_ = l_Std_Http_Request_Builder_json(v_builder_1595_, v_content_1596_);
    leanh::lean_dec_ref(v_content_1596_);
    return v_res_1598_;
}
pub unsafe fn _init_l_Std_Http_Request_Builder_html___closed__1() -> *mut leanh::LeanObject {
    let mut v___x_1600_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1601_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1600_ = l_Std_Http_Request_Builder_html___closed__0;
    v___x_1601_ = l_Std_Http_Header_Value_ofString_x21(v___x_1600_);
    return v___x_1601_;
}
pub unsafe fn l_Std_Http_Request_Builder_html(
    mut v_builder_1602_: *mut leanh::LeanObject,
    mut v_content_1603_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1605_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1606_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1607_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1608_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1609_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1605_ = l_Std_Http_Header_Name_contentType;
    v___x_1606_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Http_Request_Builder_html___closed__1),
        core::ptr::addr_of_mut!(l_Std_Http_Request_Builder_html___closed__1_once),
        _init_l_Std_Http_Request_Builder_html___closed__1,
    );
    v___x_1607_ = l_Std_Http_Request_Builder_header(v_builder_1602_, v___x_1605_, v___x_1606_);
    v___x_1608_ = lean_string_to_utf8(v_content_1603_);
    v___x_1609_ = l_Std_Http_Request_Builder_fromBytes(v___x_1607_, v___x_1608_);
    return v___x_1609_;
}
pub unsafe fn l_Std_Http_Request_Builder_html___boxed(
    mut v_builder_1610_: *mut leanh::LeanObject,
    mut v_content_1611_: *mut leanh::LeanObject,
    mut v_a_1612_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1613_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1613_ = l_Std_Http_Request_Builder_html(v_builder_1610_, v_content_1611_);
    leanh::lean_dec_ref(v_content_1611_);
    return v_res_1613_;
}
pub unsafe fn l_Std_Http_Response_Builder_fromBytes___lam__0(
    mut v_builder_1614_: *mut leanh::LeanObject,
    mut v_x_1615_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_a_1617_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1619_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1620_: u8 = 0;
    let mut v___x_1622_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1623_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1624_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1625_: u8 = 0;
    let mut v_a_1626_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1628_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1629_: u8 = 0;
    let mut v___x_1630_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1632_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1633_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1634_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1635_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_1615_) == 0 {
                    v_a_1617_ = leanh::lean_ctor_get(v_x_1615_, 0);
                    v_isSharedCheck_1625_ = (!leanh::lean_is_exclusive(v_x_1615_)) as u8;
                    if v_isSharedCheck_1625_ == 0 {
                        v___x_1619_ = v_x_1615_;
                        v_isShared_1620_ = v_isSharedCheck_1625_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_1617_);
                        leanh::lean_dec(v_x_1615_);
                        v___x_1619_ = leanh::lean_box(0);
                        v_isShared_1620_ = v_isSharedCheck_1625_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_1626_ = leanh::lean_ctor_get(v_x_1615_, 0);
                    v_isSharedCheck_1635_ = (!leanh::lean_is_exclusive(v_x_1615_)) as u8;
                    if v_isSharedCheck_1635_ == 0 {
                        v___x_1628_ = v_x_1615_;
                        v_isShared_1629_ = v_isSharedCheck_1635_;
                        state = 3;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_1626_);
                        leanh::lean_dec(v_x_1615_);
                        v___x_1628_ = leanh::lean_box(0);
                        v_isShared_1629_ = v_isSharedCheck_1635_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_1620_ == 0 {
                    v___x_1622_ = v___x_1619_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1624_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1624_, 0, v_a_1617_);
                    v___x_1622_ = v_reuseFailAlloc_1624_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_1623_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_1623_, 0, v___x_1622_);
                return v___x_1623_;
            }
            3 => {
                v___x_1630_ = l_Std_Http_Response_Builder_body___redArg(v_builder_1614_, v_a_1626_);
                if v_isShared_1629_ == 0 {
                    leanh::lean_ctor_set(v___x_1628_, 0, v___x_1630_);
                    v___x_1632_ = v___x_1628_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1634_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1634_, 0, v___x_1630_);
                    v___x_1632_ = v_reuseFailAlloc_1634_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_1633_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_1633_, 0, v___x_1632_);
                return v___x_1633_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Http_Response_Builder_fromBytes___lam__0___boxed(
    mut v_builder_1636_: *mut leanh::LeanObject,
    mut v_x_1637_: *mut leanh::LeanObject,
    mut v___y_1638_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1639_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1639_ = l_Std_Http_Response_Builder_fromBytes___lam__0(v_builder_1636_, v_x_1637_);
    leanh::lean_dec_ref(v_builder_1636_);
    return v_res_1639_;
}
pub unsafe fn l_Std_Http_Response_Builder_fromBytes(
    mut v_builder_1640_: *mut leanh::LeanObject,
    mut v_content_1641_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1643_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1644_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1645_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1646_: u8 = 0;
    let mut v___x_1647_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1643_ = l_Std_Http_Body_Full_ofByteArray(v_content_1641_);
    v___f_1644_ = leanh::lean_alloc_closure(
        l_Std_Http_Response_Builder_fromBytes___lam__0___boxed as *mut core::ffi::c_void,
        3,
        1,
    );
    leanh::lean_closure_set(v___f_1644_, 0, v_builder_1640_);
    v___x_1645_ = leanh::lean_unsigned_to_nat(0);
    v___x_1646_ = 0;
    v___x_1647_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(
        leanh::lean_box(0),
        leanh::lean_box(0),
        v___x_1645_,
        v___x_1646_,
        v___x_1643_,
        v___f_1644_,
    );
    return v___x_1647_;
}
pub unsafe fn l_Std_Http_Response_Builder_fromBytes___boxed(
    mut v_builder_1648_: *mut leanh::LeanObject,
    mut v_content_1649_: *mut leanh::LeanObject,
    mut v_a_1650_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1651_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1651_ = l_Std_Http_Response_Builder_fromBytes(v_builder_1648_, v_content_1649_);
    return v_res_1651_;
}
pub unsafe fn l_Std_Http_Response_Builder_bytes(
    mut v_builder_1652_: *mut leanh::LeanObject,
    mut v_content_1653_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1655_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1656_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1657_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1658_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1655_ = l_Std_Http_Header_Name_contentType;
    v___x_1656_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Http_Request_Builder_bytes___closed__1),
        core::ptr::addr_of_mut!(l_Std_Http_Request_Builder_bytes___closed__1_once),
        _init_l_Std_Http_Request_Builder_bytes___closed__1,
    );
    v___x_1657_ = l_Std_Http_Response_Builder_header(v_builder_1652_, v___x_1655_, v___x_1656_);
    v___x_1658_ = l_Std_Http_Response_Builder_fromBytes(v___x_1657_, v_content_1653_);
    return v___x_1658_;
}
pub unsafe fn l_Std_Http_Response_Builder_bytes___boxed(
    mut v_builder_1659_: *mut leanh::LeanObject,
    mut v_content_1660_: *mut leanh::LeanObject,
    mut v_a_1661_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1662_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1662_ = l_Std_Http_Response_Builder_bytes(v_builder_1659_, v_content_1660_);
    return v_res_1662_;
}
pub unsafe fn l_Std_Http_Response_Builder_text(
    mut v_builder_1663_: *mut leanh::LeanObject,
    mut v_content_1664_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1666_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1667_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1668_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1669_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1670_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1666_ = l_Std_Http_Header_Name_contentType;
    v___x_1667_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Http_Request_Builder_text___closed__1),
        core::ptr::addr_of_mut!(l_Std_Http_Request_Builder_text___closed__1_once),
        _init_l_Std_Http_Request_Builder_text___closed__1,
    );
    v___x_1668_ = l_Std_Http_Response_Builder_header(v_builder_1663_, v___x_1666_, v___x_1667_);
    v___x_1669_ = lean_string_to_utf8(v_content_1664_);
    v___x_1670_ = l_Std_Http_Response_Builder_fromBytes(v___x_1668_, v___x_1669_);
    return v___x_1670_;
}
pub unsafe fn l_Std_Http_Response_Builder_text___boxed(
    mut v_builder_1671_: *mut leanh::LeanObject,
    mut v_content_1672_: *mut leanh::LeanObject,
    mut v_a_1673_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1674_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1674_ = l_Std_Http_Response_Builder_text(v_builder_1671_, v_content_1672_);
    leanh::lean_dec_ref(v_content_1672_);
    return v_res_1674_;
}
pub unsafe fn l_Std_Http_Response_Builder_json(
    mut v_builder_1675_: *mut leanh::LeanObject,
    mut v_content_1676_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1678_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1679_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1680_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1681_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1682_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1678_ = l_Std_Http_Header_Name_contentType;
    v___x_1679_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Http_Request_Builder_json___closed__1),
        core::ptr::addr_of_mut!(l_Std_Http_Request_Builder_json___closed__1_once),
        _init_l_Std_Http_Request_Builder_json___closed__1,
    );
    v___x_1680_ = l_Std_Http_Response_Builder_header(v_builder_1675_, v___x_1678_, v___x_1679_);
    v___x_1681_ = lean_string_to_utf8(v_content_1676_);
    v___x_1682_ = l_Std_Http_Response_Builder_fromBytes(v___x_1680_, v___x_1681_);
    return v___x_1682_;
}
pub unsafe fn l_Std_Http_Response_Builder_json___boxed(
    mut v_builder_1683_: *mut leanh::LeanObject,
    mut v_content_1684_: *mut leanh::LeanObject,
    mut v_a_1685_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1686_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1686_ = l_Std_Http_Response_Builder_json(v_builder_1683_, v_content_1684_);
    leanh::lean_dec_ref(v_content_1684_);
    return v_res_1686_;
}
pub unsafe fn l_Std_Http_Response_Builder_html(
    mut v_builder_1687_: *mut leanh::LeanObject,
    mut v_content_1688_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1690_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1691_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1692_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1693_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1694_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1690_ = l_Std_Http_Header_Name_contentType;
    v___x_1691_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Http_Request_Builder_html___closed__1),
        core::ptr::addr_of_mut!(l_Std_Http_Request_Builder_html___closed__1_once),
        _init_l_Std_Http_Request_Builder_html___closed__1,
    );
    v___x_1692_ = l_Std_Http_Response_Builder_header(v_builder_1687_, v___x_1690_, v___x_1691_);
    v___x_1693_ = lean_string_to_utf8(v_content_1688_);
    v___x_1694_ = l_Std_Http_Response_Builder_fromBytes(v___x_1692_, v___x_1693_);
    return v___x_1694_;
}
pub unsafe fn l_Std_Http_Response_Builder_html___boxed(
    mut v_builder_1695_: *mut leanh::LeanObject,
    mut v_content_1696_: *mut leanh::LeanObject,
    mut v_a_1697_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1698_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1698_ = l_Std_Http_Response_Builder_html(v_builder_1695_, v_content_1696_);
    leanh::lean_dec_ref(v_content_1696_);
    return v_res_1698_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Std_Http_Data_Body_Full(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Std_Sync(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
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
    res = runtime_initialize_Init_Data_ByteArray(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Std_Http_Data_Body_Full(
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
pub unsafe fn initialize_Std_Http_Data_Body_Full(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Std_Sync(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
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
    res = initialize_Init_Data_ByteArray(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Std_Http_Data_Body_Full(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = meta_initialize_Std_Http_Data_Body_Full(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return initialize_Std_Http_Data_Body_Full(builtin);
}