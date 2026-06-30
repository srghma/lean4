// Lean compiler output
// Module: Std.Sync.CancellationToken
// Imports: Std.Data Init.Data.Queue Std.Sync.Mutex Std.Async.Select Init.Data.ToString.Macro
use crate::ffi::{
    lean_io_basemutex_lock, lean_io_basemutex_unlock, lean_io_bind_task, lean_io_promise_new,
    lean_io_promise_resolve, lean_io_promise_result_opt, lean_nat_dec_le, lean_nat_to_int,
    lean_st_ref_get, lean_st_ref_set, lean_st_ref_take, lean_string_append, lean_string_dec_eq,
    lean_task_map, lean_task_pure,
};
use crate::r#gen::Init::Data::List::Basic::{l_List_isEmpty___redArg, l_List_reverse___redArg};
use crate::r#gen::Init::Data::Queue::{
    initialize_Init_Data_Queue, l_Std_Queue_dequeue_x3f___redArg, l_Std_Queue_empty,
    l_Std_Queue_enqueue___redArg, runtime_initialize_Init_Data_Queue,
};
use crate::r#gen::Init::Data::Repr::{l_Repr_addAppParen, l_String_quote};
use crate::r#gen::Init::Data::ToString::Macro::{
    initialize_Init_Data_ToString_Macro, runtime_initialize_Init_Data_ToString_Macro,
};
use crate::r#gen::Init::System::IOError::lean_mk_io_user_error;
use crate::r#gen::Std::Async::Basic::{
    l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask,
    l_Std_Async_EAsync_tryFinally_x27___redArg,
};
use crate::r#gen::Std::Async::Select::{
    initialize_Std_Async_Select, runtime_initialize_Std_Async_Select,
};
use crate::r#gen::Std::Data::{initialize_Std_Data, runtime_initialize_Std_Data};
use crate::r#gen::Std::Sync::Mutex::{
    initialize_Std_Sync_Mutex, l_Std_Mutex_new___redArg, runtime_initialize_Std_Sync_Mutex,
};
pub static l_Std_instReprCancellationReason_repr___closed__0_value: leanh::LeanStringObject<
    30,
> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 30,
    m_capacity: 30,
    m_length: 29,
    m_data: [
        83, 116, 100, 46, 67, 97, 110, 99, 101, 108, 108, 97, 116, 105, 111, 110, 82, 101, 97, 115,
        111, 110, 46, 99, 97, 110, 99, 101, 108, 0,
    ],
};
static mut l_Std_instReprCancellationReason_repr___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_instReprCancellationReason_repr___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Std_instReprCancellationReason_repr___closed__1_value: leanh::LeanCtorObject<
    1,
> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [
        core::ptr::addr_of!(l_Std_instReprCancellationReason_repr___closed__0_value)
            as *mut leanh::LeanObject,
    ],
};
static mut l_Std_instReprCancellationReason_repr___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_instReprCancellationReason_repr___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Std_instReprCancellationReason_repr___closed__2_value: leanh::LeanStringObject<
    32,
> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 32,
    m_capacity: 32,
    m_length: 31,
    m_data: [
        83, 116, 100, 46, 67, 97, 110, 99, 101, 108, 108, 97, 116, 105, 111, 110, 82, 101, 97, 115,
        111, 110, 46, 115, 104, 117, 116, 100, 111, 119, 110, 0,
    ],
};
static mut l_Std_instReprCancellationReason_repr___closed__2: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_instReprCancellationReason_repr___closed__2_value)
        as *mut leanh::LeanObject;
pub static l_Std_instReprCancellationReason_repr___closed__3_value: leanh::LeanCtorObject<
    1,
> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [
        core::ptr::addr_of!(l_Std_instReprCancellationReason_repr___closed__2_value)
            as *mut leanh::LeanObject,
    ],
};
static mut l_Std_instReprCancellationReason_repr___closed__3: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_instReprCancellationReason_repr___closed__3_value)
        as *mut leanh::LeanObject;
pub static l_Std_instReprCancellationReason_repr___closed__4_value: leanh::LeanStringObject<
    32,
> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 32,
    m_capacity: 32,
    m_length: 31,
    m_data: [
        83, 116, 100, 46, 67, 97, 110, 99, 101, 108, 108, 97, 116, 105, 111, 110, 82, 101, 97, 115,
        111, 110, 46, 100, 101, 97, 100, 108, 105, 110, 101, 0,
    ],
};
static mut l_Std_instReprCancellationReason_repr___closed__4: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_instReprCancellationReason_repr___closed__4_value)
        as *mut leanh::LeanObject;
pub static l_Std_instReprCancellationReason_repr___closed__5_value: leanh::LeanCtorObject<
    1,
> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [
        core::ptr::addr_of!(l_Std_instReprCancellationReason_repr___closed__4_value)
            as *mut leanh::LeanObject,
    ],
};
static mut l_Std_instReprCancellationReason_repr___closed__5: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_instReprCancellationReason_repr___closed__5_value)
        as *mut leanh::LeanObject;
static mut l_Std_instReprCancellationReason_repr___closed__6_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_instReprCancellationReason_repr___closed__6: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_instReprCancellationReason_repr___closed__7_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_instReprCancellationReason_repr___closed__7: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Std_instReprCancellationReason_repr___closed__8_value: leanh::LeanStringObject<
    30,
> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 30,
    m_capacity: 30,
    m_length: 29,
    m_data: [
        83, 116, 100, 46, 67, 97, 110, 99, 101, 108, 108, 97, 116, 105, 111, 110, 82, 101, 97, 115,
        111, 110, 46, 99, 117, 115, 116, 111, 109, 0,
    ],
};
static mut l_Std_instReprCancellationReason_repr___closed__8: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_instReprCancellationReason_repr___closed__8_value)
        as *mut leanh::LeanObject;
pub static l_Std_instReprCancellationReason_repr___closed__9_value: leanh::LeanCtorObject<
    1,
> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [
        core::ptr::addr_of!(l_Std_instReprCancellationReason_repr___closed__8_value)
            as *mut leanh::LeanObject,
    ],
};
static mut l_Std_instReprCancellationReason_repr___closed__9: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_instReprCancellationReason_repr___closed__9_value)
        as *mut leanh::LeanObject;
pub static l_Std_instReprCancellationReason_repr___closed__10_value: leanh::LeanCtorObject<
    2,
> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 5,
    },
    m_objs: [
        core::ptr::addr_of!(l_Std_instReprCancellationReason_repr___closed__9_value)
            as *mut leanh::LeanObject,
        (((1 as usize) << 1) | 1) as *mut leanh::LeanObject,
    ],
};
static mut l_Std_instReprCancellationReason_repr___closed__10: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_instReprCancellationReason_repr___closed__10_value)
        as *mut leanh::LeanObject;
pub static l_Std_instReprCancellationReason___closed__0_value: leanh::LeanClosureObject<0> =
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
        m_fun: l_Std_instReprCancellationReason_repr___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Std_instReprCancellationReason___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_instReprCancellationReason___closed__0_value)
        as *mut leanh::LeanObject;
pub static mut l_Std_instReprCancellationReason: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_instReprCancellationReason___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Std_instBEqCancellationReason___closed__0_value: leanh::LeanClosureObject<0> =
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
        m_fun: l_Std_instBEqCancellationReason_beq___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Std_instBEqCancellationReason___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_instBEqCancellationReason___closed__0_value)
        as *mut leanh::LeanObject;
pub static mut l_Std_instBEqCancellationReason: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_instBEqCancellationReason___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Std_instToStringCancellationReason___lam__0___closed__0_value:
    leanh::LeanStringObject<9> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 9,
    m_capacity: 9,
    m_length: 8,
    m_data: [100, 101, 97, 100, 108, 105, 110, 101, 0],
};
static mut l_Std_instToStringCancellationReason___lam__0___closed__0:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_instToStringCancellationReason___lam__0___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Std_instToStringCancellationReason___lam__0___closed__1_value:
    leanh::LeanStringObject<9> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 9,
    m_capacity: 9,
    m_length: 8,
    m_data: [115, 104, 117, 116, 100, 111, 119, 110, 0],
};
static mut l_Std_instToStringCancellationReason___lam__0___closed__1:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_instToStringCancellationReason___lam__0___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Std_instToStringCancellationReason___lam__0___closed__2_value:
    leanh::LeanStringObject<7> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 7,
    m_capacity: 7,
    m_length: 6,
    m_data: [99, 97, 110, 99, 101, 108, 0],
};
static mut l_Std_instToStringCancellationReason___lam__0___closed__2:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_instToStringCancellationReason___lam__0___closed__2_value)
        as *mut leanh::LeanObject;
pub static l_Std_instToStringCancellationReason___lam__0___closed__3_value:
    leanh::LeanStringObject<9> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 9,
    m_capacity: 9,
    m_length: 8,
    m_data: [99, 117, 115, 116, 111, 109, 40, 34, 0],
};
static mut l_Std_instToStringCancellationReason___lam__0___closed__3:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_instToStringCancellationReason___lam__0___closed__3_value)
        as *mut leanh::LeanObject;
pub static l_Std_instToStringCancellationReason___lam__0___closed__4_value:
    leanh::LeanStringObject<3> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 3,
    m_capacity: 3,
    m_length: 2,
    m_data: [34, 41, 0],
};
static mut l_Std_instToStringCancellationReason___lam__0___closed__4:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_instToStringCancellationReason___lam__0___closed__4_value)
        as *mut leanh::LeanObject;
pub static l_Std_instToStringCancellationReason___closed__0_value: leanh::LeanClosureObject<
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
    m_fun: l_Std_instToStringCancellationReason___lam__0___boxed as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_instToStringCancellationReason___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_instToStringCancellationReason___closed__0_value)
        as *mut leanh::LeanObject;
pub static mut l_Std_instToStringCancellationReason: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_instToStringCancellationReason___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Std_Async_Waiter_race___at___00Std_CancellationToken_Consumer_resolve_spec__0___closed__0_value: leanh::LeanCtorObject<1> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject] };
static mut l_Std_Async_Waiter_race___at___00Std_CancellationToken_Consumer_resolve_spec__0___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l_Std_Async_Waiter_race___at___00Std_CancellationToken_Consumer_resolve_spec__0___closed__0_value) as *mut leanh::LeanObject;
pub static l_Std_CancellationToken_Consumer_resolve___closed__0_value:
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
    m_fun: l_Std_CancellationToken_Consumer_resolve___lam__0___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 1,
    m_objs: [(((0 as usize) << 1) | 1) as *mut leanh::LeanObject],
};
static mut l_Std_CancellationToken_Consumer_resolve___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_CancellationToken_Consumer_resolve___closed__0_value)
        as *mut leanh::LeanObject;
static mut l_Std_CancellationToken_new___closed__0_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_CancellationToken_new___closed__0: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_CancellationToken_new___closed__1_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_CancellationToken_new___closed__1: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Std_CancellationToken_isCancelled___closed__0_value: leanh::LeanClosureObject<
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
    m_fun: l_Std_CancellationToken_isCancelled___lam__0___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_CancellationToken_isCancelled___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_CancellationToken_isCancelled___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Std_CancellationToken_getCancellationReason___closed__0_value:
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
    m_fun: l_Std_CancellationToken_getCancellationReason___lam__0___boxed
        as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_CancellationToken_getCancellationReason___closed__0:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_CancellationToken_getCancellationReason___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Std_CancellationToken_wait___lam__0___closed__0_value: leanh::LeanStringObject<
    27,
> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 27,
    m_capacity: 27,
    m_length: 26,
    m_data: [
        99, 97, 110, 99, 101, 108, 108, 97, 116, 105, 111, 110, 32, 116, 111, 107, 101, 110, 32,
        100, 114, 111, 112, 112, 101, 100, 0,
    ],
};
static mut l_Std_CancellationToken_wait___lam__0___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_CancellationToken_wait___lam__0___closed__0_value)
        as *mut leanh::LeanObject;
static mut l_Std_CancellationToken_wait___lam__0___closed__1_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_CancellationToken_wait___lam__0___closed__1: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_CancellationToken_wait___lam__0___closed__2_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_CancellationToken_wait___lam__0___closed__2: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_CancellationToken_wait___lam__0___closed__3_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_CancellationToken_wait___lam__0___closed__3: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_CancellationToken_wait___lam__0___closed__4_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_CancellationToken_wait___lam__0___closed__4: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Std_CancellationToken_wait___closed__0_value: leanh::LeanClosureObject<0> =
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
        m_fun: l_Std_CancellationToken_wait___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Std_CancellationToken_wait___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_CancellationToken_wait___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Std_CancellationToken_wait___closed__1_value: leanh::LeanClosureObject<1> =
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
        m_fun: l_Std_CancellationToken_wait___lam__1___boxed as *const core::ffi::c_void,
        m_arity: 3,
        m_num_fixed: 1,
        m_objs: [
            core::ptr::addr_of!(l_Std_CancellationToken_wait___closed__0_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Std_CancellationToken_wait___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_CancellationToken_wait___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Std_Async_Waiter_race___at___00Std_CancellationToken_selector_spec__0___closed__0_value: leanh::LeanClosureObject<1> = leanh::LeanClosureObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut leanh::LeanObject>()*1) as u16, other: 0, tag: 245 }, m_fun: l_Std_Async_Waiter_race___at___00Std_CancellationToken_selector_spec__0___lam__0___boxed as *const core::ffi::c_void, m_arity: 3, m_num_fixed: 1, m_objs: [((( 1 as usize) << 1) | 1) as *mut leanh::LeanObject] };
static mut l_Std_Async_Waiter_race___at___00Std_CancellationToken_selector_spec__0___closed__0:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Std_Async_Waiter_race___at___00Std_CancellationToken_selector_spec__0___closed__0_value
) as *mut leanh::LeanObject;
pub static l_Std_Mutex_atomically___at___00Std_CancellationToken_selector_spec__1___redArg___closed__0_value: leanh::LeanClosureObject<0> = leanh::LeanClosureObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Std_Mutex_atomically___at___00Std_CancellationToken_selector_spec__1___redArg___lam__3 as *const core::ffi::c_void, m_arity: 1, m_num_fixed: 0, m_objs: [] };
static mut l_Std_Mutex_atomically___at___00Std_CancellationToken_selector_spec__1___redArg___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l_Std_Mutex_atomically___at___00Std_CancellationToken_selector_spec__1___redArg___closed__0_value) as *mut leanh::LeanObject;
pub static l_Std_CancellationToken_selector___lam__2___closed__0_value: leanh::LeanCtorObject<1> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 0 }, m_objs: [core::ptr::addr_of!(l_Std_Async_Waiter_race___at___00Std_CancellationToken_Consumer_resolve_spec__0___closed__0_value) as *mut leanh::LeanObject] };
static mut l_Std_CancellationToken_selector___lam__2___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_CancellationToken_selector___lam__2___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Std_CancellationToken_selector___lam__2___closed__1_value:
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
    m_fun: l_Std_CancellationToken_selector___lam__0___boxed as *const core::ffi::c_void,
    m_arity: 3,
    m_num_fixed: 1,
    m_objs: [(((0 as usize) << 1) | 1) as *mut leanh::LeanObject],
};
static mut l_Std_CancellationToken_selector___lam__2___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_CancellationToken_selector___lam__2___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Std_CancellationToken_selector___lam__2___closed__2_value:
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
    m_fun: l_Std_CancellationToken_selector___lam__1 as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 1,
    m_objs: [(((0 as usize) << 1) | 1) as *mut leanh::LeanObject],
};
static mut l_Std_CancellationToken_selector___lam__2___closed__2: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_CancellationToken_selector___lam__2___closed__2_value)
        as *mut leanh::LeanObject;
pub static l_Std_CancellationToken_selector___lam__5___closed__0_value:
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
static mut l_Std_CancellationToken_selector___lam__5___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_CancellationToken_selector___lam__5___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Std_CancellationToken_selector___lam__5___closed__1_value:
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
        core::ptr::addr_of!(l_Std_CancellationToken_selector___lam__5___closed__0_value)
            as *mut leanh::LeanObject,
    ],
};
static mut l_Std_CancellationToken_selector___lam__5___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_CancellationToken_selector___lam__5___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Std_CancellationToken_selector___lam__5___closed__2_value:
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
static mut l_Std_CancellationToken_selector___lam__5___closed__2: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_CancellationToken_selector___lam__5___closed__2_value)
        as *mut leanh::LeanObject;
pub static l_Std_CancellationToken_selector___lam__5___closed__3_value:
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
        core::ptr::addr_of!(l_Std_CancellationToken_selector___lam__5___closed__2_value)
            as *mut leanh::LeanObject,
    ],
};
static mut l_Std_CancellationToken_selector___lam__5___closed__3: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_CancellationToken_selector___lam__5___closed__3_value)
        as *mut leanh::LeanObject;
pub static l_Std_CancellationToken_selector___lam__5___closed__4_value:
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
        core::ptr::addr_of!(l_Std_CancellationToken_selector___lam__5___closed__3_value)
            as *mut leanh::LeanObject,
    ],
};
static mut l_Std_CancellationToken_selector___lam__5___closed__4: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_CancellationToken_selector___lam__5___closed__4_value)
        as *mut leanh::LeanObject;
pub static l_List_filterAuxM___at___00Std_Queue_filterM___at___00Std_CancellationToken_selector_spec__2_spec__2___redArg___closed__0_value: leanh::LeanCtorObject<1> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 1 }, m_objs: [((( 1 as usize) << 1) | 1) as *mut leanh::LeanObject] };
static mut l_List_filterAuxM___at___00Std_Queue_filterM___at___00Std_CancellationToken_selector_spec__2_spec__2___redArg___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l_List_filterAuxM___at___00Std_Queue_filterM___at___00Std_CancellationToken_selector_spec__2_spec__2___redArg___closed__0_value) as *mut leanh::LeanObject;
pub static l_List_filterAuxM___at___00Std_Queue_filterM___at___00Std_CancellationToken_selector_spec__2_spec__2___redArg___closed__1_value: leanh::LeanCtorObject<1> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 0 }, m_objs: [core::ptr::addr_of!(l_List_filterAuxM___at___00Std_Queue_filterM___at___00Std_CancellationToken_selector_spec__2_spec__2___redArg___closed__0_value) as *mut leanh::LeanObject] };
static mut l_List_filterAuxM___at___00Std_Queue_filterM___at___00Std_CancellationToken_selector_spec__2_spec__2___redArg___closed__1: *mut leanh::LeanObject = core::ptr::addr_of!(l_List_filterAuxM___at___00Std_Queue_filterM___at___00Std_CancellationToken_selector_spec__2_spec__2___redArg___closed__1_value) as *mut leanh::LeanObject;
pub static l_List_filterAuxM___at___00Std_Queue_filterM___at___00Std_CancellationToken_selector_spec__2_spec__2___redArg___closed__2_value: leanh::LeanClosureObject<0> = leanh::LeanClosureObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_List_filterAuxM___at___00Std_Queue_filterM___at___00Std_CancellationToken_selector_spec__2_spec__2___redArg___lam__1___boxed as *const core::ffi::c_void, m_arity: 2, m_num_fixed: 0, m_objs: [] };
static mut l_List_filterAuxM___at___00Std_Queue_filterM___at___00Std_CancellationToken_selector_spec__2_spec__2___redArg___closed__2: *mut leanh::LeanObject = core::ptr::addr_of!(l_List_filterAuxM___at___00Std_Queue_filterM___at___00Std_CancellationToken_selector_spec__2_spec__2___redArg___closed__2_value) as *mut leanh::LeanObject;
pub static l_Std_Queue_filterM___at___00Std_CancellationToken_selector_spec__2___closed__0_value:
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
    m_fun: l_Std_Queue_filterM___at___00Std_CancellationToken_selector_spec__2___lam__0___boxed
        as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_Queue_filterM___at___00Std_CancellationToken_selector_spec__2___closed__0:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Std_Queue_filterM___at___00Std_CancellationToken_selector_spec__2___closed__0_value
) as *mut leanh::LeanObject;
pub static l_Std_CancellationToken_selector___closed__0_value: leanh::LeanClosureObject<0> =
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
        m_fun: l_Std_CancellationToken_selector___lam__5___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Std_CancellationToken_selector___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_CancellationToken_selector___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Std_CancellationToken_selector___closed__1_value: leanh::LeanClosureObject<0> =
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
        m_fun: l_Std_CancellationToken_selector___lam__9___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Std_CancellationToken_selector___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_CancellationToken_selector___closed__1_value)
        as *mut leanh::LeanObject;
pub unsafe fn l_Std_CancellationReason_ctorIdx(
    mut v_x_1118_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    match leanh::lean_obj_tag(v_x_1118_) {
        0 => {
            let mut v___x_1119_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_1119_ = leanh::lean_unsigned_to_nat(0);
            return v___x_1119_;
        }
        1 => {
            let mut v___x_1120_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_1120_ = leanh::lean_unsigned_to_nat(1);
            return v___x_1120_;
        }
        2 => {
            let mut v___x_1121_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_1121_ = leanh::lean_unsigned_to_nat(2);
            return v___x_1121_;
        }
        _ => {
            let mut v___x_1122_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_1122_ = leanh::lean_unsigned_to_nat(3);
            return v___x_1122_;
        }
    }
}
pub unsafe fn l_Std_CancellationReason_ctorIdx___boxed(
    mut v_x_1123_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1124_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1124_ = l_Std_CancellationReason_ctorIdx(v_x_1123_);
    leanh::lean_dec(v_x_1123_);
    return v_res_1124_;
}
pub unsafe fn l_Std_CancellationReason_ctorElim___redArg(
    mut v_t_1125_: *mut leanh::LeanObject,
    mut v_k_1126_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_t_1125_) == 3 {
        let mut v_msg_1127_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1128_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_msg_1127_ = leanh::lean_ctor_get(v_t_1125_, 0);
        leanh::lean_inc_ref(v_msg_1127_);
        leanh::lean_dec_ref_known(v_t_1125_, 1);
        v___x_1128_ = leanh::lean_apply_1(v_k_1126_, v_msg_1127_);
        return v___x_1128_;
    } else {
        leanh::lean_dec(v_t_1125_);
        return v_k_1126_;
    }
}
pub unsafe fn l_Std_CancellationReason_ctorElim(
    mut v_motive_1129_: *mut leanh::LeanObject,
    mut v_ctorIdx_1130_: *mut leanh::LeanObject,
    mut v_t_1131_: *mut leanh::LeanObject,
    mut v_h_1132_: *mut leanh::LeanObject,
    mut v_k_1133_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1134_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1134_ = l_Std_CancellationReason_ctorElim___redArg(v_t_1131_, v_k_1133_);
    return v___x_1134_;
}
pub unsafe fn l_Std_CancellationReason_ctorElim___boxed(
    mut v_motive_1135_: *mut leanh::LeanObject,
    mut v_ctorIdx_1136_: *mut leanh::LeanObject,
    mut v_t_1137_: *mut leanh::LeanObject,
    mut v_h_1138_: *mut leanh::LeanObject,
    mut v_k_1139_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1140_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1140_ = l_Std_CancellationReason_ctorElim(
        v_motive_1135_,
        v_ctorIdx_1136_,
        v_t_1137_,
        v_h_1138_,
        v_k_1139_,
    );
    leanh::lean_dec(v_ctorIdx_1136_);
    return v_res_1140_;
}
pub unsafe fn l_Std_CancellationReason_deadline_elim___redArg(
    mut v_t_1141_: *mut leanh::LeanObject,
    mut v_deadline_1142_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1143_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1143_ = l_Std_CancellationReason_ctorElim___redArg(v_t_1141_, v_deadline_1142_);
    return v___x_1143_;
}
pub unsafe fn l_Std_CancellationReason_deadline_elim(
    mut v_motive_1144_: *mut leanh::LeanObject,
    mut v_t_1145_: *mut leanh::LeanObject,
    mut v_h_1146_: *mut leanh::LeanObject,
    mut v_deadline_1147_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1148_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1148_ = l_Std_CancellationReason_ctorElim___redArg(v_t_1145_, v_deadline_1147_);
    return v___x_1148_;
}
pub unsafe fn l_Std_CancellationReason_shutdown_elim___redArg(
    mut v_t_1149_: *mut leanh::LeanObject,
    mut v_shutdown_1150_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1151_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1151_ = l_Std_CancellationReason_ctorElim___redArg(v_t_1149_, v_shutdown_1150_);
    return v___x_1151_;
}
pub unsafe fn l_Std_CancellationReason_shutdown_elim(
    mut v_motive_1152_: *mut leanh::LeanObject,
    mut v_t_1153_: *mut leanh::LeanObject,
    mut v_h_1154_: *mut leanh::LeanObject,
    mut v_shutdown_1155_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1156_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1156_ = l_Std_CancellationReason_ctorElim___redArg(v_t_1153_, v_shutdown_1155_);
    return v___x_1156_;
}
pub unsafe fn l_Std_CancellationReason_cancel_elim___redArg(
    mut v_t_1157_: *mut leanh::LeanObject,
    mut v_cancel_1158_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1159_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1159_ = l_Std_CancellationReason_ctorElim___redArg(v_t_1157_, v_cancel_1158_);
    return v___x_1159_;
}
pub unsafe fn l_Std_CancellationReason_cancel_elim(
    mut v_motive_1160_: *mut leanh::LeanObject,
    mut v_t_1161_: *mut leanh::LeanObject,
    mut v_h_1162_: *mut leanh::LeanObject,
    mut v_cancel_1163_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1164_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1164_ = l_Std_CancellationReason_ctorElim___redArg(v_t_1161_, v_cancel_1163_);
    return v___x_1164_;
}
pub unsafe fn l_Std_CancellationReason_custom_elim___redArg(
    mut v_t_1165_: *mut leanh::LeanObject,
    mut v_custom_1166_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1167_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1167_ = l_Std_CancellationReason_ctorElim___redArg(v_t_1165_, v_custom_1166_);
    return v___x_1167_;
}
pub unsafe fn l_Std_CancellationReason_custom_elim(
    mut v_motive_1168_: *mut leanh::LeanObject,
    mut v_t_1169_: *mut leanh::LeanObject,
    mut v_h_1170_: *mut leanh::LeanObject,
    mut v_custom_1171_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1172_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1172_ = l_Std_CancellationReason_ctorElim___redArg(v_t_1169_, v_custom_1171_);
    return v___x_1172_;
}
pub unsafe fn _init_l_Std_instReprCancellationReason_repr___closed__6()
-> *mut leanh::LeanObject {
    let mut v___x_1182_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1183_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1182_ = leanh::lean_unsigned_to_nat(2);
    v___x_1183_ = lean_nat_to_int(v___x_1182_);
    return v___x_1183_;
}
pub unsafe fn _init_l_Std_instReprCancellationReason_repr___closed__7()
-> *mut leanh::LeanObject {
    let mut v___x_1184_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1185_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1184_ = leanh::lean_unsigned_to_nat(1);
    v___x_1185_ = lean_nat_to_int(v___x_1184_);
    return v___x_1185_;
}
pub unsafe fn l_Std_instReprCancellationReason_repr(
    mut v_x_1192_: *mut leanh::LeanObject,
    mut v_prec_1193_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___y_1195_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1196_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1197_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1198_: u8 = 0;
    let mut v___x_1199_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1200_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1202_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1203_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1204_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1205_: u8 = 0;
    let mut v___x_1206_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1207_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1209_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1210_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1211_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1212_: u8 = 0;
    let mut v___x_1213_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1214_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1215_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1216_: u8 = 0;
    let mut v___x_1217_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1218_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1219_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1220_: u8 = 0;
    let mut v___x_1221_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1222_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1223_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1224_: u8 = 0;
    let mut v___x_1225_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1226_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_msg_1227_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1229_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1230_: u8 = 0;
    let mut v___y_1232_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1233_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1234_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1236_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1237_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1238_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1239_: u8 = 0;
    let mut v___x_1240_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1241_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1242_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1243_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1244_: u8 = 0;
    let mut v___x_1245_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1246_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1247_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => match leanh::lean_obj_tag(v_x_1192_) {
                0 => {
                    v___x_1215_ = leanh::lean_unsigned_to_nat(1024);
                    v___x_1216_ = lean_nat_dec_le(v___x_1215_, v_prec_1193_);
                    if v___x_1216_ == 0 {
                        v___x_1217_ = leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(
                                l_Std_instReprCancellationReason_repr___closed__6
                            ),
                            core::ptr::addr_of_mut!(
                                l_Std_instReprCancellationReason_repr___closed__6_once
                            ),
                            _init_l_Std_instReprCancellationReason_repr___closed__6,
                        );
                        v___y_1209_ = v___x_1217_;
                        state = 3;
                        continue;
                    } else {
                        v___x_1218_ = leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(
                                l_Std_instReprCancellationReason_repr___closed__7
                            ),
                            core::ptr::addr_of_mut!(
                                l_Std_instReprCancellationReason_repr___closed__7_once
                            ),
                            _init_l_Std_instReprCancellationReason_repr___closed__7,
                        );
                        v___y_1209_ = v___x_1218_;
                        state = 3;
                        continue;
                    }
                }
                1 => {
                    v___x_1219_ = leanh::lean_unsigned_to_nat(1024);
                    v___x_1220_ = lean_nat_dec_le(v___x_1219_, v_prec_1193_);
                    if v___x_1220_ == 0 {
                        v___x_1221_ = leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(
                                l_Std_instReprCancellationReason_repr___closed__6
                            ),
                            core::ptr::addr_of_mut!(
                                l_Std_instReprCancellationReason_repr___closed__6_once
                            ),
                            _init_l_Std_instReprCancellationReason_repr___closed__6,
                        );
                        v___y_1202_ = v___x_1221_;
                        state = 2;
                        continue;
                    } else {
                        v___x_1222_ = leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(
                                l_Std_instReprCancellationReason_repr___closed__7
                            ),
                            core::ptr::addr_of_mut!(
                                l_Std_instReprCancellationReason_repr___closed__7_once
                            ),
                            _init_l_Std_instReprCancellationReason_repr___closed__7,
                        );
                        v___y_1202_ = v___x_1222_;
                        state = 2;
                        continue;
                    }
                }
                2 => {
                    v___x_1223_ = leanh::lean_unsigned_to_nat(1024);
                    v___x_1224_ = lean_nat_dec_le(v___x_1223_, v_prec_1193_);
                    if v___x_1224_ == 0 {
                        v___x_1225_ = leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(
                                l_Std_instReprCancellationReason_repr___closed__6
                            ),
                            core::ptr::addr_of_mut!(
                                l_Std_instReprCancellationReason_repr___closed__6_once
                            ),
                            _init_l_Std_instReprCancellationReason_repr___closed__6,
                        );
                        v___y_1195_ = v___x_1225_;
                        state = 1;
                        continue;
                    } else {
                        v___x_1226_ = leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(
                                l_Std_instReprCancellationReason_repr___closed__7
                            ),
                            core::ptr::addr_of_mut!(
                                l_Std_instReprCancellationReason_repr___closed__7_once
                            ),
                            _init_l_Std_instReprCancellationReason_repr___closed__7,
                        );
                        v___y_1195_ = v___x_1226_;
                        state = 1;
                        continue;
                    }
                }
                _ => {
                    v_msg_1227_ = leanh::lean_ctor_get(v_x_1192_, 0);
                    v_isSharedCheck_1247_ = (!leanh::lean_is_exclusive(v_x_1192_)) as u8;
                    if v_isSharedCheck_1247_ == 0 {
                        v___x_1229_ = v_x_1192_;
                        v_isShared_1230_ = v_isSharedCheck_1247_;
                        state = 4;
                        continue;
                    } else {
                        leanh::lean_inc(v_msg_1227_);
                        leanh::lean_dec(v_x_1192_);
                        v___x_1229_ = leanh::lean_box(0);
                        v_isShared_1230_ = v_isSharedCheck_1247_;
                        state = 4;
                        continue;
                    }
                }
            },
            1 => {
                v___x_1196_ = l_Std_instReprCancellationReason_repr___closed__1;
                leanh::lean_inc(v___y_1195_);
                v___x_1197_ = leanh::lean_alloc_ctor(4, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_1197_, 0, v___y_1195_);
                leanh::lean_ctor_set(v___x_1197_, 1, v___x_1196_);
                v___x_1198_ = 0;
                v___x_1199_ = leanh::lean_alloc_ctor(6, 1, (1) as u32);
                leanh::lean_ctor_set(v___x_1199_, 0, v___x_1197_);
                leanh::lean_ctor_set_uint8(
                    v___x_1199_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                    v___x_1198_,
                );
                v___x_1200_ = l_Repr_addAppParen(v___x_1199_, v_prec_1193_);
                return v___x_1200_;
            }
            2 => {
                v___x_1203_ = l_Std_instReprCancellationReason_repr___closed__3;
                leanh::lean_inc(v___y_1202_);
                v___x_1204_ = leanh::lean_alloc_ctor(4, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_1204_, 0, v___y_1202_);
                leanh::lean_ctor_set(v___x_1204_, 1, v___x_1203_);
                v___x_1205_ = 0;
                v___x_1206_ = leanh::lean_alloc_ctor(6, 1, (1) as u32);
                leanh::lean_ctor_set(v___x_1206_, 0, v___x_1204_);
                leanh::lean_ctor_set_uint8(
                    v___x_1206_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                    v___x_1205_,
                );
                v___x_1207_ = l_Repr_addAppParen(v___x_1206_, v_prec_1193_);
                return v___x_1207_;
            }
            3 => {
                v___x_1210_ = l_Std_instReprCancellationReason_repr___closed__5;
                leanh::lean_inc(v___y_1209_);
                v___x_1211_ = leanh::lean_alloc_ctor(4, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_1211_, 0, v___y_1209_);
                leanh::lean_ctor_set(v___x_1211_, 1, v___x_1210_);
                v___x_1212_ = 0;
                v___x_1213_ = leanh::lean_alloc_ctor(6, 1, (1) as u32);
                leanh::lean_ctor_set(v___x_1213_, 0, v___x_1211_);
                leanh::lean_ctor_set_uint8(
                    v___x_1213_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                    v___x_1212_,
                );
                v___x_1214_ = l_Repr_addAppParen(v___x_1213_, v_prec_1193_);
                return v___x_1214_;
            }
            4 => {
                v___x_1243_ = leanh::lean_unsigned_to_nat(1024);
                v___x_1244_ = lean_nat_dec_le(v___x_1243_, v_prec_1193_);
                if v___x_1244_ == 0 {
                    v___x_1245_ = leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(l_Std_instReprCancellationReason_repr___closed__6),
                        core::ptr::addr_of_mut!(
                            l_Std_instReprCancellationReason_repr___closed__6_once
                        ),
                        _init_l_Std_instReprCancellationReason_repr___closed__6,
                    );
                    v___y_1232_ = v___x_1245_;
                    state = 5;
                    continue;
                } else {
                    v___x_1246_ = leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(l_Std_instReprCancellationReason_repr___closed__7),
                        core::ptr::addr_of_mut!(
                            l_Std_instReprCancellationReason_repr___closed__7_once
                        ),
                        _init_l_Std_instReprCancellationReason_repr___closed__7,
                    );
                    v___y_1232_ = v___x_1246_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v___x_1233_ = l_Std_instReprCancellationReason_repr___closed__10;
                v___x_1234_ = l_String_quote(v_msg_1227_);
                if v_isShared_1230_ == 0 {
                    leanh::lean_ctor_set(v___x_1229_, 0, v___x_1234_);
                    v___x_1236_ = v___x_1229_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_1242_ = leanh::lean_alloc_ctor(3, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1242_, 0, v___x_1234_);
                    v___x_1236_ = v_reuseFailAlloc_1242_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                v___x_1237_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_1237_, 0, v___x_1233_);
                leanh::lean_ctor_set(v___x_1237_, 1, v___x_1236_);
                leanh::lean_inc(v___y_1232_);
                v___x_1238_ = leanh::lean_alloc_ctor(4, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_1238_, 0, v___y_1232_);
                leanh::lean_ctor_set(v___x_1238_, 1, v___x_1237_);
                v___x_1239_ = 0;
                v___x_1240_ = leanh::lean_alloc_ctor(6, 1, (1) as u32);
                leanh::lean_ctor_set(v___x_1240_, 0, v___x_1238_);
                leanh::lean_ctor_set_uint8(
                    v___x_1240_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                    v___x_1239_,
                );
                v___x_1241_ = l_Repr_addAppParen(v___x_1240_, v_prec_1193_);
                return v___x_1241_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_instReprCancellationReason_repr___boxed(
    mut v_x_1248_: *mut leanh::LeanObject,
    mut v_prec_1249_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1250_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1250_ = l_Std_instReprCancellationReason_repr(v_x_1248_, v_prec_1249_);
    leanh::lean_dec(v_prec_1249_);
    return v_res_1250_;
}
pub unsafe fn l_Std_instBEqCancellationReason_beq(
    mut v_x_1253_: *mut leanh::LeanObject,
    mut v_x_1254_: *mut leanh::LeanObject,
) -> u8 {
    match leanh::lean_obj_tag(v_x_1253_) {
        0 => {
            if leanh::lean_obj_tag(v_x_1254_) == 0 {
                let mut v___x_1255_: u8 = 0;
                v___x_1255_ = 1;
                return v___x_1255_;
            } else {
                let mut v___x_1256_: u8 = 0;
                v___x_1256_ = 0;
                return v___x_1256_;
            }
        }
        1 => {
            if leanh::lean_obj_tag(v_x_1254_) == 1 {
                let mut v___x_1257_: u8 = 0;
                v___x_1257_ = 1;
                return v___x_1257_;
            } else {
                let mut v___x_1258_: u8 = 0;
                v___x_1258_ = 0;
                return v___x_1258_;
            }
        }
        2 => {
            if leanh::lean_obj_tag(v_x_1254_) == 2 {
                let mut v___x_1259_: u8 = 0;
                v___x_1259_ = 1;
                return v___x_1259_;
            } else {
                let mut v___x_1260_: u8 = 0;
                v___x_1260_ = 0;
                return v___x_1260_;
            }
        }
        _ => {
            if leanh::lean_obj_tag(v_x_1254_) == 3 {
                let mut v_msg_1261_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v_msg_1262_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_1263_: u8 = 0;
                v_msg_1261_ = leanh::lean_ctor_get(v_x_1253_, 0);
                v_msg_1262_ = leanh::lean_ctor_get(v_x_1254_, 0);
                v___x_1263_ = lean_string_dec_eq(v_msg_1261_, v_msg_1262_);
                return v___x_1263_;
            } else {
                let mut v___x_1264_: u8 = 0;
                v___x_1264_ = 0;
                return v___x_1264_;
            }
        }
    }
}
pub unsafe fn l_Std_instBEqCancellationReason_beq___boxed(
    mut v_x_1265_: *mut leanh::LeanObject,
    mut v_x_1266_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1267_: u8 = 0;
    let mut v_r_1268_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1267_ = l_Std_instBEqCancellationReason_beq(v_x_1265_, v_x_1266_);
    leanh::lean_dec(v_x_1266_);
    leanh::lean_dec(v_x_1265_);
    v_r_1268_ = leanh::lean_box((v_res_1267_) as usize);
    return v_r_1268_;
}
pub unsafe fn l_Std_instToStringCancellationReason___lam__0(
    mut v_x_1276_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    match leanh::lean_obj_tag(v_x_1276_) {
        0 => {
            let mut v___x_1277_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_1277_ = l_Std_instToStringCancellationReason___lam__0___closed__0;
            return v___x_1277_;
        }
        1 => {
            let mut v___x_1278_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_1278_ = l_Std_instToStringCancellationReason___lam__0___closed__1;
            return v___x_1278_;
        }
        2 => {
            let mut v___x_1279_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_1279_ = l_Std_instToStringCancellationReason___lam__0___closed__2;
            return v___x_1279_;
        }
        _ => {
            let mut v_msg_1280_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1281_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1282_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1283_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1284_: *mut leanh::LeanObject = core::ptr::null_mut();
            v_msg_1280_ = leanh::lean_ctor_get(v_x_1276_, 0);
            v___x_1281_ = l_Std_instToStringCancellationReason___lam__0___closed__3;
            v___x_1282_ = lean_string_append(v___x_1281_, v_msg_1280_);
            v___x_1283_ = l_Std_instToStringCancellationReason___lam__0___closed__4;
            v___x_1284_ = lean_string_append(v___x_1282_, v___x_1283_);
            return v___x_1284_;
        }
    }
}
pub unsafe fn l_Std_instToStringCancellationReason___lam__0___boxed(
    mut v_x_1285_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1286_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1286_ = l_Std_instToStringCancellationReason___lam__0(v_x_1285_);
    leanh::lean_dec(v_x_1285_);
    return v_res_1286_;
}
pub unsafe fn l_Std_CancellationToken_Consumer_ctorIdx(
    mut v_x_1289_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_x_1289_) == 0 {
        let mut v___x_1290_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_1290_ = leanh::lean_unsigned_to_nat(0);
        return v___x_1290_;
    } else {
        let mut v___x_1291_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_1291_ = leanh::lean_unsigned_to_nat(1);
        return v___x_1291_;
    }
}
pub unsafe fn l_Std_CancellationToken_Consumer_ctorIdx___boxed(
    mut v_x_1292_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1293_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1293_ = l_Std_CancellationToken_Consumer_ctorIdx(v_x_1292_);
    leanh::lean_dec_ref(v_x_1292_);
    return v_res_1293_;
}
pub unsafe fn l_Std_CancellationToken_Consumer_ctorElim___redArg(
    mut v_t_1294_: *mut leanh::LeanObject,
    mut v_k_1295_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_t_1294_) == 0 {
        let mut v_promise_1296_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1297_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_promise_1296_ = leanh::lean_ctor_get(v_t_1294_, 0);
        leanh::lean_inc(v_promise_1296_);
        leanh::lean_dec_ref_known(v_t_1294_, 1);
        v___x_1297_ = leanh::lean_apply_1(v_k_1295_, v_promise_1296_);
        return v___x_1297_;
    } else {
        let mut v_finished_1298_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1299_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_finished_1298_ = leanh::lean_ctor_get(v_t_1294_, 0);
        leanh::lean_inc_ref(v_finished_1298_);
        leanh::lean_dec_ref_known(v_t_1294_, 1);
        v___x_1299_ = leanh::lean_apply_1(v_k_1295_, v_finished_1298_);
        return v___x_1299_;
    }
}
pub unsafe fn l_Std_CancellationToken_Consumer_ctorElim(
    mut v_motive_1300_: *mut leanh::LeanObject,
    mut v_ctorIdx_1301_: *mut leanh::LeanObject,
    mut v_t_1302_: *mut leanh::LeanObject,
    mut v_h_1303_: *mut leanh::LeanObject,
    mut v_k_1304_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1305_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1305_ = l_Std_CancellationToken_Consumer_ctorElim___redArg(v_t_1302_, v_k_1304_);
    return v___x_1305_;
}
pub unsafe fn l_Std_CancellationToken_Consumer_ctorElim___boxed(
    mut v_motive_1306_: *mut leanh::LeanObject,
    mut v_ctorIdx_1307_: *mut leanh::LeanObject,
    mut v_t_1308_: *mut leanh::LeanObject,
    mut v_h_1309_: *mut leanh::LeanObject,
    mut v_k_1310_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1311_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1311_ = l_Std_CancellationToken_Consumer_ctorElim(
        v_motive_1306_,
        v_ctorIdx_1307_,
        v_t_1308_,
        v_h_1309_,
        v_k_1310_,
    );
    leanh::lean_dec(v_ctorIdx_1307_);
    return v_res_1311_;
}
pub unsafe fn l_Std_CancellationToken_Consumer_normal_elim___redArg(
    mut v_t_1312_: *mut leanh::LeanObject,
    mut v_normal_1313_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1314_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1314_ = l_Std_CancellationToken_Consumer_ctorElim___redArg(v_t_1312_, v_normal_1313_);
    return v___x_1314_;
}
pub unsafe fn l_Std_CancellationToken_Consumer_normal_elim(
    mut v_motive_1315_: *mut leanh::LeanObject,
    mut v_t_1316_: *mut leanh::LeanObject,
    mut v_h_1317_: *mut leanh::LeanObject,
    mut v_normal_1318_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1319_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1319_ = l_Std_CancellationToken_Consumer_ctorElim___redArg(v_t_1316_, v_normal_1318_);
    return v___x_1319_;
}
pub unsafe fn l_Std_CancellationToken_Consumer_select_elim___redArg(
    mut v_t_1320_: *mut leanh::LeanObject,
    mut v_select_1321_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1322_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1322_ = l_Std_CancellationToken_Consumer_ctorElim___redArg(v_t_1320_, v_select_1321_);
    return v___x_1322_;
}
pub unsafe fn l_Std_CancellationToken_Consumer_select_elim(
    mut v_motive_1323_: *mut leanh::LeanObject,
    mut v_t_1324_: *mut leanh::LeanObject,
    mut v_h_1325_: *mut leanh::LeanObject,
    mut v_select_1326_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1327_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1327_ = l_Std_CancellationToken_Consumer_ctorElim___redArg(v_t_1324_, v_select_1326_);
    return v___x_1327_;
}
pub unsafe fn l_Std_Async_Waiter_race___at___00Std_CancellationToken_Consumer_resolve_spec__0(
    mut v_w_1330_: *mut leanh::LeanObject,
    mut v_lose_1331_: *mut leanh::LeanObject,
) -> u8 {
    let mut v_finished_1333_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_promise_1334_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1335_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1337_: u8 = 0;
    let mut v___x_1338_: u8 = 0;
    let mut v___x_1339_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1340_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1341_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1342_: u8 = 0;
    let mut v___x_1343_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1344_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1345_: u8 = 0;
    let mut v___x_1346_: u8 = 0;
    let mut v___x_1347_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_finished_1333_ = leanh::lean_ctor_get(v_w_1330_, 0);
                v_promise_1334_ = leanh::lean_ctor_get(v_w_1330_, 1);
                v___x_1335_ = lean_st_ref_take(v_finished_1333_);
                v___x_1345_ = (leanh::lean_unbox(v___x_1335_) as u8);
                leanh::lean_dec(v___x_1335_);
                if v___x_1345_ == 0 {
                    v___x_1346_ = 1;
                    v___y_1337_ = v___x_1346_;
                    state = 1;
                    continue;
                } else {
                    v___x_1347_ = 0;
                    v___y_1337_ = v___x_1347_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_1338_ = 1;
                v___x_1339_ = leanh::lean_box((v___x_1338_) as usize);
                v___x_1340_ = lean_st_ref_set(v_finished_1333_, v___x_1339_);
                if v___y_1337_ == 0 {
                    v___x_1341_ =
                        leanh::lean_apply_1(v_lose_1331_, leanh::lean_box(0));
                    v___x_1342_ = (leanh::lean_unbox(v___x_1341_) as u8);
                    return v___x_1342_;
                } else {
                    leanh::lean_dec_ref(v_lose_1331_);
                    v___x_1343_ = l_Std_Async_Waiter_race___at___00Std_CancellationToken_Consumer_resolve_spec__0___closed__0;
                    v___x_1344_ = lean_io_promise_resolve(v___x_1343_, v_promise_1334_);
                    return v___y_1337_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Async_Waiter_race___at___00Std_CancellationToken_Consumer_resolve_spec__0___boxed(
    mut v_w_1348_: *mut leanh::LeanObject,
    mut v_lose_1349_: *mut leanh::LeanObject,
    mut v___y_1350_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1351_: u8 = 0;
    let mut v_r_1352_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1351_ = l_Std_Async_Waiter_race___at___00Std_CancellationToken_Consumer_resolve_spec__0(
        v_w_1348_,
        v_lose_1349_,
    );
    leanh::lean_dec_ref(v_w_1348_);
    v_r_1352_ = leanh::lean_box((v_res_1351_) as usize);
    return v_r_1352_;
}
pub unsafe fn l_Std_CancellationToken_Consumer_resolve___lam__0(mut v___x_1353_: u8) -> u8 {
    return v___x_1353_;
}
pub unsafe fn l_Std_CancellationToken_Consumer_resolve___lam__0___boxed(
    mut v___x_1355_: *mut leanh::LeanObject,
    mut v___y_1356_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_408__boxed_1357_: u8 = 0;
    let mut v_res_1358_: u8 = 0;
    let mut v_r_1359_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_408__boxed_1357_ = (leanh::lean_unbox(v___x_1355_) as u8);
    v_res_1358_ = l_Std_CancellationToken_Consumer_resolve___lam__0(v___x_408__boxed_1357_);
    v_r_1359_ = leanh::lean_box((v_res_1358_) as usize);
    return v_r_1359_;
}
pub unsafe fn l_Std_CancellationToken_Consumer_resolve(
    mut v_c_1363_: *mut leanh::LeanObject,
) -> u8 {
    if leanh::lean_obj_tag(v_c_1363_) == 0 {
        let mut v_promise_1365_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1366_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1367_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1368_: u8 = 0;
        v_promise_1365_ = leanh::lean_ctor_get(v_c_1363_, 0);
        v___x_1366_ = leanh::lean_box(0);
        v___x_1367_ = lean_io_promise_resolve(v___x_1366_, v_promise_1365_);
        v___x_1368_ = 1;
        return v___x_1368_;
    } else {
        let mut v_finished_1369_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_lose_1370_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1371_: u8 = 0;
        v_finished_1369_ = leanh::lean_ctor_get(v_c_1363_, 0);
        v_lose_1370_ = l_Std_CancellationToken_Consumer_resolve___closed__0;
        v___x_1371_ =
            l_Std_Async_Waiter_race___at___00Std_CancellationToken_Consumer_resolve_spec__0(
                v_finished_1369_,
                v_lose_1370_,
            );
        return v___x_1371_;
    }
}
pub unsafe fn l_Std_CancellationToken_Consumer_resolve___boxed(
    mut v_c_1372_: *mut leanh::LeanObject,
    mut v_a_1373_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1374_: u8 = 0;
    let mut v_r_1375_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1374_ = l_Std_CancellationToken_Consumer_resolve(v_c_1372_);
    leanh::lean_dec_ref(v_c_1372_);
    v_r_1375_ = leanh::lean_box((v_res_1374_) as usize);
    return v_r_1375_;
}
pub unsafe fn _init_l_Std_CancellationToken_new___closed__0() -> *mut leanh::LeanObject {
    let mut v___x_1376_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1376_ = l_Std_Queue_empty(leanh::lean_box(0));
    return v___x_1376_;
}
pub unsafe fn _init_l_Std_CancellationToken_new___closed__1() -> *mut leanh::LeanObject {
    let mut v___x_1377_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1378_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1379_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1377_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_CancellationToken_new___closed__0),
        core::ptr::addr_of_mut!(l_Std_CancellationToken_new___closed__0_once),
        _init_l_Std_CancellationToken_new___closed__0,
    );
    v___x_1378_ = leanh::lean_box(0);
    v___x_1379_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1379_, 0, v___x_1378_);
    leanh::lean_ctor_set(v___x_1379_, 1, v___x_1377_);
    return v___x_1379_;
}
pub unsafe fn l_Std_CancellationToken_new() -> *mut leanh::LeanObject {
    let mut v___x_1381_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1382_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1381_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_CancellationToken_new___closed__1),
        core::ptr::addr_of_mut!(l_Std_CancellationToken_new___closed__1_once),
        _init_l_Std_CancellationToken_new___closed__1,
    );
    v___x_1382_ = l_Std_Mutex_new___redArg(v___x_1381_);
    return v___x_1382_;
}
pub unsafe fn l_Std_CancellationToken_new___boxed(
    mut v_a_1383_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1384_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1384_ = l_Std_CancellationToken_new();
    return v_res_1384_;
}
pub unsafe fn l_Std_Mutex_atomically___at___00Std_CancellationToken_cancel_spec__1___redArg(
    mut v_mutex_1385_: *mut leanh::LeanObject,
    mut v_k_1386_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_ref_1388_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_mutex_1389_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1390_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1391_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1392_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_ref_1388_ = leanh::lean_ctor_get(v_mutex_1385_, 0);
    leanh::lean_inc(v_ref_1388_);
    v_mutex_1389_ = leanh::lean_ctor_get(v_mutex_1385_, 1);
    leanh::lean_inc(v_mutex_1389_);
    leanh::lean_dec_ref(v_mutex_1385_);
    v___x_1390_ = lean_io_basemutex_lock(v_mutex_1389_);
    v___x_1391_ = leanh::lean_apply_2(v_k_1386_, v_ref_1388_, leanh::lean_box(0));
    v___x_1392_ = lean_io_basemutex_unlock(v_mutex_1389_);
    leanh::lean_dec(v_mutex_1389_);
    return v___x_1391_;
}
pub unsafe fn l_Std_Mutex_atomically___at___00Std_CancellationToken_cancel_spec__1___redArg___boxed(
    mut v_mutex_1393_: *mut leanh::LeanObject,
    mut v_k_1394_: *mut leanh::LeanObject,
    mut v___y_1395_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1396_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1396_ = l_Std_Mutex_atomically___at___00Std_CancellationToken_cancel_spec__1___redArg(
        v_mutex_1393_,
        v_k_1394_,
    );
    return v_res_1396_;
}
pub unsafe fn l_Std_Mutex_atomically___at___00Std_CancellationToken_cancel_spec__1(
    mut v_00_u03b1_1397_: *mut leanh::LeanObject,
    mut v_00_u03b2_1398_: *mut leanh::LeanObject,
    mut v_mutex_1399_: *mut leanh::LeanObject,
    mut v_k_1400_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1402_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1402_ = l_Std_Mutex_atomically___at___00Std_CancellationToken_cancel_spec__1___redArg(
        v_mutex_1399_,
        v_k_1400_,
    );
    return v___x_1402_;
}
pub unsafe fn l_Std_Mutex_atomically___at___00Std_CancellationToken_cancel_spec__1___boxed(
    mut v_00_u03b1_1403_: *mut leanh::LeanObject,
    mut v_00_u03b2_1404_: *mut leanh::LeanObject,
    mut v_mutex_1405_: *mut leanh::LeanObject,
    mut v_k_1406_: *mut leanh::LeanObject,
    mut v___y_1407_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1408_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1408_ = l_Std_Mutex_atomically___at___00Std_CancellationToken_cancel_spec__1(
        v_00_u03b1_1403_,
        v_00_u03b2_1404_,
        v_mutex_1405_,
        v_k_1406_,
    );
    return v_res_1408_;
}
pub unsafe fn l___private_Init_While_0__whileM_erased___at___00Std_CancellationToken_cancel_spec__0___redArg(
    mut v_a_1409_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1411_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1412_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_1413_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1414_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1415_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                leanh::lean_inc_ref(v_a_1409_);
                v___x_1411_ = l_Std_Queue_dequeue_x3f___redArg(v_a_1409_);
                if leanh::lean_obj_tag(v___x_1411_) == 1 {
                    leanh::lean_dec_ref(v_a_1409_);
                    v_val_1412_ = leanh::lean_ctor_get(v___x_1411_, 0);
                    leanh::lean_inc(v_val_1412_);
                    leanh::lean_dec_ref_known(v___x_1411_, 1);
                    v_fst_1413_ = leanh::lean_ctor_get(v_val_1412_, 0);
                    leanh::lean_inc(v_fst_1413_);
                    v_snd_1414_ = leanh::lean_ctor_get(v_val_1412_, 1);
                    leanh::lean_inc(v_snd_1414_);
                    leanh::lean_dec(v_val_1412_);
                    v___x_1415_ = l_Std_CancellationToken_Consumer_resolve(v_fst_1413_);
                    leanh::lean_dec(v_fst_1413_);
                    v_a_1409_ = v_snd_1414_;
                    state = 0;
                    continue;
                } else {
                    leanh::lean_dec(v___x_1411_);
                    return v_a_1409_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_While_0__whileM_erased___at___00Std_CancellationToken_cancel_spec__0___redArg___boxed(
    mut v_a_1417_: *mut leanh::LeanObject,
    mut v___y_1418_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1419_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1419_ = l___private_Init_While_0__whileM_erased___at___00Std_CancellationToken_cancel_spec__0___redArg(v_a_1417_);
    return v_res_1419_;
}
pub unsafe fn l_Std_CancellationToken_cancel___lam__0(
    mut v_reason_1420_: *mut leanh::LeanObject,
    mut v___y_1421_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1423_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reason_1424_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_consumers_1425_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1427_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1428_: u8 = 0;
    let mut v___x_1429_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1430_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1431_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_st_1433_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1434_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1435_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1436_: u8 = 0;
    let mut v_unused_1437_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1438_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1423_ = lean_st_ref_get(v___y_1421_);
                v_reason_1424_ = leanh::lean_ctor_get(v___x_1423_, 0);
                leanh::lean_inc(v_reason_1424_);
                if leanh::lean_obj_tag(v_reason_1424_) == 0 {
                    v_consumers_1425_ = leanh::lean_ctor_get(v___x_1423_, 1);
                    v_isSharedCheck_1436_ = (!leanh::lean_is_exclusive(v___x_1423_)) as u8;
                    if v_isSharedCheck_1436_ == 0 {
                        v_unused_1437_ = leanh::lean_ctor_get(v___x_1423_, 0);
                        leanh::lean_dec(v_unused_1437_);
                        v___x_1427_ = v___x_1423_;
                        v_isShared_1428_ = v_isSharedCheck_1436_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_consumers_1425_);
                        leanh::lean_dec(v___x_1423_);
                        v___x_1427_ = leanh::lean_box(0);
                        v_isShared_1428_ = v_isSharedCheck_1436_;
                        state = 1;
                        continue;
                    }
                } else {
                    leanh::lean_dec_ref_known(v_reason_1424_, 1);
                    leanh::lean_dec(v___x_1423_);
                    leanh::lean_dec(v_reason_1420_);
                    v___x_1438_ = leanh::lean_box(0);
                    return v___x_1438_;
                }
            }
            1 => {
                v___x_1429_ = l___private_Init_While_0__whileM_erased___at___00Std_CancellationToken_cancel_spec__0___redArg(v_consumers_1425_);
                leanh::lean_dec_ref(v___x_1429_);
                v___x_1430_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_1430_, 0, v_reason_1420_);
                v___x_1431_ = leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Std_CancellationToken_new___closed__0),
                    core::ptr::addr_of_mut!(l_Std_CancellationToken_new___closed__0_once),
                    _init_l_Std_CancellationToken_new___closed__0,
                );
                if v_isShared_1428_ == 0 {
                    leanh::lean_ctor_set(v___x_1427_, 1, v___x_1431_);
                    leanh::lean_ctor_set(v___x_1427_, 0, v___x_1430_);
                    v_st_1433_ = v___x_1427_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1435_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1435_, 0, v___x_1430_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1435_, 1, v___x_1431_);
                    v_st_1433_ = v_reuseFailAlloc_1435_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_1434_ = lean_st_ref_set(v___y_1421_, v_st_1433_);
                return v___x_1434_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_CancellationToken_cancel___lam__0___boxed(
    mut v_reason_1439_: *mut leanh::LeanObject,
    mut v___y_1440_: *mut leanh::LeanObject,
    mut v___y_1441_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1442_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1442_ = l_Std_CancellationToken_cancel___lam__0(v_reason_1439_, v___y_1440_);
    leanh::lean_dec(v___y_1440_);
    return v_res_1442_;
}
pub unsafe fn l_Std_CancellationToken_cancel(
    mut v_x_1443_: *mut leanh::LeanObject,
    mut v_reason_1444_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_1446_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1447_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_1446_ = leanh::lean_alloc_closure(
        l_Std_CancellationToken_cancel___lam__0___boxed as *mut core::ffi::c_void,
        3,
        1,
    );
    leanh::lean_closure_set(v___f_1446_, 0, v_reason_1444_);
    v___x_1447_ = l_Std_Mutex_atomically___at___00Std_CancellationToken_cancel_spec__1___redArg(
        v_x_1443_,
        v___f_1446_,
    );
    return v___x_1447_;
}
pub unsafe fn l_Std_CancellationToken_cancel___boxed(
    mut v_x_1448_: *mut leanh::LeanObject,
    mut v_reason_1449_: *mut leanh::LeanObject,
    mut v_a_1450_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1451_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1451_ = l_Std_CancellationToken_cancel(v_x_1448_, v_reason_1449_);
    return v_res_1451_;
}
pub unsafe fn l___private_Init_While_0__whileM_erased___at___00Std_CancellationToken_cancel_spec__0(
    mut v_inst_1452_: *mut leanh::LeanObject,
    mut v_a_1453_: *mut leanh::LeanObject,
    mut v___y_1454_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1456_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1456_ = l___private_Init_While_0__whileM_erased___at___00Std_CancellationToken_cancel_spec__0___redArg(v_a_1453_);
    return v___x_1456_;
}
pub unsafe fn l___private_Init_While_0__whileM_erased___at___00Std_CancellationToken_cancel_spec__0___boxed(
    mut v_inst_1457_: *mut leanh::LeanObject,
    mut v_a_1458_: *mut leanh::LeanObject,
    mut v___y_1459_: *mut leanh::LeanObject,
    mut v___y_1460_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1461_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1461_ =
        l___private_Init_While_0__whileM_erased___at___00Std_CancellationToken_cancel_spec__0(
            v_inst_1457_,
            v_a_1458_,
            v___y_1459_,
        );
    leanh::lean_dec(v___y_1459_);
    return v_res_1461_;
}
pub unsafe fn l_Std_CancellationToken_isCancelled___lam__0(
    mut v___y_1462_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_1464_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reason_1465_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1464_ = lean_st_ref_get(v___y_1462_);
    v_reason_1465_ = leanh::lean_ctor_get(v___x_1464_, 0);
    leanh::lean_inc(v_reason_1465_);
    leanh::lean_dec(v___x_1464_);
    if leanh::lean_obj_tag(v_reason_1465_) == 0 {
        let mut v___x_1466_: u8 = 0;
        v___x_1466_ = 0;
        return v___x_1466_;
    } else {
        let mut v___x_1467_: u8 = 0;
        leanh::lean_dec_ref_known(v_reason_1465_, 1);
        v___x_1467_ = 1;
        return v___x_1467_;
    }
}
pub unsafe fn l_Std_CancellationToken_isCancelled___lam__0___boxed(
    mut v___y_1468_: *mut leanh::LeanObject,
    mut v___y_1469_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1470_: u8 = 0;
    let mut v_r_1471_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1470_ = l_Std_CancellationToken_isCancelled___lam__0(v___y_1468_);
    leanh::lean_dec(v___y_1468_);
    v_r_1471_ = leanh::lean_box((v_res_1470_) as usize);
    return v_r_1471_;
}
pub unsafe fn l_Std_CancellationToken_isCancelled(
    mut v_x_1473_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___f_1475_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1476_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1477_: u8 = 0;
    v___f_1475_ = l_Std_CancellationToken_isCancelled___closed__0;
    v___x_1476_ = l_Std_Mutex_atomically___at___00Std_CancellationToken_cancel_spec__1___redArg(
        v_x_1473_,
        v___f_1475_,
    );
    v___x_1477_ = (leanh::lean_unbox(v___x_1476_) as u8);
    leanh::lean_dec(v___x_1476_);
    return v___x_1477_;
}
pub unsafe fn l_Std_CancellationToken_isCancelled___boxed(
    mut v_x_1478_: *mut leanh::LeanObject,
    mut v_a_1479_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1480_: u8 = 0;
    let mut v_r_1481_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1480_ = l_Std_CancellationToken_isCancelled(v_x_1478_);
    v_r_1481_ = leanh::lean_box((v_res_1480_) as usize);
    return v_r_1481_;
}
pub unsafe fn l_Std_CancellationToken_getCancellationReason___lam__0(
    mut v___y_1482_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1484_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reason_1485_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1484_ = lean_st_ref_get(v___y_1482_);
    v_reason_1485_ = leanh::lean_ctor_get(v___x_1484_, 0);
    leanh::lean_inc(v_reason_1485_);
    leanh::lean_dec(v___x_1484_);
    return v_reason_1485_;
}
pub unsafe fn l_Std_CancellationToken_getCancellationReason___lam__0___boxed(
    mut v___y_1486_: *mut leanh::LeanObject,
    mut v___y_1487_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1488_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1488_ = l_Std_CancellationToken_getCancellationReason___lam__0(v___y_1486_);
    leanh::lean_dec(v___y_1486_);
    return v_res_1488_;
}
pub unsafe fn l_Std_CancellationToken_getCancellationReason(
    mut v_x_1490_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_1492_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1493_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_1492_ = l_Std_CancellationToken_getCancellationReason___closed__0;
    v___x_1493_ = l_Std_Mutex_atomically___at___00Std_CancellationToken_cancel_spec__1___redArg(
        v_x_1490_,
        v___f_1492_,
    );
    return v___x_1493_;
}
pub unsafe fn l_Std_CancellationToken_getCancellationReason___boxed(
    mut v_x_1494_: *mut leanh::LeanObject,
    mut v_a_1495_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1496_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1496_ = l_Std_CancellationToken_getCancellationReason(v_x_1494_);
    return v_res_1496_;
}
pub unsafe fn l_Std_Mutex_atomically___at___00Std_CancellationToken_wait_spec__0___redArg(
    mut v_mutex_1497_: *mut leanh::LeanObject,
    mut v_k_1498_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_ref_1500_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_mutex_1501_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1502_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_1503_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1504_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1506_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1507_: u8 = 0;
    let mut v___x_1508_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1510_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1511_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1512_: u8 = 0;
    let mut v_a_1513_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1515_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1516_: u8 = 0;
    let mut v___x_1517_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1519_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1520_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1521_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ref_1500_ = leanh::lean_ctor_get(v_mutex_1497_, 0);
                leanh::lean_inc(v_ref_1500_);
                v_mutex_1501_ = leanh::lean_ctor_get(v_mutex_1497_, 1);
                leanh::lean_inc(v_mutex_1501_);
                leanh::lean_dec_ref(v_mutex_1497_);
                v___x_1502_ = lean_io_basemutex_lock(v_mutex_1501_);
                v_r_1503_ =
                    leanh::lean_apply_2(v_k_1498_, v_ref_1500_, leanh::lean_box(0));
                if leanh::lean_obj_tag(v_r_1503_) == 0 {
                    v_a_1504_ = leanh::lean_ctor_get(v_r_1503_, 0);
                    v_isSharedCheck_1512_ = (!leanh::lean_is_exclusive(v_r_1503_)) as u8;
                    if v_isSharedCheck_1512_ == 0 {
                        v___x_1506_ = v_r_1503_;
                        v_isShared_1507_ = v_isSharedCheck_1512_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_1504_);
                        leanh::lean_dec(v_r_1503_);
                        v___x_1506_ = leanh::lean_box(0);
                        v_isShared_1507_ = v_isSharedCheck_1512_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_1513_ = leanh::lean_ctor_get(v_r_1503_, 0);
                    v_isSharedCheck_1521_ = (!leanh::lean_is_exclusive(v_r_1503_)) as u8;
                    if v_isSharedCheck_1521_ == 0 {
                        v___x_1515_ = v_r_1503_;
                        v_isShared_1516_ = v_isSharedCheck_1521_;
                        state = 3;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_1513_);
                        leanh::lean_dec(v_r_1503_);
                        v___x_1515_ = leanh::lean_box(0);
                        v_isShared_1516_ = v_isSharedCheck_1521_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v___x_1508_ = lean_io_basemutex_unlock(v_mutex_1501_);
                leanh::lean_dec(v_mutex_1501_);
                if v_isShared_1507_ == 0 {
                    v___x_1510_ = v___x_1506_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1511_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1511_, 0, v_a_1504_);
                    v___x_1510_ = v_reuseFailAlloc_1511_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1510_;
            }
            3 => {
                v___x_1517_ = lean_io_basemutex_unlock(v_mutex_1501_);
                leanh::lean_dec(v_mutex_1501_);
                if v_isShared_1516_ == 0 {
                    v___x_1519_ = v___x_1515_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1520_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1520_, 0, v_a_1513_);
                    v___x_1519_ = v_reuseFailAlloc_1520_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_1519_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Mutex_atomically___at___00Std_CancellationToken_wait_spec__0___redArg___boxed(
    mut v_mutex_1522_: *mut leanh::LeanObject,
    mut v_k_1523_: *mut leanh::LeanObject,
    mut v___y_1524_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1525_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1525_ = l_Std_Mutex_atomically___at___00Std_CancellationToken_wait_spec__0___redArg(
        v_mutex_1522_,
        v_k_1523_,
    );
    return v_res_1525_;
}
pub unsafe fn l_Std_Mutex_atomically___at___00Std_CancellationToken_wait_spec__0(
    mut v_00_u03b1_1526_: *mut leanh::LeanObject,
    mut v_00_u03b2_1527_: *mut leanh::LeanObject,
    mut v_mutex_1528_: *mut leanh::LeanObject,
    mut v_k_1529_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1531_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1531_ = l_Std_Mutex_atomically___at___00Std_CancellationToken_wait_spec__0___redArg(
        v_mutex_1528_,
        v_k_1529_,
    );
    return v___x_1531_;
}
pub unsafe fn l_Std_Mutex_atomically___at___00Std_CancellationToken_wait_spec__0___boxed(
    mut v_00_u03b1_1532_: *mut leanh::LeanObject,
    mut v_00_u03b2_1533_: *mut leanh::LeanObject,
    mut v_mutex_1534_: *mut leanh::LeanObject,
    mut v_k_1535_: *mut leanh::LeanObject,
    mut v___y_1536_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1537_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1537_ = l_Std_Mutex_atomically___at___00Std_CancellationToken_wait_spec__0(
        v_00_u03b1_1532_,
        v_00_u03b2_1533_,
        v_mutex_1534_,
        v_k_1535_,
    );
    return v_res_1537_;
}
pub unsafe fn _init_l_Std_CancellationToken_wait___lam__0___closed__1()
-> *mut leanh::LeanObject {
    let mut v___x_1539_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1540_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1539_ = l_Std_CancellationToken_wait___lam__0___closed__0;
    v___x_1540_ = lean_mk_io_user_error(v___x_1539_);
    return v___x_1540_;
}
pub unsafe fn _init_l_Std_CancellationToken_wait___lam__0___closed__2()
-> *mut leanh::LeanObject {
    let mut v___x_1541_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1542_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1541_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_CancellationToken_wait___lam__0___closed__1),
        core::ptr::addr_of_mut!(l_Std_CancellationToken_wait___lam__0___closed__1_once),
        _init_l_Std_CancellationToken_wait___lam__0___closed__1,
    );
    v___x_1542_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_1542_, 0, v___x_1541_);
    return v___x_1542_;
}
pub unsafe fn _init_l_Std_CancellationToken_wait___lam__0___closed__3()
-> *mut leanh::LeanObject {
    let mut v___x_1543_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1544_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1543_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_CancellationToken_wait___lam__0___closed__2),
        core::ptr::addr_of_mut!(l_Std_CancellationToken_wait___lam__0___closed__2_once),
        _init_l_Std_CancellationToken_wait___lam__0___closed__2,
    );
    v___x_1544_ = lean_task_pure(v___x_1543_);
    return v___x_1544_;
}
pub unsafe fn _init_l_Std_CancellationToken_wait___lam__0___closed__4()
-> *mut leanh::LeanObject {
    let mut v___x_1545_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1546_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1545_ =
        l_Std_Async_Waiter_race___at___00Std_CancellationToken_Consumer_resolve_spec__0___closed__0;
    v___x_1546_ = lean_task_pure(v___x_1545_);
    return v___x_1546_;
}
pub unsafe fn l_Std_CancellationToken_wait___lam__0(
    mut v_a_1547_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_a_1547_) == 0 {
        let mut v___x_1549_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_1549_ = leanh::lean_obj_once(
            core::ptr::addr_of_mut!(l_Std_CancellationToken_wait___lam__0___closed__3),
            core::ptr::addr_of_mut!(l_Std_CancellationToken_wait___lam__0___closed__3_once),
            _init_l_Std_CancellationToken_wait___lam__0___closed__3,
        );
        return v___x_1549_;
    } else {
        let mut v___x_1550_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_1550_ = leanh::lean_obj_once(
            core::ptr::addr_of_mut!(l_Std_CancellationToken_wait___lam__0___closed__4),
            core::ptr::addr_of_mut!(l_Std_CancellationToken_wait___lam__0___closed__4_once),
            _init_l_Std_CancellationToken_wait___lam__0___closed__4,
        );
        return v___x_1550_;
    }
}
pub unsafe fn l_Std_CancellationToken_wait___lam__0___boxed(
    mut v_a_1551_: *mut leanh::LeanObject,
    mut v___y_1552_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1553_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1553_ = l_Std_CancellationToken_wait___lam__0(v_a_1551_);
    leanh::lean_dec(v_a_1551_);
    return v_res_1553_;
}
pub unsafe fn l_Std_CancellationToken_wait___lam__1(
    mut v___f_1554_: *mut leanh::LeanObject,
    mut v___y_1555_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1557_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reason_1558_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1559_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1560_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reason_1561_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_consumers_1562_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1564_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1565_: u8 = 0;
    let mut v___x_1566_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1567_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1569_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1570_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1571_: u8 = 0;
    let mut v___x_1572_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1573_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1574_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1575_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1576_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1577_: u8 = 0;
    let mut v___x_1579_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1580_: u8 = 0;
    let mut v___x_1581_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1583_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1584_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1585_: u8 = 0;
    let mut v_unused_1586_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1557_ = lean_st_ref_get(v___y_1555_);
                v_reason_1558_ = leanh::lean_ctor_get(v___x_1557_, 0);
                leanh::lean_inc(v_reason_1558_);
                leanh::lean_dec(v___x_1557_);
                if leanh::lean_obj_tag(v_reason_1558_) == 0 {
                    v___x_1559_ = lean_io_promise_new();
                    v___x_1560_ = lean_st_ref_take(v___y_1555_);
                    v_reason_1561_ = leanh::lean_ctor_get(v___x_1560_, 0);
                    v_consumers_1562_ = leanh::lean_ctor_get(v___x_1560_, 1);
                    v_isSharedCheck_1577_ = (!leanh::lean_is_exclusive(v___x_1560_)) as u8;
                    if v_isSharedCheck_1577_ == 0 {
                        v___x_1564_ = v___x_1560_;
                        v_isShared_1565_ = v_isSharedCheck_1577_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_consumers_1562_);
                        leanh::lean_inc(v_reason_1561_);
                        leanh::lean_dec(v___x_1560_);
                        v___x_1564_ = leanh::lean_box(0);
                        v_isShared_1565_ = v_isSharedCheck_1577_;
                        state = 1;
                        continue;
                    }
                } else {
                    leanh::lean_dec_ref(v___f_1554_);
                    v_isSharedCheck_1585_ =
                        (!leanh::lean_is_exclusive(v_reason_1558_)) as u8;
                    if v_isSharedCheck_1585_ == 0 {
                        v_unused_1586_ = leanh::lean_ctor_get(v_reason_1558_, 0);
                        leanh::lean_dec(v_unused_1586_);
                        v___x_1579_ = v_reason_1558_;
                        v_isShared_1580_ = v_isSharedCheck_1585_;
                        state = 3;
                        continue;
                    } else {
                        leanh::lean_dec(v_reason_1558_);
                        v___x_1579_ = leanh::lean_box(0);
                        v_isShared_1580_ = v_isSharedCheck_1585_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                leanh::lean_inc(v___x_1559_);
                v___x_1566_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_1566_, 0, v___x_1559_);
                v___x_1567_ = l_Std_Queue_enqueue___redArg(v___x_1566_, v_consumers_1562_);
                if v_isShared_1565_ == 0 {
                    leanh::lean_ctor_set(v___x_1564_, 1, v___x_1567_);
                    v___x_1569_ = v___x_1564_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1576_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1576_, 0, v_reason_1561_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1576_, 1, v___x_1567_);
                    v___x_1569_ = v_reuseFailAlloc_1576_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_1570_ = lean_st_ref_set(v___y_1555_, v___x_1569_);
                v___x_1571_ = 0;
                v___x_1572_ = lean_io_promise_result_opt(v___x_1559_);
                leanh::lean_dec(v___x_1559_);
                v___x_1573_ = leanh::lean_unsigned_to_nat(0);
                v___x_1574_ = lean_io_bind_task(v___x_1572_, v___f_1554_, v___x_1573_, v___x_1571_);
                v___x_1575_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_1575_, 0, v___x_1574_);
                return v___x_1575_;
            }
            3 => {
                v___x_1581_ = leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Std_CancellationToken_wait___lam__0___closed__4),
                    core::ptr::addr_of_mut!(l_Std_CancellationToken_wait___lam__0___closed__4_once),
                    _init_l_Std_CancellationToken_wait___lam__0___closed__4,
                );
                if v_isShared_1580_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_1579_, 0);
                    leanh::lean_ctor_set(v___x_1579_, 0, v___x_1581_);
                    v___x_1583_ = v___x_1579_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1584_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1584_, 0, v___x_1581_);
                    v___x_1583_ = v_reuseFailAlloc_1584_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_1583_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_CancellationToken_wait___lam__1___boxed(
    mut v___f_1587_: *mut leanh::LeanObject,
    mut v___y_1588_: *mut leanh::LeanObject,
    mut v___y_1589_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1590_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1590_ = l_Std_CancellationToken_wait___lam__1(v___f_1587_, v___y_1588_);
    leanh::lean_dec(v___y_1588_);
    return v_res_1590_;
}
pub unsafe fn l_Std_CancellationToken_wait(
    mut v_x_1594_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_1596_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1597_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_1596_ = l_Std_CancellationToken_wait___closed__1;
    v___x_1597_ = l_Std_Mutex_atomically___at___00Std_CancellationToken_wait_spec__0___redArg(
        v_x_1594_,
        v___f_1596_,
    );
    return v___x_1597_;
}
pub unsafe fn l_Std_CancellationToken_wait___boxed(
    mut v_x_1598_: *mut leanh::LeanObject,
    mut v_a_1599_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1600_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1600_ = l_Std_CancellationToken_wait(v_x_1598_);
    return v_res_1600_;
}
pub unsafe fn l_Std_Async_Waiter_race___at___00Std_CancellationToken_selector_spec__0___lam__0(
    mut v___x_1601_: u8,
    mut v_x_1602_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_a_1604_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1606_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1607_: u8 = 0;
    let mut v___x_1609_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1610_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1611_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1612_: u8 = 0;
    let mut v___x_1614_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1615_: u8 = 0;
    let mut v___x_1616_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1618_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1619_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1620_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1621_: u8 = 0;
    let mut v_unused_1622_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_1602_) == 0 {
                    v_a_1604_ = leanh::lean_ctor_get(v_x_1602_, 0);
                    v_isSharedCheck_1612_ = (!leanh::lean_is_exclusive(v_x_1602_)) as u8;
                    if v_isSharedCheck_1612_ == 0 {
                        v___x_1606_ = v_x_1602_;
                        v_isShared_1607_ = v_isSharedCheck_1612_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_1604_);
                        leanh::lean_dec(v_x_1602_);
                        v___x_1606_ = leanh::lean_box(0);
                        v_isShared_1607_ = v_isSharedCheck_1612_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_isSharedCheck_1621_ = (!leanh::lean_is_exclusive(v_x_1602_)) as u8;
                    if v_isSharedCheck_1621_ == 0 {
                        v_unused_1622_ = leanh::lean_ctor_get(v_x_1602_, 0);
                        leanh::lean_dec(v_unused_1622_);
                        v___x_1614_ = v_x_1602_;
                        v_isShared_1615_ = v_isSharedCheck_1621_;
                        state = 3;
                        continue;
                    } else {
                        leanh::lean_dec(v_x_1602_);
                        v___x_1614_ = leanh::lean_box(0);
                        v_isShared_1615_ = v_isSharedCheck_1621_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_1607_ == 0 {
                    v___x_1609_ = v___x_1606_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1611_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1611_, 0, v_a_1604_);
                    v___x_1609_ = v_reuseFailAlloc_1611_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_1610_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_1610_, 0, v___x_1609_);
                return v___x_1610_;
            }
            3 => {
                v___x_1616_ = leanh::lean_box((v___x_1601_) as usize);
                if v_isShared_1615_ == 0 {
                    leanh::lean_ctor_set(v___x_1614_, 0, v___x_1616_);
                    v___x_1618_ = v___x_1614_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1620_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1620_, 0, v___x_1616_);
                    v___x_1618_ = v_reuseFailAlloc_1620_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_1619_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_1619_, 0, v___x_1618_);
                return v___x_1619_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Async_Waiter_race___at___00Std_CancellationToken_selector_spec__0___lam__0___boxed(
    mut v___x_1623_: *mut leanh::LeanObject,
    mut v_x_1624_: *mut leanh::LeanObject,
    mut v___y_1625_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_6814__boxed_1626_: u8 = 0;
    let mut v_res_1627_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_6814__boxed_1626_ = (leanh::lean_unbox(v___x_1623_) as u8);
    v_res_1627_ = l_Std_Async_Waiter_race___at___00Std_CancellationToken_selector_spec__0___lam__0(
        v___x_6814__boxed_1626_,
        v_x_1624_,
    );
    return v_res_1627_;
}
pub unsafe fn l_Std_Async_Waiter_race___at___00Std_CancellationToken_selector_spec__0___lam__1(
    mut v_lose_1628_: *mut leanh::LeanObject,
    mut v___y_1629_: *mut leanh::LeanObject,
    mut v_promise_1630_: *mut leanh::LeanObject,
    mut v___f_1631_: *mut leanh::LeanObject,
    mut v_x_1632_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1634_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1635_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1637_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1638_: u8 = 0;
    let mut v___x_1639_: u8 = 0;
    let mut v___x_1640_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1641_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1642_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1644_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1645_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1646_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1647_: u8 = 0;
    let mut v___x_1648_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1649_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1650_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_1632_) == 0 {
                    leanh::lean_dec_ref(v___f_1631_);
                    leanh::lean_dec_ref(v_lose_1628_);
                    v___x_1634_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_1634_, 0, v_x_1632_);
                    return v___x_1634_;
                } else {
                    v_a_1635_ = leanh::lean_ctor_get(v_x_1632_, 0);
                    v_isSharedCheck_1650_ = (!leanh::lean_is_exclusive(v_x_1632_)) as u8;
                    if v_isSharedCheck_1650_ == 0 {
                        v___x_1637_ = v_x_1632_;
                        v_isShared_1638_ = v_isSharedCheck_1650_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_1635_);
                        leanh::lean_dec(v_x_1632_);
                        v___x_1637_ = leanh::lean_box(0);
                        v_isShared_1638_ = v_isSharedCheck_1650_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_1639_ = (leanh::lean_unbox(v_a_1635_) as u8);
                leanh::lean_dec(v_a_1635_);
                if v___x_1639_ == 0 {
                    leanh::lean_del_object(v___x_1637_);
                    leanh::lean_dec_ref(v___f_1631_);
                    leanh::lean_inc(v___y_1629_);
                    v___x_1640_ = leanh::lean_apply_2(
                        v_lose_1628_,
                        v___y_1629_,
                        leanh::lean_box(0),
                    );
                    return v___x_1640_;
                } else {
                    leanh::lean_dec_ref(v_lose_1628_);
                    v___x_1641_ = l_Std_Async_Waiter_race___at___00Std_CancellationToken_Consumer_resolve_spec__0___closed__0;
                    v___x_1642_ = lean_io_promise_resolve(v___x_1641_, v_promise_1630_);
                    if v_isShared_1638_ == 0 {
                        leanh::lean_ctor_set(v___x_1637_, 0, v___x_1642_);
                        v___x_1644_ = v___x_1637_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_1649_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_1649_, 0, v___x_1642_);
                        v___x_1644_ = v_reuseFailAlloc_1649_;
                        state = 2;
                        continue;
                    }
                }
            }
            2 => {
                v___x_1645_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_1645_, 0, v___x_1644_);
                v___x_1646_ = leanh::lean_unsigned_to_nat(0);
                v___x_1647_ = 0;
                v___x_1648_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(
                    leanh::lean_box(0),
                    leanh::lean_box(0),
                    v___x_1646_,
                    v___x_1647_,
                    v___x_1645_,
                    v___f_1631_,
                );
                return v___x_1648_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Async_Waiter_race___at___00Std_CancellationToken_selector_spec__0___lam__1___boxed(
    mut v_lose_1651_: *mut leanh::LeanObject,
    mut v___y_1652_: *mut leanh::LeanObject,
    mut v_promise_1653_: *mut leanh::LeanObject,
    mut v___f_1654_: *mut leanh::LeanObject,
    mut v_x_1655_: *mut leanh::LeanObject,
    mut v___y_1656_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1657_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1657_ = l_Std_Async_Waiter_race___at___00Std_CancellationToken_selector_spec__0___lam__1(
        v_lose_1651_,
        v___y_1652_,
        v_promise_1653_,
        v___f_1654_,
        v_x_1655_,
    );
    leanh::lean_dec(v_promise_1653_);
    leanh::lean_dec(v___y_1652_);
    return v_res_1657_;
}
pub unsafe fn l_Std_Async_Waiter_race___at___00Std_CancellationToken_selector_spec__0(
    mut v_w_1661_: *mut leanh::LeanObject,
    mut v_lose_1662_: *mut leanh::LeanObject,
    mut v___y_1663_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_finished_1665_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_promise_1666_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1667_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1668_: u8 = 0;
    let mut v___f_1669_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1670_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1672_: u8 = 0;
    let mut v___x_1673_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1674_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1675_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1676_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1677_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1678_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1679_: u8 = 0;
    let mut v___x_1680_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1681_: u8 = 0;
    let mut v___x_1682_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_finished_1665_ = leanh::lean_ctor_get(v_w_1661_, 0);
                leanh::lean_inc(v_finished_1665_);
                v_promise_1666_ = leanh::lean_ctor_get(v_w_1661_, 1);
                leanh::lean_inc(v_promise_1666_);
                leanh::lean_dec_ref(v_w_1661_);
                v___x_1667_ = lean_st_ref_take(v_finished_1665_);
                v___x_1668_ = 1;
                v___f_1669_ = l_Std_Async_Waiter_race___at___00Std_CancellationToken_selector_spec__0___closed__0;
                leanh::lean_inc(v___y_1663_);
                v___f_1670_ = leanh::lean_alloc_closure(l_Std_Async_Waiter_race___at___00Std_CancellationToken_selector_spec__0___lam__1___boxed as *mut core::ffi::c_void, 6, 4);
                leanh::lean_closure_set(v___f_1670_, 0, v_lose_1662_);
                leanh::lean_closure_set(v___f_1670_, 1, v___y_1663_);
                leanh::lean_closure_set(v___f_1670_, 2, v_promise_1666_);
                leanh::lean_closure_set(v___f_1670_, 3, v___f_1669_);
                v___x_1681_ = (leanh::lean_unbox(v___x_1667_) as u8);
                leanh::lean_dec(v___x_1667_);
                if v___x_1681_ == 0 {
                    v___y_1672_ = v___x_1668_;
                    state = 1;
                    continue;
                } else {
                    v___x_1682_ = 0;
                    v___y_1672_ = v___x_1682_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_1673_ = leanh::lean_box((v___x_1668_) as usize);
                v___x_1674_ = lean_st_ref_set(v_finished_1665_, v___x_1673_);
                leanh::lean_dec(v_finished_1665_);
                v___x_1675_ = leanh::lean_box((v___y_1672_) as usize);
                v___x_1676_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_1676_, 0, v___x_1675_);
                v___x_1677_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_1677_, 0, v___x_1676_);
                v___x_1678_ = leanh::lean_unsigned_to_nat(0);
                v___x_1679_ = 0;
                v___x_1680_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(
                    leanh::lean_box(0),
                    leanh::lean_box(0),
                    v___x_1678_,
                    v___x_1679_,
                    v___x_1677_,
                    v___f_1670_,
                );
                return v___x_1680_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Async_Waiter_race___at___00Std_CancellationToken_selector_spec__0___boxed(
    mut v_w_1683_: *mut leanh::LeanObject,
    mut v_lose_1684_: *mut leanh::LeanObject,
    mut v___y_1685_: *mut leanh::LeanObject,
    mut v___y_1686_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1687_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1687_ = l_Std_Async_Waiter_race___at___00Std_CancellationToken_selector_spec__0(
        v_w_1683_,
        v_lose_1684_,
        v___y_1685_,
    );
    leanh::lean_dec(v___y_1685_);
    return v_res_1687_;
}
pub unsafe fn l_Std_Mutex_atomically___at___00Std_CancellationToken_selector_spec__1___redArg___lam__0(
    mut v_mutex_1688_: *mut leanh::LeanObject,
    mut v_x_1689_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1691_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1692_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1693_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1691_ = lean_io_basemutex_unlock(v_mutex_1688_);
    v___x_1692_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_1692_, 0, v___x_1691_);
    v___x_1693_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_1693_, 0, v___x_1692_);
    return v___x_1693_;
}
pub unsafe fn l_Std_Mutex_atomically___at___00Std_CancellationToken_selector_spec__1___redArg___lam__0___boxed(
    mut v_mutex_1694_: *mut leanh::LeanObject,
    mut v_x_1695_: *mut leanh::LeanObject,
    mut v___y_1696_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1697_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1697_ =
        l_Std_Mutex_atomically___at___00Std_CancellationToken_selector_spec__1___redArg___lam__0(
            v_mutex_1694_,
            v_x_1695_,
        );
    leanh::lean_dec(v_x_1695_);
    leanh::lean_dec(v_mutex_1694_);
    return v_res_1697_;
}
pub unsafe fn l_Std_Mutex_atomically___at___00Std_CancellationToken_selector_spec__1___redArg___lam__1(
    mut v_k_1698_: *mut leanh::LeanObject,
    mut v_ref_1699_: *mut leanh::LeanObject,
    mut v_x_1700_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_a_1702_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1704_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1705_: u8 = 0;
    let mut v___x_1707_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1708_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1709_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1710_: u8 = 0;
    let mut v___x_1711_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_1700_) == 0 {
                    leanh::lean_dec(v_ref_1699_);
                    leanh::lean_dec_ref(v_k_1698_);
                    v_a_1702_ = leanh::lean_ctor_get(v_x_1700_, 0);
                    v_isSharedCheck_1710_ = (!leanh::lean_is_exclusive(v_x_1700_)) as u8;
                    if v_isSharedCheck_1710_ == 0 {
                        v___x_1704_ = v_x_1700_;
                        v_isShared_1705_ = v_isSharedCheck_1710_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_1702_);
                        leanh::lean_dec(v_x_1700_);
                        v___x_1704_ = leanh::lean_box(0);
                        v_isShared_1705_ = v_isSharedCheck_1710_;
                        state = 1;
                        continue;
                    }
                } else {
                    leanh::lean_dec_ref_known(v_x_1700_, 1);
                    v___x_1711_ = leanh::lean_apply_2(
                        v_k_1698_,
                        v_ref_1699_,
                        leanh::lean_box(0),
                    );
                    return v___x_1711_;
                }
            }
            1 => {
                if v_isShared_1705_ == 0 {
                    v___x_1707_ = v___x_1704_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1709_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1709_, 0, v_a_1702_);
                    v___x_1707_ = v_reuseFailAlloc_1709_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_1708_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_1708_, 0, v___x_1707_);
                return v___x_1708_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Mutex_atomically___at___00Std_CancellationToken_selector_spec__1___redArg___lam__1___boxed(
    mut v_k_1712_: *mut leanh::LeanObject,
    mut v_ref_1713_: *mut leanh::LeanObject,
    mut v_x_1714_: *mut leanh::LeanObject,
    mut v___y_1715_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1716_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1716_ =
        l_Std_Mutex_atomically___at___00Std_CancellationToken_selector_spec__1___redArg___lam__1(
            v_k_1712_,
            v_ref_1713_,
            v_x_1714_,
        );
    return v_res_1716_;
}
pub unsafe fn l_Std_Mutex_atomically___at___00Std_CancellationToken_selector_spec__1___redArg___lam__2(
    mut v_mutex_1717_: *mut leanh::LeanObject,
    mut v___f_1718_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1720_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1721_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1722_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1723_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1724_: u8 = 0;
    let mut v___x_1725_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1720_ = lean_io_basemutex_lock(v_mutex_1717_);
    v___x_1721_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_1721_, 0, v___x_1720_);
    v___x_1722_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_1722_, 0, v___x_1721_);
    v___x_1723_ = leanh::lean_unsigned_to_nat(0);
    v___x_1724_ = 0;
    v___x_1725_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(
        leanh::lean_box(0),
        leanh::lean_box(0),
        v___x_1723_,
        v___x_1724_,
        v___x_1722_,
        v___f_1718_,
    );
    return v___x_1725_;
}
pub unsafe fn l_Std_Mutex_atomically___at___00Std_CancellationToken_selector_spec__1___redArg___lam__2___boxed(
    mut v_mutex_1726_: *mut leanh::LeanObject,
    mut v___f_1727_: *mut leanh::LeanObject,
    mut v___y_1728_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1729_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1729_ =
        l_Std_Mutex_atomically___at___00Std_CancellationToken_selector_spec__1___redArg___lam__2(
            v_mutex_1726_,
            v___f_1727_,
        );
    leanh::lean_dec(v_mutex_1726_);
    return v_res_1729_;
}
pub unsafe fn l_Std_Mutex_atomically___at___00Std_CancellationToken_selector_spec__1___redArg___lam__3(
    mut v___y_1730_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_a_1731_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1733_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1734_: u8 = 0;
    let mut v___x_1736_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1737_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1738_: u8 = 0;
    let mut v_a_1739_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1741_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1742_: u8 = 0;
    let mut v_fst_1743_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1745_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1746_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1747_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v___y_1730_) == 0 {
                    v_a_1731_ = leanh::lean_ctor_get(v___y_1730_, 0);
                    v_isSharedCheck_1738_ = (!leanh::lean_is_exclusive(v___y_1730_)) as u8;
                    if v_isSharedCheck_1738_ == 0 {
                        v___x_1733_ = v___y_1730_;
                        v_isShared_1734_ = v_isSharedCheck_1738_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_1731_);
                        leanh::lean_dec(v___y_1730_);
                        v___x_1733_ = leanh::lean_box(0);
                        v_isShared_1734_ = v_isSharedCheck_1738_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_1739_ = leanh::lean_ctor_get(v___y_1730_, 0);
                    v_isSharedCheck_1747_ = (!leanh::lean_is_exclusive(v___y_1730_)) as u8;
                    if v_isSharedCheck_1747_ == 0 {
                        v___x_1741_ = v___y_1730_;
                        v_isShared_1742_ = v_isSharedCheck_1747_;
                        state = 3;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_1739_);
                        leanh::lean_dec(v___y_1730_);
                        v___x_1741_ = leanh::lean_box(0);
                        v_isShared_1742_ = v_isSharedCheck_1747_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_1734_ == 0 {
                    v___x_1736_ = v___x_1733_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1737_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1737_, 0, v_a_1731_);
                    v___x_1736_ = v_reuseFailAlloc_1737_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1736_;
            }
            3 => {
                v_fst_1743_ = leanh::lean_ctor_get(v_a_1739_, 0);
                leanh::lean_inc(v_fst_1743_);
                leanh::lean_dec(v_a_1739_);
                if v_isShared_1742_ == 0 {
                    leanh::lean_ctor_set(v___x_1741_, 0, v_fst_1743_);
                    v___x_1745_ = v___x_1741_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1746_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1746_, 0, v_fst_1743_);
                    v___x_1745_ = v_reuseFailAlloc_1746_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_1745_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Mutex_atomically___at___00Std_CancellationToken_selector_spec__1___redArg(
    mut v_mutex_1749_: *mut leanh::LeanObject,
    mut v_k_1750_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_ref_1752_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_mutex_1753_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1754_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1755_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1756_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1757_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1758_: u8 = 0;
    let mut v___x_1759_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1761_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1762_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1763_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1764_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1766_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1767_: u8 = 0;
    let mut v___x_1769_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1770_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1771_: u8 = 0;
    let mut v_a_1772_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1774_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1775_: u8 = 0;
    let mut v_fst_1776_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1778_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1779_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1780_: u8 = 0;
    let mut v_a_1781_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1783_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1784_: u8 = 0;
    let mut v___f_1785_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1786_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1788_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1789_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1790_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ref_1752_ = leanh::lean_ctor_get(v_mutex_1749_, 0);
                leanh::lean_inc(v_ref_1752_);
                v_mutex_1753_ = leanh::lean_ctor_get(v_mutex_1749_, 1);
                leanh::lean_inc_n(v_mutex_1753_, 2);
                leanh::lean_dec_ref(v_mutex_1749_);
                v___f_1754_ = leanh::lean_alloc_closure(l_Std_Mutex_atomically___at___00Std_CancellationToken_selector_spec__1___redArg___lam__0___boxed as *mut core::ffi::c_void, 3, 1);
                leanh::lean_closure_set(v___f_1754_, 0, v_mutex_1753_);
                v___f_1755_ = leanh::lean_alloc_closure(l_Std_Mutex_atomically___at___00Std_CancellationToken_selector_spec__1___redArg___lam__1___boxed as *mut core::ffi::c_void, 4, 2);
                leanh::lean_closure_set(v___f_1755_, 0, v_k_1750_);
                leanh::lean_closure_set(v___f_1755_, 1, v_ref_1752_);
                v___f_1756_ = leanh::lean_alloc_closure(l_Std_Mutex_atomically___at___00Std_CancellationToken_selector_spec__1___redArg___lam__2___boxed as *mut core::ffi::c_void, 3, 2);
                leanh::lean_closure_set(v___f_1756_, 0, v_mutex_1753_);
                leanh::lean_closure_set(v___f_1756_, 1, v___f_1755_);
                v___x_1757_ = leanh::lean_unsigned_to_nat(0);
                v___x_1758_ = 0;
                v___x_1759_ = l_Std_Async_EAsync_tryFinally_x27___redArg(
                    v___f_1756_,
                    v___f_1754_,
                    v___x_1757_,
                    v___x_1758_,
                );
                if leanh::lean_obj_tag(v___x_1759_) == 0 {
                    v_a_1763_ = leanh::lean_ctor_get(v___x_1759_, 0);
                    leanh::lean_inc(v_a_1763_);
                    leanh::lean_dec_ref_known(v___x_1759_, 1);
                    if leanh::lean_obj_tag(v_a_1763_) == 0 {
                        v_a_1764_ = leanh::lean_ctor_get(v_a_1763_, 0);
                        v_isSharedCheck_1771_ = (!leanh::lean_is_exclusive(v_a_1763_)) as u8;
                        if v_isSharedCheck_1771_ == 0 {
                            v___x_1766_ = v_a_1763_;
                            v_isShared_1767_ = v_isSharedCheck_1771_;
                            state = 2;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_1764_);
                            leanh::lean_dec(v_a_1763_);
                            v___x_1766_ = leanh::lean_box(0);
                            v_isShared_1767_ = v_isSharedCheck_1771_;
                            state = 2;
                            continue;
                        }
                    } else {
                        v_a_1772_ = leanh::lean_ctor_get(v_a_1763_, 0);
                        v_isSharedCheck_1780_ = (!leanh::lean_is_exclusive(v_a_1763_)) as u8;
                        if v_isSharedCheck_1780_ == 0 {
                            v___x_1774_ = v_a_1763_;
                            v_isShared_1775_ = v_isSharedCheck_1780_;
                            state = 4;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_1772_);
                            leanh::lean_dec(v_a_1763_);
                            v___x_1774_ = leanh::lean_box(0);
                            v_isShared_1775_ = v_isSharedCheck_1780_;
                            state = 4;
                            continue;
                        }
                    }
                } else {
                    v_a_1781_ = leanh::lean_ctor_get(v___x_1759_, 0);
                    v_isSharedCheck_1790_ = (!leanh::lean_is_exclusive(v___x_1759_)) as u8;
                    if v_isSharedCheck_1790_ == 0 {
                        v___x_1783_ = v___x_1759_;
                        v_isShared_1784_ = v_isSharedCheck_1790_;
                        state = 6;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_1781_);
                        leanh::lean_dec(v___x_1759_);
                        v___x_1783_ = leanh::lean_box(0);
                        v_isShared_1784_ = v_isSharedCheck_1790_;
                        state = 6;
                        continue;
                    }
                }
            }
            1 => {
                v___x_1762_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_1762_, 0, v___y_1761_);
                return v___x_1762_;
            }
            2 => {
                if v_isShared_1767_ == 0 {
                    v___x_1769_ = v___x_1766_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_1770_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1770_, 0, v_a_1764_);
                    v___x_1769_ = v_reuseFailAlloc_1770_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___y_1761_ = v___x_1769_;
                state = 1;
                continue;
            }
            4 => {
                v_fst_1776_ = leanh::lean_ctor_get(v_a_1772_, 0);
                leanh::lean_inc(v_fst_1776_);
                leanh::lean_dec(v_a_1772_);
                if v_isShared_1775_ == 0 {
                    leanh::lean_ctor_set(v___x_1774_, 0, v_fst_1776_);
                    v___x_1778_ = v___x_1774_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_1779_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1779_, 0, v_fst_1776_);
                    v___x_1778_ = v_reuseFailAlloc_1779_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v___y_1761_ = v___x_1778_;
                state = 1;
                continue;
            }
            6 => {
                v___f_1785_ = l_Std_Mutex_atomically___at___00Std_CancellationToken_selector_spec__1___redArg___closed__0;
                v___x_1786_ = lean_task_map(v___f_1785_, v_a_1781_, v___x_1757_, v___x_1758_);
                if v_isShared_1784_ == 0 {
                    leanh::lean_ctor_set(v___x_1783_, 0, v___x_1786_);
                    v___x_1788_ = v___x_1783_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_1789_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1789_, 0, v___x_1786_);
                    v___x_1788_ = v_reuseFailAlloc_1789_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_1788_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Mutex_atomically___at___00Std_CancellationToken_selector_spec__1___redArg___boxed(
    mut v_mutex_1791_: *mut leanh::LeanObject,
    mut v_k_1792_: *mut leanh::LeanObject,
    mut v___y_1793_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1794_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1794_ = l_Std_Mutex_atomically___at___00Std_CancellationToken_selector_spec__1___redArg(
        v_mutex_1791_,
        v_k_1792_,
    );
    return v_res_1794_;
}
pub unsafe fn l_Std_Mutex_atomically___at___00Std_CancellationToken_selector_spec__1(
    mut v_00_u03b1_1795_: *mut leanh::LeanObject,
    mut v_00_u03b2_1796_: *mut leanh::LeanObject,
    mut v_mutex_1797_: *mut leanh::LeanObject,
    mut v_k_1798_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1800_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1800_ = l_Std_Mutex_atomically___at___00Std_CancellationToken_selector_spec__1___redArg(
        v_mutex_1797_,
        v_k_1798_,
    );
    return v___x_1800_;
}
pub unsafe fn l_Std_Mutex_atomically___at___00Std_CancellationToken_selector_spec__1___boxed(
    mut v_00_u03b1_1801_: *mut leanh::LeanObject,
    mut v_00_u03b2_1802_: *mut leanh::LeanObject,
    mut v_mutex_1803_: *mut leanh::LeanObject,
    mut v_k_1804_: *mut leanh::LeanObject,
    mut v___y_1805_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1806_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1806_ = l_Std_Mutex_atomically___at___00Std_CancellationToken_selector_spec__1(
        v_00_u03b1_1801_,
        v_00_u03b2_1802_,
        v_mutex_1803_,
        v_k_1804_,
    );
    return v_res_1806_;
}
pub unsafe fn l_Std_CancellationToken_selector___lam__0(
    mut v___x_1807_: u8,
    mut v___y_1808_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1810_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1811_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1812_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1810_ = leanh::lean_box((v___x_1807_) as usize);
    v___x_1811_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_1811_, 0, v___x_1810_);
    v___x_1812_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_1812_, 0, v___x_1811_);
    return v___x_1812_;
}
pub unsafe fn l_Std_CancellationToken_selector___lam__0___boxed(
    mut v___x_1813_: *mut leanh::LeanObject,
    mut v___y_1814_: *mut leanh::LeanObject,
    mut v___y_1815_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_7132__boxed_1816_: u8 = 0;
    let mut v_res_1817_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_7132__boxed_1816_ = (leanh::lean_unbox(v___x_1813_) as u8);
    v_res_1817_ = l_Std_CancellationToken_selector___lam__0(v___x_7132__boxed_1816_, v___y_1814_);
    leanh::lean_dec(v___y_1814_);
    return v_res_1817_;
}
pub unsafe fn l_Std_CancellationToken_selector___lam__1(
    mut v___x_1818_: *mut leanh::LeanObject,
    mut v___y_1819_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_a_1820_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1822_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1823_: u8 = 0;
    let mut v___x_1825_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1826_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1827_: u8 = 0;
    let mut v___x_1829_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1830_: u8 = 0;
    let mut v___x_1832_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1833_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1834_: u8 = 0;
    let mut v_unused_1835_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v___y_1819_) == 0 {
                    v_a_1820_ = leanh::lean_ctor_get(v___y_1819_, 0);
                    v_isSharedCheck_1827_ = (!leanh::lean_is_exclusive(v___y_1819_)) as u8;
                    if v_isSharedCheck_1827_ == 0 {
                        v___x_1822_ = v___y_1819_;
                        v_isShared_1823_ = v_isSharedCheck_1827_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_1820_);
                        leanh::lean_dec(v___y_1819_);
                        v___x_1822_ = leanh::lean_box(0);
                        v_isShared_1823_ = v_isSharedCheck_1827_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_isSharedCheck_1834_ = (!leanh::lean_is_exclusive(v___y_1819_)) as u8;
                    if v_isSharedCheck_1834_ == 0 {
                        v_unused_1835_ = leanh::lean_ctor_get(v___y_1819_, 0);
                        leanh::lean_dec(v_unused_1835_);
                        v___x_1829_ = v___y_1819_;
                        v_isShared_1830_ = v_isSharedCheck_1834_;
                        state = 3;
                        continue;
                    } else {
                        leanh::lean_dec(v___y_1819_);
                        v___x_1829_ = leanh::lean_box(0);
                        v_isShared_1830_ = v_isSharedCheck_1834_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_1823_ == 0 {
                    v___x_1825_ = v___x_1822_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1826_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1826_, 0, v_a_1820_);
                    v___x_1825_ = v_reuseFailAlloc_1826_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1825_;
            }
            3 => {
                if v_isShared_1830_ == 0 {
                    leanh::lean_ctor_set(v___x_1829_, 0, v___x_1818_);
                    v___x_1832_ = v___x_1829_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1833_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1833_, 0, v___x_1818_);
                    v___x_1832_ = v_reuseFailAlloc_1833_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_1832_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_CancellationToken_selector___lam__2(
    mut v___y_1843_: *mut leanh::LeanObject,
    mut v_waiter_1844_: *mut leanh::LeanObject,
    mut v_x_1845_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_a_1847_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1849_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1850_: u8 = 0;
    let mut v___x_1852_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1853_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1854_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1855_: u8 = 0;
    let mut v_a_1856_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reason_1857_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1858_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reason_1859_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_consumers_1860_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1862_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1863_: u8 = 0;
    let mut v___x_1864_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1865_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1867_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1868_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1869_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1870_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1871_: u8 = 0;
    let mut v___x_1873_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1874_: u8 = 0;
    let mut v___x_1875_: u8 = 0;
    let mut v___f_1876_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1877_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1879_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1881_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1882_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1883_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1884_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1886_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1887_: u8 = 0;
    let mut v___x_1889_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1890_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1891_: u8 = 0;
    let mut v___x_1892_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1893_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1895_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1896_: u8 = 0;
    let mut v___f_1897_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1898_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1899_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1901_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1902_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1903_: u8 = 0;
    let mut v_isSharedCheck_1904_: u8 = 0;
    let mut v_unused_1905_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_1845_) == 0 {
                    leanh::lean_dec_ref(v_waiter_1844_);
                    v_a_1847_ = leanh::lean_ctor_get(v_x_1845_, 0);
                    v_isSharedCheck_1855_ = (!leanh::lean_is_exclusive(v_x_1845_)) as u8;
                    if v_isSharedCheck_1855_ == 0 {
                        v___x_1849_ = v_x_1845_;
                        v_isShared_1850_ = v_isSharedCheck_1855_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_1847_);
                        leanh::lean_dec(v_x_1845_);
                        v___x_1849_ = leanh::lean_box(0);
                        v_isShared_1850_ = v_isSharedCheck_1855_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_1856_ = leanh::lean_ctor_get(v_x_1845_, 0);
                    leanh::lean_inc(v_a_1856_);
                    leanh::lean_dec_ref_known(v_x_1845_, 1);
                    v_reason_1857_ = leanh::lean_ctor_get(v_a_1856_, 0);
                    leanh::lean_inc(v_reason_1857_);
                    leanh::lean_dec(v_a_1856_);
                    if leanh::lean_obj_tag(v_reason_1857_) == 0 {
                        v___x_1858_ = lean_st_ref_take(v___y_1843_);
                        v_reason_1859_ = leanh::lean_ctor_get(v___x_1858_, 0);
                        v_consumers_1860_ = leanh::lean_ctor_get(v___x_1858_, 1);
                        v_isSharedCheck_1871_ =
                            (!leanh::lean_is_exclusive(v___x_1858_)) as u8;
                        if v_isSharedCheck_1871_ == 0 {
                            v___x_1862_ = v___x_1858_;
                            v_isShared_1863_ = v_isSharedCheck_1871_;
                            state = 3;
                            continue;
                        } else {
                            leanh::lean_inc(v_consumers_1860_);
                            leanh::lean_inc(v_reason_1859_);
                            leanh::lean_dec(v___x_1858_);
                            v___x_1862_ = leanh::lean_box(0);
                            v_isShared_1863_ = v_isSharedCheck_1871_;
                            state = 3;
                            continue;
                        }
                    } else {
                        v_isSharedCheck_1904_ =
                            (!leanh::lean_is_exclusive(v_reason_1857_)) as u8;
                        if v_isSharedCheck_1904_ == 0 {
                            v_unused_1905_ = leanh::lean_ctor_get(v_reason_1857_, 0);
                            leanh::lean_dec(v_unused_1905_);
                            v___x_1873_ = v_reason_1857_;
                            v_isShared_1874_ = v_isSharedCheck_1904_;
                            state = 5;
                            continue;
                        } else {
                            leanh::lean_dec(v_reason_1857_);
                            v___x_1873_ = leanh::lean_box(0);
                            v_isShared_1874_ = v_isSharedCheck_1904_;
                            state = 5;
                            continue;
                        }
                    }
                }
            }
            1 => {
                if v_isShared_1850_ == 0 {
                    v___x_1852_ = v___x_1849_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1854_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1854_, 0, v_a_1847_);
                    v___x_1852_ = v_reuseFailAlloc_1854_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_1853_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_1853_, 0, v___x_1852_);
                return v___x_1853_;
            }
            3 => {
                v___x_1864_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_1864_, 0, v_waiter_1844_);
                v___x_1865_ = l_Std_Queue_enqueue___redArg(v___x_1864_, v_consumers_1860_);
                if v_isShared_1863_ == 0 {
                    leanh::lean_ctor_set(v___x_1862_, 1, v___x_1865_);
                    v___x_1867_ = v___x_1862_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1870_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1870_, 0, v_reason_1859_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1870_, 1, v___x_1865_);
                    v___x_1867_ = v_reuseFailAlloc_1870_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_1868_ = lean_st_ref_set(v___y_1843_, v___x_1867_);
                v___x_1869_ = l_Std_CancellationToken_selector___lam__2___closed__0;
                return v___x_1869_;
            }
            5 => {
                v___x_1875_ = 0;
                v___f_1876_ = l_Std_CancellationToken_selector___lam__2___closed__1;
                v___x_1877_ =
                    l_Std_Async_Waiter_race___at___00Std_CancellationToken_selector_spec__0(
                        v_waiter_1844_,
                        v___f_1876_,
                        v___y_1843_,
                    );
                if leanh::lean_obj_tag(v___x_1877_) == 0 {
                    v_a_1883_ = leanh::lean_ctor_get(v___x_1877_, 0);
                    leanh::lean_inc(v_a_1883_);
                    leanh::lean_dec_ref_known(v___x_1877_, 1);
                    if leanh::lean_obj_tag(v_a_1883_) == 0 {
                        v_a_1884_ = leanh::lean_ctor_get(v_a_1883_, 0);
                        v_isSharedCheck_1891_ = (!leanh::lean_is_exclusive(v_a_1883_)) as u8;
                        if v_isSharedCheck_1891_ == 0 {
                            v___x_1886_ = v_a_1883_;
                            v_isShared_1887_ = v_isSharedCheck_1891_;
                            state = 8;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_1884_);
                            leanh::lean_dec(v_a_1883_);
                            v___x_1886_ = leanh::lean_box(0);
                            v_isShared_1887_ = v_isSharedCheck_1891_;
                            state = 8;
                            continue;
                        }
                    } else {
                        leanh::lean_dec_ref_known(v_a_1883_, 1);
                        v___x_1892_ = l_Std_Async_Waiter_race___at___00Std_CancellationToken_Consumer_resolve_spec__0___closed__0;
                        v___y_1879_ = v___x_1892_;
                        state = 6;
                        continue;
                    }
                } else {
                    leanh::lean_del_object(v___x_1873_);
                    v_a_1893_ = leanh::lean_ctor_get(v___x_1877_, 0);
                    v_isSharedCheck_1903_ = (!leanh::lean_is_exclusive(v___x_1877_)) as u8;
                    if v_isSharedCheck_1903_ == 0 {
                        v___x_1895_ = v___x_1877_;
                        v_isShared_1896_ = v_isSharedCheck_1903_;
                        state = 10;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_1893_);
                        leanh::lean_dec(v___x_1877_);
                        v___x_1895_ = leanh::lean_box(0);
                        v_isShared_1896_ = v_isSharedCheck_1903_;
                        state = 10;
                        continue;
                    }
                }
            }
            6 => {
                if v_isShared_1874_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_1873_, 0);
                    leanh::lean_ctor_set(v___x_1873_, 0, v___y_1879_);
                    v___x_1881_ = v___x_1873_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_1882_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1882_, 0, v___y_1879_);
                    v___x_1881_ = v_reuseFailAlloc_1882_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_1881_;
            }
            8 => {
                if v_isShared_1887_ == 0 {
                    v___x_1889_ = v___x_1886_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_1890_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1890_, 0, v_a_1884_);
                    v___x_1889_ = v_reuseFailAlloc_1890_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                v___y_1879_ = v___x_1889_;
                state = 6;
                continue;
            }
            10 => {
                v___f_1897_ = l_Std_CancellationToken_selector___lam__2___closed__2;
                v___x_1898_ = leanh::lean_unsigned_to_nat(0);
                v___x_1899_ = lean_task_map(v___f_1897_, v_a_1893_, v___x_1898_, v___x_1875_);
                if v_isShared_1896_ == 0 {
                    leanh::lean_ctor_set(v___x_1895_, 0, v___x_1899_);
                    v___x_1901_ = v___x_1895_;
                    state = 11;
                    continue;
                } else {
                    v_reuseFailAlloc_1902_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1902_, 0, v___x_1899_);
                    v___x_1901_ = v_reuseFailAlloc_1902_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                return v___x_1901_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_CancellationToken_selector___lam__2___boxed(
    mut v___y_1906_: *mut leanh::LeanObject,
    mut v_waiter_1907_: *mut leanh::LeanObject,
    mut v_x_1908_: *mut leanh::LeanObject,
    mut v___y_1909_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1910_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1910_ = l_Std_CancellationToken_selector___lam__2(v___y_1906_, v_waiter_1907_, v_x_1908_);
    leanh::lean_dec(v___y_1906_);
    return v_res_1910_;
}
pub unsafe fn l_Std_CancellationToken_selector___lam__3(
    mut v_waiter_1911_: *mut leanh::LeanObject,
    mut v___y_1912_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1914_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1915_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1916_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1917_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1918_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1919_: u8 = 0;
    let mut v___x_1920_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1914_ = lean_st_ref_get(v___y_1912_);
    leanh::lean_inc(v___y_1912_);
    v___f_1915_ = leanh::lean_alloc_closure(
        l_Std_CancellationToken_selector___lam__2___boxed as *mut core::ffi::c_void,
        4,
        2,
    );
    leanh::lean_closure_set(v___f_1915_, 0, v___y_1912_);
    leanh::lean_closure_set(v___f_1915_, 1, v_waiter_1911_);
    v___x_1916_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_1916_, 0, v___x_1914_);
    v___x_1917_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_1917_, 0, v___x_1916_);
    v___x_1918_ = leanh::lean_unsigned_to_nat(0);
    v___x_1919_ = 0;
    v___x_1920_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(
        leanh::lean_box(0),
        leanh::lean_box(0),
        v___x_1918_,
        v___x_1919_,
        v___x_1917_,
        v___f_1915_,
    );
    return v___x_1920_;
}
pub unsafe fn l_Std_CancellationToken_selector___lam__3___boxed(
    mut v_waiter_1921_: *mut leanh::LeanObject,
    mut v___y_1922_: *mut leanh::LeanObject,
    mut v___y_1923_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1924_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1924_ = l_Std_CancellationToken_selector___lam__3(v_waiter_1921_, v___y_1922_);
    leanh::lean_dec(v___y_1922_);
    return v_res_1924_;
}
pub unsafe fn l_Std_CancellationToken_selector___lam__4(
    mut v_token_1925_: *mut leanh::LeanObject,
    mut v_waiter_1926_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_1928_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1929_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_1928_ = leanh::lean_alloc_closure(
        l_Std_CancellationToken_selector___lam__3___boxed as *mut core::ffi::c_void,
        3,
        1,
    );
    leanh::lean_closure_set(v___f_1928_, 0, v_waiter_1926_);
    v___x_1929_ = l_Std_Mutex_atomically___at___00Std_CancellationToken_selector_spec__1___redArg(
        v_token_1925_,
        v___f_1928_,
    );
    return v___x_1929_;
}
pub unsafe fn l_Std_CancellationToken_selector___lam__4___boxed(
    mut v_token_1930_: *mut leanh::LeanObject,
    mut v_waiter_1931_: *mut leanh::LeanObject,
    mut v___y_1932_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1933_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1933_ = l_Std_CancellationToken_selector___lam__4(v_token_1930_, v_waiter_1931_);
    return v_res_1933_;
}
pub unsafe fn l_Std_CancellationToken_selector___lam__5(
    mut v_x_1944_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_a_1946_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1948_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1949_: u8 = 0;
    let mut v___x_1951_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1952_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1953_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1954_: u8 = 0;
    let mut v_a_1955_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1956_: u8 = 0;
    let mut v___x_1957_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1958_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_1944_) == 0 {
                    v_a_1946_ = leanh::lean_ctor_get(v_x_1944_, 0);
                    v_isSharedCheck_1954_ = (!leanh::lean_is_exclusive(v_x_1944_)) as u8;
                    if v_isSharedCheck_1954_ == 0 {
                        v___x_1948_ = v_x_1944_;
                        v_isShared_1949_ = v_isSharedCheck_1954_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_1946_);
                        leanh::lean_dec(v_x_1944_);
                        v___x_1948_ = leanh::lean_box(0);
                        v_isShared_1949_ = v_isSharedCheck_1954_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_1955_ = leanh::lean_ctor_get(v_x_1944_, 0);
                    leanh::lean_inc(v_a_1955_);
                    leanh::lean_dec_ref_known(v_x_1944_, 1);
                    v___x_1956_ = (leanh::lean_unbox(v_a_1955_) as u8);
                    leanh::lean_dec(v_a_1955_);
                    if v___x_1956_ == 0 {
                        v___x_1957_ = l_Std_CancellationToken_selector___lam__5___closed__1;
                        return v___x_1957_;
                    } else {
                        v___x_1958_ = l_Std_CancellationToken_selector___lam__5___closed__4;
                        return v___x_1958_;
                    }
                }
            }
            1 => {
                if v_isShared_1949_ == 0 {
                    v___x_1951_ = v___x_1948_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1953_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1953_, 0, v_a_1946_);
                    v___x_1951_ = v_reuseFailAlloc_1953_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_1952_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_1952_, 0, v___x_1951_);
                return v___x_1952_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_CancellationToken_selector___lam__5___boxed(
    mut v_x_1959_: *mut leanh::LeanObject,
    mut v___y_1960_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1961_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1961_ = l_Std_CancellationToken_selector___lam__5(v_x_1959_);
    return v_res_1961_;
}
pub unsafe fn l_Std_CancellationToken_selector___lam__6(
    mut v_token_1962_: *mut leanh::LeanObject,
    mut v___f_1963_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1965_: u8 = 0;
    let mut v___x_1966_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1967_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1968_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1969_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1970_: u8 = 0;
    let mut v___x_1971_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1965_ = l_Std_CancellationToken_isCancelled(v_token_1962_);
    v___x_1966_ = leanh::lean_box((v___x_1965_) as usize);
    v___x_1967_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_1967_, 0, v___x_1966_);
    v___x_1968_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_1968_, 0, v___x_1967_);
    v___x_1969_ = leanh::lean_unsigned_to_nat(0);
    v___x_1970_ = 0;
    v___x_1971_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(
        leanh::lean_box(0),
        leanh::lean_box(0),
        v___x_1969_,
        v___x_1970_,
        v___x_1968_,
        v___f_1963_,
    );
    return v___x_1971_;
}
pub unsafe fn l_Std_CancellationToken_selector___lam__6___boxed(
    mut v_token_1972_: *mut leanh::LeanObject,
    mut v___f_1973_: *mut leanh::LeanObject,
    mut v___y_1974_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1975_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1975_ = l_Std_CancellationToken_selector___lam__6(v_token_1972_, v___f_1973_);
    return v_res_1975_;
}
pub unsafe fn l_Std_CancellationToken_selector___lam__7(
    mut v_reason_1976_: *mut leanh::LeanObject,
    mut v___y_1977_: *mut leanh::LeanObject,
    mut v_x_1978_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_a_1980_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1982_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1983_: u8 = 0;
    let mut v___x_1985_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1986_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1987_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1988_: u8 = 0;
    let mut v_a_1989_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1991_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1992_: u8 = 0;
    let mut v___x_1993_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1994_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1996_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1997_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1998_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1999_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_1978_) == 0 {
                    leanh::lean_dec(v_reason_1976_);
                    v_a_1980_ = leanh::lean_ctor_get(v_x_1978_, 0);
                    v_isSharedCheck_1988_ = (!leanh::lean_is_exclusive(v_x_1978_)) as u8;
                    if v_isSharedCheck_1988_ == 0 {
                        v___x_1982_ = v_x_1978_;
                        v_isShared_1983_ = v_isSharedCheck_1988_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_1980_);
                        leanh::lean_dec(v_x_1978_);
                        v___x_1982_ = leanh::lean_box(0);
                        v_isShared_1983_ = v_isSharedCheck_1988_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_1989_ = leanh::lean_ctor_get(v_x_1978_, 0);
                    v_isSharedCheck_1999_ = (!leanh::lean_is_exclusive(v_x_1978_)) as u8;
                    if v_isSharedCheck_1999_ == 0 {
                        v___x_1991_ = v_x_1978_;
                        v_isShared_1992_ = v_isSharedCheck_1999_;
                        state = 3;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_1989_);
                        leanh::lean_dec(v_x_1978_);
                        v___x_1991_ = leanh::lean_box(0);
                        v_isShared_1992_ = v_isSharedCheck_1999_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_1983_ == 0 {
                    v___x_1985_ = v___x_1982_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1987_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1987_, 0, v_a_1980_);
                    v___x_1985_ = v_reuseFailAlloc_1987_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_1986_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_1986_, 0, v___x_1985_);
                return v___x_1986_;
            }
            3 => {
                v___x_1993_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_1993_, 0, v_reason_1976_);
                leanh::lean_ctor_set(v___x_1993_, 1, v_a_1989_);
                v___x_1994_ = lean_st_ref_set(v___y_1977_, v___x_1993_);
                if v_isShared_1992_ == 0 {
                    leanh::lean_ctor_set(v___x_1991_, 0, v___x_1994_);
                    v___x_1996_ = v___x_1991_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1998_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1998_, 0, v___x_1994_);
                    v___x_1996_ = v_reuseFailAlloc_1998_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_1997_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_1997_, 0, v___x_1996_);
                return v___x_1997_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_CancellationToken_selector___lam__7___boxed(
    mut v_reason_2000_: *mut leanh::LeanObject,
    mut v___y_2001_: *mut leanh::LeanObject,
    mut v_x_2002_: *mut leanh::LeanObject,
    mut v___y_2003_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2004_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2004_ = l_Std_CancellationToken_selector___lam__7(v_reason_2000_, v___y_2001_, v_x_2002_);
    leanh::lean_dec(v___y_2001_);
    return v_res_2004_;
}
pub unsafe fn l_Std_Queue_filterM___at___00Std_CancellationToken_selector_spec__2___lam__0(
    mut v_x_2005_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2007_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2008_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2010_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2011_: u8 = 0;
    let mut v___x_2012_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2014_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2015_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2016_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2017_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_2005_) == 0 {
                    v___x_2007_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_2007_, 0, v_x_2005_);
                    return v___x_2007_;
                } else {
                    v_a_2008_ = leanh::lean_ctor_get(v_x_2005_, 0);
                    v_isSharedCheck_2017_ = (!leanh::lean_is_exclusive(v_x_2005_)) as u8;
                    if v_isSharedCheck_2017_ == 0 {
                        v___x_2010_ = v_x_2005_;
                        v_isShared_2011_ = v_isSharedCheck_2017_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_2008_);
                        leanh::lean_dec(v_x_2005_);
                        v___x_2010_ = leanh::lean_box(0);
                        v_isShared_2011_ = v_isSharedCheck_2017_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_2012_ = l_List_reverse___redArg(v_a_2008_);
                if v_isShared_2011_ == 0 {
                    leanh::lean_ctor_set(v___x_2010_, 0, v___x_2012_);
                    v___x_2014_ = v___x_2010_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2016_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2016_, 0, v___x_2012_);
                    v___x_2014_ = v_reuseFailAlloc_2016_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_2015_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_2015_, 0, v___x_2014_);
                return v___x_2015_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Queue_filterM___at___00Std_CancellationToken_selector_spec__2___lam__0___boxed(
    mut v_x_2018_: *mut leanh::LeanObject,
    mut v___y_2019_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2020_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2020_ =
        l_Std_Queue_filterM___at___00Std_CancellationToken_selector_spec__2___lam__0(v_x_2018_);
    return v_res_2020_;
}
pub unsafe fn l_Std_Queue_filterM___at___00Std_CancellationToken_selector_spec__2___lam__2(
    mut v_a_2021_: *mut leanh::LeanObject,
    mut v___x_2022_: *mut leanh::LeanObject,
    mut v_x_2023_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_a_2025_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2027_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2028_: u8 = 0;
    let mut v___x_2030_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2031_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2032_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2033_: u8 = 0;
    let mut v_a_2034_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2036_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2037_: u8 = 0;
    let mut v___x_2038_: u8 = 0;
    let mut v___x_2039_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2041_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2042_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2043_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2044_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2045_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2047_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2048_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2049_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2050_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_2023_) == 0 {
                    leanh::lean_dec(v___x_2022_);
                    leanh::lean_dec(v_a_2021_);
                    v_a_2025_ = leanh::lean_ctor_get(v_x_2023_, 0);
                    v_isSharedCheck_2033_ = (!leanh::lean_is_exclusive(v_x_2023_)) as u8;
                    if v_isSharedCheck_2033_ == 0 {
                        v___x_2027_ = v_x_2023_;
                        v_isShared_2028_ = v_isSharedCheck_2033_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_2025_);
                        leanh::lean_dec(v_x_2023_);
                        v___x_2027_ = leanh::lean_box(0);
                        v_isShared_2028_ = v_isSharedCheck_2033_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_2034_ = leanh::lean_ctor_get(v_x_2023_, 0);
                    v_isSharedCheck_2050_ = (!leanh::lean_is_exclusive(v_x_2023_)) as u8;
                    if v_isSharedCheck_2050_ == 0 {
                        v___x_2036_ = v_x_2023_;
                        v_isShared_2037_ = v_isSharedCheck_2050_;
                        state = 3;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_2034_);
                        leanh::lean_dec(v_x_2023_);
                        v___x_2036_ = leanh::lean_box(0);
                        v_isShared_2037_ = v_isSharedCheck_2050_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_2028_ == 0 {
                    v___x_2030_ = v___x_2027_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2032_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2032_, 0, v_a_2025_);
                    v___x_2030_ = v_reuseFailAlloc_2032_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_2031_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_2031_, 0, v___x_2030_);
                return v___x_2031_;
            }
            3 => {
                v___x_2038_ = l_List_isEmpty___redArg(v_a_2021_);
                if v___x_2038_ == 0 {
                    leanh::lean_dec(v___x_2022_);
                    v___x_2039_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_2039_, 0, v_a_2034_);
                    leanh::lean_ctor_set(v___x_2039_, 1, v_a_2021_);
                    if v_isShared_2037_ == 0 {
                        leanh::lean_ctor_set(v___x_2036_, 0, v___x_2039_);
                        v___x_2041_ = v___x_2036_;
                        state = 4;
                        continue;
                    } else {
                        v_reuseFailAlloc_2043_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_2043_, 0, v___x_2039_);
                        v___x_2041_ = v_reuseFailAlloc_2043_;
                        state = 4;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v_a_2021_);
                    v___x_2044_ = l_List_reverse___redArg(v_a_2034_);
                    v___x_2045_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_2045_, 0, v___x_2022_);
                    leanh::lean_ctor_set(v___x_2045_, 1, v___x_2044_);
                    if v_isShared_2037_ == 0 {
                        leanh::lean_ctor_set(v___x_2036_, 0, v___x_2045_);
                        v___x_2047_ = v___x_2036_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_2049_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_2049_, 0, v___x_2045_);
                        v___x_2047_ = v_reuseFailAlloc_2049_;
                        state = 5;
                        continue;
                    }
                }
            }
            4 => {
                v___x_2042_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_2042_, 0, v___x_2041_);
                return v___x_2042_;
            }
            5 => {
                v___x_2048_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_2048_, 0, v___x_2047_);
                return v___x_2048_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Queue_filterM___at___00Std_CancellationToken_selector_spec__2___lam__2___boxed(
    mut v_a_2051_: *mut leanh::LeanObject,
    mut v___x_2052_: *mut leanh::LeanObject,
    mut v_x_2053_: *mut leanh::LeanObject,
    mut v___y_2054_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2055_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2055_ = l_Std_Queue_filterM___at___00Std_CancellationToken_selector_spec__2___lam__2(
        v_a_2051_,
        v___x_2052_,
        v_x_2053_,
    );
    return v_res_2055_;
}
pub unsafe fn l_List_filterAuxM___at___00Std_Queue_filterM___at___00Std_CancellationToken_selector_spec__2_spec__2___redArg___lam__1(
    mut v_x_2056_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___y_2059_: u8 = 0;
    let mut v___x_2060_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2061_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2062_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2063_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2064_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2065_: u8 = 0;
    let mut v___x_2066_: u8 = 0;
    let mut v___x_2067_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_2056_) == 0 {
                    v___x_2063_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_2063_, 0, v_x_2056_);
                    return v___x_2063_;
                } else {
                    v_a_2064_ = leanh::lean_ctor_get(v_x_2056_, 0);
                    leanh::lean_inc(v_a_2064_);
                    leanh::lean_dec_ref_known(v_x_2056_, 1);
                    v___x_2065_ = (leanh::lean_unbox(v_a_2064_) as u8);
                    leanh::lean_dec(v_a_2064_);
                    if v___x_2065_ == 0 {
                        v___x_2066_ = 1;
                        v___y_2059_ = v___x_2066_;
                        state = 1;
                        continue;
                    } else {
                        v___x_2067_ = 0;
                        v___y_2059_ = v___x_2067_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_2060_ = leanh::lean_box((v___y_2059_) as usize);
                v___x_2061_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_2061_, 0, v___x_2060_);
                v___x_2062_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_2062_, 0, v___x_2061_);
                return v___x_2062_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_filterAuxM___at___00Std_Queue_filterM___at___00Std_CancellationToken_selector_spec__2_spec__2___redArg___lam__1___boxed(
    mut v_x_2068_: *mut leanh::LeanObject,
    mut v___y_2069_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2070_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2070_ = l_List_filterAuxM___at___00Std_Queue_filterM___at___00Std_CancellationToken_selector_spec__2_spec__2___redArg___lam__1(v_x_2068_);
    return v_res_2070_;
}
pub unsafe fn l_List_filterAuxM___at___00Std_Queue_filterM___at___00Std_CancellationToken_selector_spec__2_spec__2___redArg___lam__0___boxed(
    mut v_tail_2071_: *mut leanh::LeanObject,
    mut v_x_2072_: *mut leanh::LeanObject,
    mut v_head_2073_: *mut leanh::LeanObject,
    mut v_x_2074_: *mut leanh::LeanObject,
    mut v___y_2075_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2076_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2076_ = l_List_filterAuxM___at___00Std_Queue_filterM___at___00Std_CancellationToken_selector_spec__2_spec__2___redArg___lam__0(v_tail_2071_, v_x_2072_, v_head_2073_, v_x_2074_);
    return v_res_2076_;
}
pub unsafe fn l_List_filterAuxM___at___00Std_Queue_filterM___at___00Std_CancellationToken_selector_spec__2_spec__2___redArg(
    mut v_x_2083_: *mut leanh::LeanObject,
    mut v_x_2084_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2086_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2087_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_head_2088_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_2089_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2090_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2092_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2093_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2094_: u8 = 0;
    let mut v___x_2095_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2096_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_finished_2097_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2099_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2100_: u8 = 0;
    let mut v_finished_2101_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2102_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2103_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2105_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2106_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2107_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2108_: u8 = 0;
    let mut v___x_2109_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2110_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2111_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_2083_) == 0 {
                    v___x_2086_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_2086_, 0, v_x_2084_);
                    v___x_2087_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_2087_, 0, v___x_2086_);
                    return v___x_2087_;
                } else {
                    v_head_2088_ = leanh::lean_ctor_get(v_x_2083_, 0);
                    leanh::lean_inc_n(v_head_2088_, 2);
                    v_tail_2089_ = leanh::lean_ctor_get(v_x_2083_, 1);
                    leanh::lean_inc(v_tail_2089_);
                    leanh::lean_dec_ref_known(v_x_2083_, 2);
                    v___f_2090_ = leanh::lean_alloc_closure(l_List_filterAuxM___at___00Std_Queue_filterM___at___00Std_CancellationToken_selector_spec__2_spec__2___redArg___lam__0___boxed as *mut core::ffi::c_void, 5, 3);
                    leanh::lean_closure_set(v___f_2090_, 0, v_tail_2089_);
                    leanh::lean_closure_set(v___f_2090_, 1, v_x_2084_);
                    leanh::lean_closure_set(v___f_2090_, 2, v_head_2088_);
                    if leanh::lean_obj_tag(v_head_2088_) == 0 {
                        leanh::lean_dec_ref_known(v_head_2088_, 1);
                        v___x_2096_ = l_List_filterAuxM___at___00Std_Queue_filterM___at___00Std_CancellationToken_selector_spec__2_spec__2___redArg___closed__1;
                        v_val_2092_ = v___x_2096_;
                        state = 1;
                        continue;
                    } else {
                        v_finished_2097_ = leanh::lean_ctor_get(v_head_2088_, 0);
                        v_isSharedCheck_2111_ =
                            (!leanh::lean_is_exclusive(v_head_2088_)) as u8;
                        if v_isSharedCheck_2111_ == 0 {
                            v___x_2099_ = v_head_2088_;
                            v_isShared_2100_ = v_isSharedCheck_2111_;
                            state = 2;
                            continue;
                        } else {
                            leanh::lean_inc(v_finished_2097_);
                            leanh::lean_dec(v_head_2088_);
                            v___x_2099_ = leanh::lean_box(0);
                            v_isShared_2100_ = v_isSharedCheck_2111_;
                            state = 2;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v___x_2093_ = leanh::lean_unsigned_to_nat(0);
                v___x_2094_ = 0;
                v___x_2095_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(
                    leanh::lean_box(0),
                    leanh::lean_box(0),
                    v___x_2093_,
                    v___x_2094_,
                    v_val_2092_,
                    v___f_2090_,
                );
                return v___x_2095_;
            }
            2 => {
                v_finished_2101_ = leanh::lean_ctor_get(v_finished_2097_, 0);
                leanh::lean_inc(v_finished_2101_);
                leanh::lean_dec_ref(v_finished_2097_);
                v___x_2102_ = lean_st_ref_get(v_finished_2101_);
                leanh::lean_dec(v_finished_2101_);
                v___f_2103_ = l_List_filterAuxM___at___00Std_Queue_filterM___at___00Std_CancellationToken_selector_spec__2_spec__2___redArg___closed__2;
                if v_isShared_2100_ == 0 {
                    leanh::lean_ctor_set(v___x_2099_, 0, v___x_2102_);
                    v___x_2105_ = v___x_2099_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_2110_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2110_, 0, v___x_2102_);
                    v___x_2105_ = v_reuseFailAlloc_2110_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_2106_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_2106_, 0, v___x_2105_);
                v___x_2107_ = leanh::lean_unsigned_to_nat(0);
                v___x_2108_ = 0;
                v___x_2109_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(
                    leanh::lean_box(0),
                    leanh::lean_box(0),
                    v___x_2107_,
                    v___x_2108_,
                    v___x_2106_,
                    v___f_2103_,
                );
                v_val_2092_ = v___x_2109_;
                state = 1;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_filterAuxM___at___00Std_Queue_filterM___at___00Std_CancellationToken_selector_spec__2_spec__2___redArg___lam__0(
    mut v_tail_2112_: *mut leanh::LeanObject,
    mut v_x_2113_: *mut leanh::LeanObject,
    mut v_head_2114_: *mut leanh::LeanObject,
    mut v_x_2115_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_a_2117_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2119_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2120_: u8 = 0;
    let mut v___x_2122_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2123_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2124_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2125_: u8 = 0;
    let mut v_a_2126_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2127_: u8 = 0;
    let mut v___x_2128_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2129_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2130_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_2115_) == 0 {
                    leanh::lean_dec_ref(v_head_2114_);
                    leanh::lean_dec(v_x_2113_);
                    leanh::lean_dec(v_tail_2112_);
                    v_a_2117_ = leanh::lean_ctor_get(v_x_2115_, 0);
                    v_isSharedCheck_2125_ = (!leanh::lean_is_exclusive(v_x_2115_)) as u8;
                    if v_isSharedCheck_2125_ == 0 {
                        v___x_2119_ = v_x_2115_;
                        v_isShared_2120_ = v_isSharedCheck_2125_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_2117_);
                        leanh::lean_dec(v_x_2115_);
                        v___x_2119_ = leanh::lean_box(0);
                        v_isShared_2120_ = v_isSharedCheck_2125_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_2126_ = leanh::lean_ctor_get(v_x_2115_, 0);
                    leanh::lean_inc(v_a_2126_);
                    leanh::lean_dec_ref_known(v_x_2115_, 1);
                    v___x_2127_ = (leanh::lean_unbox(v_a_2126_) as u8);
                    leanh::lean_dec(v_a_2126_);
                    if v___x_2127_ == 0 {
                        leanh::lean_dec_ref(v_head_2114_);
                        v___x_2128_ = l_List_filterAuxM___at___00Std_Queue_filterM___at___00Std_CancellationToken_selector_spec__2_spec__2___redArg(v_tail_2112_, v_x_2113_);
                        return v___x_2128_;
                    } else {
                        v___x_2129_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                        leanh::lean_ctor_set(v___x_2129_, 0, v_head_2114_);
                        leanh::lean_ctor_set(v___x_2129_, 1, v_x_2113_);
                        v___x_2130_ = l_List_filterAuxM___at___00Std_Queue_filterM___at___00Std_CancellationToken_selector_spec__2_spec__2___redArg(v_tail_2112_, v___x_2129_);
                        return v___x_2130_;
                    }
                }
            }
            1 => {
                if v_isShared_2120_ == 0 {
                    v___x_2122_ = v___x_2119_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2124_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2124_, 0, v_a_2117_);
                    v___x_2122_ = v_reuseFailAlloc_2124_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_2123_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_2123_, 0, v___x_2122_);
                return v___x_2123_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_filterAuxM___at___00Std_Queue_filterM___at___00Std_CancellationToken_selector_spec__2_spec__2___redArg___boxed(
    mut v_x_2131_: *mut leanh::LeanObject,
    mut v_x_2132_: *mut leanh::LeanObject,
    mut v___y_2133_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2134_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2134_ = l_List_filterAuxM___at___00Std_Queue_filterM___at___00Std_CancellationToken_selector_spec__2_spec__2___redArg(v_x_2131_, v_x_2132_);
    return v_res_2134_;
}
pub unsafe fn l_Std_Queue_filterM___at___00Std_CancellationToken_selector_spec__2___lam__1(
    mut v_eList_2135_: *mut leanh::LeanObject,
    mut v___x_2136_: *mut leanh::LeanObject,
    mut v___f_2137_: *mut leanh::LeanObject,
    mut v_x_2138_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_a_2140_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2142_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2143_: u8 = 0;
    let mut v___x_2145_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2146_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2147_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2148_: u8 = 0;
    let mut v_a_2149_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2150_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2151_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2152_: u8 = 0;
    let mut v___x_2153_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2154_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2155_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_2138_) == 0 {
                    leanh::lean_dec_ref(v___f_2137_);
                    leanh::lean_dec(v___x_2136_);
                    leanh::lean_dec(v_eList_2135_);
                    v_a_2140_ = leanh::lean_ctor_get(v_x_2138_, 0);
                    v_isSharedCheck_2148_ = (!leanh::lean_is_exclusive(v_x_2138_)) as u8;
                    if v_isSharedCheck_2148_ == 0 {
                        v___x_2142_ = v_x_2138_;
                        v_isShared_2143_ = v_isSharedCheck_2148_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_2140_);
                        leanh::lean_dec(v_x_2138_);
                        v___x_2142_ = leanh::lean_box(0);
                        v_isShared_2143_ = v_isSharedCheck_2148_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_2149_ = leanh::lean_ctor_get(v_x_2138_, 0);
                    leanh::lean_inc(v_a_2149_);
                    leanh::lean_dec_ref_known(v_x_2138_, 1);
                    leanh::lean_inc(v___x_2136_);
                    v___x_2150_ = l_List_filterAuxM___at___00Std_Queue_filterM___at___00Std_CancellationToken_selector_spec__2_spec__2___redArg(v_eList_2135_, v___x_2136_);
                    v___x_2151_ = leanh::lean_unsigned_to_nat(0);
                    v___x_2152_ = 0;
                    v___x_2153_ =
                        l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(
                            leanh::lean_box(0),
                            leanh::lean_box(0),
                            v___x_2151_,
                            v___x_2152_,
                            v___x_2150_,
                            v___f_2137_,
                        );
                    v___f_2154_ = leanh::lean_alloc_closure(l_Std_Queue_filterM___at___00Std_CancellationToken_selector_spec__2___lam__2___boxed as *mut core::ffi::c_void, 4, 2);
                    leanh::lean_closure_set(v___f_2154_, 0, v_a_2149_);
                    leanh::lean_closure_set(v___f_2154_, 1, v___x_2136_);
                    v___x_2155_ =
                        l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(
                            leanh::lean_box(0),
                            leanh::lean_box(0),
                            v___x_2151_,
                            v___x_2152_,
                            v___x_2153_,
                            v___f_2154_,
                        );
                    return v___x_2155_;
                }
            }
            1 => {
                if v_isShared_2143_ == 0 {
                    v___x_2145_ = v___x_2142_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2147_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2147_, 0, v_a_2140_);
                    v___x_2145_ = v_reuseFailAlloc_2147_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_2146_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_2146_, 0, v___x_2145_);
                return v___x_2146_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Queue_filterM___at___00Std_CancellationToken_selector_spec__2___lam__1___boxed(
    mut v_eList_2156_: *mut leanh::LeanObject,
    mut v___x_2157_: *mut leanh::LeanObject,
    mut v___f_2158_: *mut leanh::LeanObject,
    mut v_x_2159_: *mut leanh::LeanObject,
    mut v___y_2160_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2161_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2161_ = l_Std_Queue_filterM___at___00Std_CancellationToken_selector_spec__2___lam__1(
        v_eList_2156_,
        v___x_2157_,
        v___f_2158_,
        v_x_2159_,
    );
    return v_res_2161_;
}
pub unsafe fn l_Std_Queue_filterM___at___00Std_CancellationToken_selector_spec__2(
    mut v_q_2163_: *mut leanh::LeanObject,
    mut v___y_2164_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_eList_2166_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_dList_2167_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2168_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2169_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2170_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2171_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2172_: u8 = 0;
    let mut v___x_2173_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2174_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2175_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_eList_2166_ = leanh::lean_ctor_get(v_q_2163_, 0);
    leanh::lean_inc(v_eList_2166_);
    v_dList_2167_ = leanh::lean_ctor_get(v_q_2163_, 1);
    leanh::lean_inc(v_dList_2167_);
    leanh::lean_dec_ref(v_q_2163_);
    v___x_2168_ = leanh::lean_box(0);
    v___x_2169_ = l_List_filterAuxM___at___00Std_Queue_filterM___at___00Std_CancellationToken_selector_spec__2_spec__2___redArg(v_dList_2167_, v___x_2168_);
    v___f_2170_ = l_Std_Queue_filterM___at___00Std_CancellationToken_selector_spec__2___closed__0;
    v___x_2171_ = leanh::lean_unsigned_to_nat(0);
    v___x_2172_ = 0;
    v___x_2173_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(
        leanh::lean_box(0),
        leanh::lean_box(0),
        v___x_2171_,
        v___x_2172_,
        v___x_2169_,
        v___f_2170_,
    );
    v___f_2174_ = leanh::lean_alloc_closure(
        l_Std_Queue_filterM___at___00Std_CancellationToken_selector_spec__2___lam__1___boxed
            as *mut core::ffi::c_void,
        5,
        3,
    );
    leanh::lean_closure_set(v___f_2174_, 0, v_eList_2166_);
    leanh::lean_closure_set(v___f_2174_, 1, v___x_2168_);
    leanh::lean_closure_set(v___f_2174_, 2, v___f_2170_);
    v___x_2175_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(
        leanh::lean_box(0),
        leanh::lean_box(0),
        v___x_2171_,
        v___x_2172_,
        v___x_2173_,
        v___f_2174_,
    );
    return v___x_2175_;
}
pub unsafe fn l_Std_Queue_filterM___at___00Std_CancellationToken_selector_spec__2___boxed(
    mut v_q_2176_: *mut leanh::LeanObject,
    mut v___y_2177_: *mut leanh::LeanObject,
    mut v___y_2178_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2179_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2179_ =
        l_Std_Queue_filterM___at___00Std_CancellationToken_selector_spec__2(v_q_2176_, v___y_2177_);
    leanh::lean_dec(v___y_2177_);
    return v_res_2179_;
}
pub unsafe fn l_Std_CancellationToken_selector___lam__8(
    mut v___y_2180_: *mut leanh::LeanObject,
    mut v_x_2181_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_a_2183_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2185_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2186_: u8 = 0;
    let mut v___x_2188_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2189_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2190_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2191_: u8 = 0;
    let mut v_a_2192_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reason_2193_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_consumers_2194_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2195_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2196_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2197_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2198_: u8 = 0;
    let mut v___x_2199_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_2181_) == 0 {
                    v_a_2183_ = leanh::lean_ctor_get(v_x_2181_, 0);
                    v_isSharedCheck_2191_ = (!leanh::lean_is_exclusive(v_x_2181_)) as u8;
                    if v_isSharedCheck_2191_ == 0 {
                        v___x_2185_ = v_x_2181_;
                        v_isShared_2186_ = v_isSharedCheck_2191_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_2183_);
                        leanh::lean_dec(v_x_2181_);
                        v___x_2185_ = leanh::lean_box(0);
                        v_isShared_2186_ = v_isSharedCheck_2191_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_2192_ = leanh::lean_ctor_get(v_x_2181_, 0);
                    leanh::lean_inc(v_a_2192_);
                    leanh::lean_dec_ref_known(v_x_2181_, 1);
                    v_reason_2193_ = leanh::lean_ctor_get(v_a_2192_, 0);
                    leanh::lean_inc(v_reason_2193_);
                    v_consumers_2194_ = leanh::lean_ctor_get(v_a_2192_, 1);
                    leanh::lean_inc_ref(v_consumers_2194_);
                    leanh::lean_dec(v_a_2192_);
                    v___x_2195_ =
                        l_Std_Queue_filterM___at___00Std_CancellationToken_selector_spec__2(
                            v_consumers_2194_,
                            v___y_2180_,
                        );
                    leanh::lean_inc(v___y_2180_);
                    v___f_2196_ = leanh::lean_alloc_closure(
                        l_Std_CancellationToken_selector___lam__7___boxed as *mut core::ffi::c_void,
                        4,
                        2,
                    );
                    leanh::lean_closure_set(v___f_2196_, 0, v_reason_2193_);
                    leanh::lean_closure_set(v___f_2196_, 1, v___y_2180_);
                    v___x_2197_ = leanh::lean_unsigned_to_nat(0);
                    v___x_2198_ = 0;
                    v___x_2199_ =
                        l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(
                            leanh::lean_box(0),
                            leanh::lean_box(0),
                            v___x_2197_,
                            v___x_2198_,
                            v___x_2195_,
                            v___f_2196_,
                        );
                    return v___x_2199_;
                }
            }
            1 => {
                if v_isShared_2186_ == 0 {
                    v___x_2188_ = v___x_2185_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2190_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2190_, 0, v_a_2183_);
                    v___x_2188_ = v_reuseFailAlloc_2190_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_2189_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_2189_, 0, v___x_2188_);
                return v___x_2189_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_CancellationToken_selector___lam__8___boxed(
    mut v___y_2200_: *mut leanh::LeanObject,
    mut v_x_2201_: *mut leanh::LeanObject,
    mut v___y_2202_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2203_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2203_ = l_Std_CancellationToken_selector___lam__8(v___y_2200_, v_x_2201_);
    leanh::lean_dec(v___y_2200_);
    return v_res_2203_;
}
pub unsafe fn l_Std_CancellationToken_selector___lam__9(
    mut v___y_2204_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2206_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2207_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2208_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2209_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2210_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2211_: u8 = 0;
    let mut v___x_2212_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2206_ = lean_st_ref_get(v___y_2204_);
    leanh::lean_inc(v___y_2204_);
    v___f_2207_ = leanh::lean_alloc_closure(
        l_Std_CancellationToken_selector___lam__8___boxed as *mut core::ffi::c_void,
        3,
        1,
    );
    leanh::lean_closure_set(v___f_2207_, 0, v___y_2204_);
    v___x_2208_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_2208_, 0, v___x_2206_);
    v___x_2209_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_2209_, 0, v___x_2208_);
    v___x_2210_ = leanh::lean_unsigned_to_nat(0);
    v___x_2211_ = 0;
    v___x_2212_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(
        leanh::lean_box(0),
        leanh::lean_box(0),
        v___x_2210_,
        v___x_2211_,
        v___x_2209_,
        v___f_2207_,
    );
    return v___x_2212_;
}
pub unsafe fn l_Std_CancellationToken_selector___lam__9___boxed(
    mut v___y_2213_: *mut leanh::LeanObject,
    mut v___y_2214_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2215_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2215_ = l_Std_CancellationToken_selector___lam__9(v___y_2213_);
    leanh::lean_dec(v___y_2213_);
    return v_res_2215_;
}
pub unsafe fn l_Std_CancellationToken_selector(
    mut v_token_2218_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_2219_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2220_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2221_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2222_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2223_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2224_: *mut leanh::LeanObject = core::ptr::null_mut();
    leanh::lean_inc_ref_n(v_token_2218_, 2);
    v___f_2219_ = leanh::lean_alloc_closure(
        l_Std_CancellationToken_selector___lam__4___boxed as *mut core::ffi::c_void,
        3,
        1,
    );
    leanh::lean_closure_set(v___f_2219_, 0, v_token_2218_);
    v___f_2220_ = l_Std_CancellationToken_selector___closed__0;
    v___f_2221_ = leanh::lean_alloc_closure(
        l_Std_CancellationToken_selector___lam__6___boxed as *mut core::ffi::c_void,
        3,
        2,
    );
    leanh::lean_closure_set(v___f_2221_, 0, v_token_2218_);
    leanh::lean_closure_set(v___f_2221_, 1, v___f_2220_);
    v___f_2222_ = l_Std_CancellationToken_selector___closed__1;
    v___x_2223_ = leanh::lean_alloc_closure(
        l_Std_Mutex_atomically___at___00Std_CancellationToken_selector_spec__1___boxed
            as *mut core::ffi::c_void,
        5,
        4,
    );
    leanh::lean_closure_set(v___x_2223_, 0, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_2223_, 1, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_2223_, 2, v_token_2218_);
    leanh::lean_closure_set(v___x_2223_, 3, v___f_2222_);
    v___x_2224_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
    leanh::lean_ctor_set(v___x_2224_, 0, v___f_2221_);
    leanh::lean_ctor_set(v___x_2224_, 1, v___f_2219_);
    leanh::lean_ctor_set(v___x_2224_, 2, v___x_2223_);
    return v___x_2224_;
}
pub unsafe fn l_List_filterAuxM___at___00Std_Queue_filterM___at___00Std_CancellationToken_selector_spec__2_spec__2(
    mut v_x_2225_: *mut leanh::LeanObject,
    mut v_x_2226_: *mut leanh::LeanObject,
    mut v___y_2227_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2229_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2229_ = l_List_filterAuxM___at___00Std_Queue_filterM___at___00Std_CancellationToken_selector_spec__2_spec__2___redArg(v_x_2225_, v_x_2226_);
    return v___x_2229_;
}
pub unsafe fn l_List_filterAuxM___at___00Std_Queue_filterM___at___00Std_CancellationToken_selector_spec__2_spec__2___boxed(
    mut v_x_2230_: *mut leanh::LeanObject,
    mut v_x_2231_: *mut leanh::LeanObject,
    mut v___y_2232_: *mut leanh::LeanObject,
    mut v___y_2233_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2234_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2234_ = l_List_filterAuxM___at___00Std_Queue_filterM___at___00Std_CancellationToken_selector_spec__2_spec__2(v_x_2230_, v_x_2231_, v___y_2232_);
    leanh::lean_dec(v___y_2232_);
    return v_res_2234_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Std_Sync_CancellationToken(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Std_Data(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
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
    res = runtime_initialize_Init_Data_ToString_Macro(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Std_Sync_CancellationToken(
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
pub unsafe fn initialize_Std_Sync_CancellationToken(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Std_Data(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
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
    res = initialize_Init_Data_ToString_Macro(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Std_Sync_CancellationToken(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = meta_initialize_Std_Sync_CancellationToken(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return initialize_Std_Sync_CancellationToken(builtin);
}