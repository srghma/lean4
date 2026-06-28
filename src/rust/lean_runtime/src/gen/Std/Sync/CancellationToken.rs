// Lean compiler output
// Module: Std.Sync.CancellationToken
// Imports: Std.Data Init.Data.Queue Std.Sync.Mutex Std.Async.Select Init.Data.ToString.Macro
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
use crate::lean_imports_rs::Init::Core::{lean_task_map, lean_task_pure};
use crate::lean_imports_rs::Init::Data::Int::Basic::lean_nat_to_int;
use crate::lean_imports_rs::Init::Data::String::Defs::lean_string_append;
use crate::lean_imports_rs::Init::Prelude::{lean_nat_dec_le, lean_string_dec_eq};
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
    lean_apply_2, lean_box, lean_closure_set, lean_ctor_get, lean_ctor_set, lean_ctor_set_tag,
    lean_ctor_set_uint8, lean_dec, lean_dec_ref, lean_dec_ref_known, lean_del_object, lean_inc,
    lean_inc_n, lean_inc_ref, lean_inc_ref_n, lean_io_result_is_error, lean_io_result_mk_ok,
    lean_is_exclusive, lean_obj_once, lean_obj_tag, lean_unbox, lean_unsigned_to_nat,
};
pub static l_Std_instReprCancellationReason_repr___closed__0_value: LeanStringObject<30> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 30,
        m_capacity: 30,
        m_length: 29,
        m_data: [
            83, 116, 100, 46, 67, 97, 110, 99, 101, 108, 108, 97, 116, 105, 111, 110, 82, 101, 97,
            115, 111, 110, 46, 99, 97, 110, 99, 101, 108, 0,
        ],
    };
static mut l_Std_instReprCancellationReason_repr___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Std_instReprCancellationReason_repr___closed__0_value) as *mut LeanObject;
pub static l_Std_instReprCancellationReason_repr___closed__1_value: LeanCtorObject<1> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 3,
        },
        m_objs: [
            core::ptr::addr_of!(l_Std_instReprCancellationReason_repr___closed__0_value)
                as *mut LeanObject,
        ],
    };
static mut l_Std_instReprCancellationReason_repr___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Std_instReprCancellationReason_repr___closed__1_value) as *mut LeanObject;
pub static l_Std_instReprCancellationReason_repr___closed__2_value: LeanStringObject<32> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 32,
        m_capacity: 32,
        m_length: 31,
        m_data: [
            83, 116, 100, 46, 67, 97, 110, 99, 101, 108, 108, 97, 116, 105, 111, 110, 82, 101, 97,
            115, 111, 110, 46, 115, 104, 117, 116, 100, 111, 119, 110, 0,
        ],
    };
static mut l_Std_instReprCancellationReason_repr___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Std_instReprCancellationReason_repr___closed__2_value) as *mut LeanObject;
pub static l_Std_instReprCancellationReason_repr___closed__3_value: LeanCtorObject<1> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 3,
        },
        m_objs: [
            core::ptr::addr_of!(l_Std_instReprCancellationReason_repr___closed__2_value)
                as *mut LeanObject,
        ],
    };
static mut l_Std_instReprCancellationReason_repr___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Std_instReprCancellationReason_repr___closed__3_value) as *mut LeanObject;
pub static l_Std_instReprCancellationReason_repr___closed__4_value: LeanStringObject<32> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 32,
        m_capacity: 32,
        m_length: 31,
        m_data: [
            83, 116, 100, 46, 67, 97, 110, 99, 101, 108, 108, 97, 116, 105, 111, 110, 82, 101, 97,
            115, 111, 110, 46, 100, 101, 97, 100, 108, 105, 110, 101, 0,
        ],
    };
static mut l_Std_instReprCancellationReason_repr___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Std_instReprCancellationReason_repr___closed__4_value) as *mut LeanObject;
pub static l_Std_instReprCancellationReason_repr___closed__5_value: LeanCtorObject<1> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 3,
        },
        m_objs: [
            core::ptr::addr_of!(l_Std_instReprCancellationReason_repr___closed__4_value)
                as *mut LeanObject,
        ],
    };
static mut l_Std_instReprCancellationReason_repr___closed__5: *mut LeanObject =
    core::ptr::addr_of!(l_Std_instReprCancellationReason_repr___closed__5_value) as *mut LeanObject;
static mut l_Std_instReprCancellationReason_repr___closed__6_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_instReprCancellationReason_repr___closed__6: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Std_instReprCancellationReason_repr___closed__7_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_instReprCancellationReason_repr___closed__7: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Std_instReprCancellationReason_repr___closed__8_value: LeanStringObject<30> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 30,
        m_capacity: 30,
        m_length: 29,
        m_data: [
            83, 116, 100, 46, 67, 97, 110, 99, 101, 108, 108, 97, 116, 105, 111, 110, 82, 101, 97,
            115, 111, 110, 46, 99, 117, 115, 116, 111, 109, 0,
        ],
    };
static mut l_Std_instReprCancellationReason_repr___closed__8: *mut LeanObject =
    core::ptr::addr_of!(l_Std_instReprCancellationReason_repr___closed__8_value) as *mut LeanObject;
pub static l_Std_instReprCancellationReason_repr___closed__9_value: LeanCtorObject<1> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 3,
        },
        m_objs: [
            core::ptr::addr_of!(l_Std_instReprCancellationReason_repr___closed__8_value)
                as *mut LeanObject,
        ],
    };
static mut l_Std_instReprCancellationReason_repr___closed__9: *mut LeanObject =
    core::ptr::addr_of!(l_Std_instReprCancellationReason_repr___closed__9_value) as *mut LeanObject;
pub static l_Std_instReprCancellationReason_repr___closed__10_value: LeanCtorObject<2> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 5,
        },
        m_objs: [
            core::ptr::addr_of!(l_Std_instReprCancellationReason_repr___closed__9_value)
                as *mut LeanObject,
            (((1 as usize) << 1) | 1) as *mut LeanObject,
        ],
    };
static mut l_Std_instReprCancellationReason_repr___closed__10: *mut LeanObject =
    core::ptr::addr_of!(l_Std_instReprCancellationReason_repr___closed__10_value)
        as *mut LeanObject;
pub static l_Std_instReprCancellationReason___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_Std_instReprCancellationReason_repr___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Std_instReprCancellationReason___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Std_instReprCancellationReason___closed__0_value) as *mut LeanObject;
pub static mut l_Std_instReprCancellationReason: *mut LeanObject =
    core::ptr::addr_of!(l_Std_instReprCancellationReason___closed__0_value) as *mut LeanObject;
pub static l_Std_instBEqCancellationReason___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_Std_instBEqCancellationReason_beq___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Std_instBEqCancellationReason___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Std_instBEqCancellationReason___closed__0_value) as *mut LeanObject;
pub static mut l_Std_instBEqCancellationReason: *mut LeanObject =
    core::ptr::addr_of!(l_Std_instBEqCancellationReason___closed__0_value) as *mut LeanObject;
pub static l_Std_instToStringCancellationReason___lam__0___closed__0_value: LeanStringObject<9> =
    LeanStringObject {
        m_header: LeanObject {
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
static mut l_Std_instToStringCancellationReason___lam__0___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Std_instToStringCancellationReason___lam__0___closed__0_value)
        as *mut LeanObject;
pub static l_Std_instToStringCancellationReason___lam__0___closed__1_value: LeanStringObject<9> =
    LeanStringObject {
        m_header: LeanObject {
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
static mut l_Std_instToStringCancellationReason___lam__0___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Std_instToStringCancellationReason___lam__0___closed__1_value)
        as *mut LeanObject;
pub static l_Std_instToStringCancellationReason___lam__0___closed__2_value: LeanStringObject<7> =
    LeanStringObject {
        m_header: LeanObject {
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
static mut l_Std_instToStringCancellationReason___lam__0___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Std_instToStringCancellationReason___lam__0___closed__2_value)
        as *mut LeanObject;
pub static l_Std_instToStringCancellationReason___lam__0___closed__3_value: LeanStringObject<9> =
    LeanStringObject {
        m_header: LeanObject {
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
static mut l_Std_instToStringCancellationReason___lam__0___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Std_instToStringCancellationReason___lam__0___closed__3_value)
        as *mut LeanObject;
pub static l_Std_instToStringCancellationReason___lam__0___closed__4_value: LeanStringObject<3> =
    LeanStringObject {
        m_header: LeanObject {
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
static mut l_Std_instToStringCancellationReason___lam__0___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Std_instToStringCancellationReason___lam__0___closed__4_value)
        as *mut LeanObject;
pub static l_Std_instToStringCancellationReason___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_Std_instToStringCancellationReason___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Std_instToStringCancellationReason___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Std_instToStringCancellationReason___closed__0_value) as *mut LeanObject;
pub static mut l_Std_instToStringCancellationReason: *mut LeanObject =
    core::ptr::addr_of!(l_Std_instToStringCancellationReason___closed__0_value) as *mut LeanObject;
pub static l_Std_Async_Waiter_race___at___00Std_CancellationToken_Consumer_resolve_spec__0___closed__0_value: LeanCtorObject<1> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*1 + 0) as u16, other: 1, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject] };
static mut l_Std_Async_Waiter_race___at___00Std_CancellationToken_Consumer_resolve_spec__0___closed__0: *mut LeanObject = core::ptr::addr_of!(l_Std_Async_Waiter_race___at___00Std_CancellationToken_Consumer_resolve_spec__0___closed__0_value) as *mut LeanObject;
pub static l_Std_CancellationToken_Consumer_resolve___closed__0_value: LeanClosureObject<1> =
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
        m_fun: l_Std_CancellationToken_Consumer_resolve___lam__0___boxed
            as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 1,
        m_objs: [(((0 as usize) << 1) | 1) as *mut LeanObject],
    };
static mut l_Std_CancellationToken_Consumer_resolve___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Std_CancellationToken_Consumer_resolve___closed__0_value)
        as *mut LeanObject;
static mut l_Std_CancellationToken_new___closed__0_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_CancellationToken_new___closed__0: *mut LeanObject = core::ptr::null_mut();
static mut l_Std_CancellationToken_new___closed__1_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_CancellationToken_new___closed__1: *mut LeanObject = core::ptr::null_mut();
pub static l_Std_CancellationToken_isCancelled___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_Std_CancellationToken_isCancelled___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Std_CancellationToken_isCancelled___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Std_CancellationToken_isCancelled___closed__0_value) as *mut LeanObject;
pub static l_Std_CancellationToken_getCancellationReason___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_Std_CancellationToken_getCancellationReason___lam__0___boxed
            as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Std_CancellationToken_getCancellationReason___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Std_CancellationToken_getCancellationReason___closed__0_value)
        as *mut LeanObject;
pub static l_Std_CancellationToken_wait___lam__0___closed__0_value: LeanStringObject<27> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 27,
        m_capacity: 27,
        m_length: 26,
        m_data: [
            99, 97, 110, 99, 101, 108, 108, 97, 116, 105, 111, 110, 32, 116, 111, 107, 101, 110,
            32, 100, 114, 111, 112, 112, 101, 100, 0,
        ],
    };
static mut l_Std_CancellationToken_wait___lam__0___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Std_CancellationToken_wait___lam__0___closed__0_value) as *mut LeanObject;
static mut l_Std_CancellationToken_wait___lam__0___closed__1_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_CancellationToken_wait___lam__0___closed__1: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Std_CancellationToken_wait___lam__0___closed__2_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_CancellationToken_wait___lam__0___closed__2: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Std_CancellationToken_wait___lam__0___closed__3_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_CancellationToken_wait___lam__0___closed__3: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Std_CancellationToken_wait___lam__0___closed__4_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_CancellationToken_wait___lam__0___closed__4: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Std_CancellationToken_wait___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_Std_CancellationToken_wait___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Std_CancellationToken_wait___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Std_CancellationToken_wait___closed__0_value) as *mut LeanObject;
pub static l_Std_CancellationToken_wait___closed__1_value: LeanClosureObject<1> =
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
        m_fun: l_Std_CancellationToken_wait___lam__1___boxed as *const core::ffi::c_void,
        m_arity: 3,
        m_num_fixed: 1,
        m_objs: [
            core::ptr::addr_of!(l_Std_CancellationToken_wait___closed__0_value) as *mut LeanObject,
        ],
    };
static mut l_Std_CancellationToken_wait___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Std_CancellationToken_wait___closed__1_value) as *mut LeanObject;
pub static l_Std_Async_Waiter_race___at___00Std_CancellationToken_selector_spec__0___closed__0_value: LeanClosureObject<1> = LeanClosureObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut LeanObject>()*1) as u16, other: 0, tag: 245 }, m_fun: l_Std_Async_Waiter_race___at___00Std_CancellationToken_selector_spec__0___lam__0___boxed as *const core::ffi::c_void, m_arity: 3, m_num_fixed: 1, m_objs: [((( 1 as usize) << 1) | 1) as *mut LeanObject] };
static mut l_Std_Async_Waiter_race___at___00Std_CancellationToken_selector_spec__0___closed__0:
    *mut LeanObject = core::ptr::addr_of!(
    l_Std_Async_Waiter_race___at___00Std_CancellationToken_selector_spec__0___closed__0_value
) as *mut LeanObject;
pub static l_Std_Mutex_atomically___at___00Std_CancellationToken_selector_spec__1___redArg___closed__0_value: LeanClosureObject<0> = LeanClosureObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Std_Mutex_atomically___at___00Std_CancellationToken_selector_spec__1___redArg___lam__3 as *const core::ffi::c_void, m_arity: 1, m_num_fixed: 0, m_objs: [] };
static mut l_Std_Mutex_atomically___at___00Std_CancellationToken_selector_spec__1___redArg___closed__0: *mut LeanObject = core::ptr::addr_of!(l_Std_Mutex_atomically___at___00Std_CancellationToken_selector_spec__1___redArg___closed__0_value) as *mut LeanObject;
pub static l_Std_CancellationToken_selector___lam__2___closed__0_value: LeanCtorObject<1> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*1 + 0) as u16, other: 1, tag: 0 }, m_objs: [core::ptr::addr_of!(l_Std_Async_Waiter_race___at___00Std_CancellationToken_Consumer_resolve_spec__0___closed__0_value) as *mut LeanObject] };
static mut l_Std_CancellationToken_selector___lam__2___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Std_CancellationToken_selector___lam__2___closed__0_value)
        as *mut LeanObject;
pub static l_Std_CancellationToken_selector___lam__2___closed__1_value: LeanClosureObject<1> =
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
        m_fun: l_Std_CancellationToken_selector___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 3,
        m_num_fixed: 1,
        m_objs: [(((0 as usize) << 1) | 1) as *mut LeanObject],
    };
static mut l_Std_CancellationToken_selector___lam__2___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Std_CancellationToken_selector___lam__2___closed__1_value)
        as *mut LeanObject;
pub static l_Std_CancellationToken_selector___lam__2___closed__2_value: LeanClosureObject<1> =
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
        m_fun: l_Std_CancellationToken_selector___lam__1 as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 1,
        m_objs: [(((0 as usize) << 1) | 1) as *mut LeanObject],
    };
static mut l_Std_CancellationToken_selector___lam__2___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Std_CancellationToken_selector___lam__2___closed__2_value)
        as *mut LeanObject;
pub static l_Std_CancellationToken_selector___lam__5___closed__0_value: LeanCtorObject<1> =
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
static mut l_Std_CancellationToken_selector___lam__5___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Std_CancellationToken_selector___lam__5___closed__0_value)
        as *mut LeanObject;
pub static l_Std_CancellationToken_selector___lam__5___closed__1_value: LeanCtorObject<1> =
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
            core::ptr::addr_of!(l_Std_CancellationToken_selector___lam__5___closed__0_value)
                as *mut LeanObject,
        ],
    };
static mut l_Std_CancellationToken_selector___lam__5___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Std_CancellationToken_selector___lam__5___closed__1_value)
        as *mut LeanObject;
pub static l_Std_CancellationToken_selector___lam__5___closed__2_value: LeanCtorObject<1> =
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
static mut l_Std_CancellationToken_selector___lam__5___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Std_CancellationToken_selector___lam__5___closed__2_value)
        as *mut LeanObject;
pub static l_Std_CancellationToken_selector___lam__5___closed__3_value: LeanCtorObject<1> =
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
            core::ptr::addr_of!(l_Std_CancellationToken_selector___lam__5___closed__2_value)
                as *mut LeanObject,
        ],
    };
static mut l_Std_CancellationToken_selector___lam__5___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Std_CancellationToken_selector___lam__5___closed__3_value)
        as *mut LeanObject;
pub static l_Std_CancellationToken_selector___lam__5___closed__4_value: LeanCtorObject<1> =
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
            core::ptr::addr_of!(l_Std_CancellationToken_selector___lam__5___closed__3_value)
                as *mut LeanObject,
        ],
    };
static mut l_Std_CancellationToken_selector___lam__5___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Std_CancellationToken_selector___lam__5___closed__4_value)
        as *mut LeanObject;
pub static l_List_filterAuxM___at___00Std_Queue_filterM___at___00Std_CancellationToken_selector_spec__2_spec__2___redArg___closed__0_value: LeanCtorObject<1> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*1 + 0) as u16, other: 1, tag: 1 }, m_objs: [((( 1 as usize) << 1) | 1) as *mut LeanObject] };
static mut l_List_filterAuxM___at___00Std_Queue_filterM___at___00Std_CancellationToken_selector_spec__2_spec__2___redArg___closed__0: *mut LeanObject = core::ptr::addr_of!(l_List_filterAuxM___at___00Std_Queue_filterM___at___00Std_CancellationToken_selector_spec__2_spec__2___redArg___closed__0_value) as *mut LeanObject;
pub static l_List_filterAuxM___at___00Std_Queue_filterM___at___00Std_CancellationToken_selector_spec__2_spec__2___redArg___closed__1_value: LeanCtorObject<1> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*1 + 0) as u16, other: 1, tag: 0 }, m_objs: [core::ptr::addr_of!(l_List_filterAuxM___at___00Std_Queue_filterM___at___00Std_CancellationToken_selector_spec__2_spec__2___redArg___closed__0_value) as *mut LeanObject] };
static mut l_List_filterAuxM___at___00Std_Queue_filterM___at___00Std_CancellationToken_selector_spec__2_spec__2___redArg___closed__1: *mut LeanObject = core::ptr::addr_of!(l_List_filterAuxM___at___00Std_Queue_filterM___at___00Std_CancellationToken_selector_spec__2_spec__2___redArg___closed__1_value) as *mut LeanObject;
pub static l_List_filterAuxM___at___00Std_Queue_filterM___at___00Std_CancellationToken_selector_spec__2_spec__2___redArg___closed__2_value: LeanClosureObject<0> = LeanClosureObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_List_filterAuxM___at___00Std_Queue_filterM___at___00Std_CancellationToken_selector_spec__2_spec__2___redArg___lam__1___boxed as *const core::ffi::c_void, m_arity: 2, m_num_fixed: 0, m_objs: [] };
static mut l_List_filterAuxM___at___00Std_Queue_filterM___at___00Std_CancellationToken_selector_spec__2_spec__2___redArg___closed__2: *mut LeanObject = core::ptr::addr_of!(l_List_filterAuxM___at___00Std_Queue_filterM___at___00Std_CancellationToken_selector_spec__2_spec__2___redArg___closed__2_value) as *mut LeanObject;
pub static l_Std_Queue_filterM___at___00Std_CancellationToken_selector_spec__2___closed__0_value:
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
    m_fun: l_Std_Queue_filterM___at___00Std_CancellationToken_selector_spec__2___lam__0___boxed
        as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_Queue_filterM___at___00Std_CancellationToken_selector_spec__2___closed__0:
    *mut LeanObject = core::ptr::addr_of!(
    l_Std_Queue_filterM___at___00Std_CancellationToken_selector_spec__2___closed__0_value
) as *mut LeanObject;
pub static l_Std_CancellationToken_selector___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_Std_CancellationToken_selector___lam__5___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Std_CancellationToken_selector___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Std_CancellationToken_selector___closed__0_value) as *mut LeanObject;
pub static l_Std_CancellationToken_selector___closed__1_value: LeanClosureObject<0> =
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
        m_fun: l_Std_CancellationToken_selector___lam__9___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Std_CancellationToken_selector___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Std_CancellationToken_selector___closed__1_value) as *mut LeanObject;
pub unsafe fn l_Std_CancellationReason_ctorIdx(mut v_x_1118_: *mut LeanObject) -> *mut LeanObject {
    match lean_obj_tag(v_x_1118_) {
        0 => {
            let mut v___x_1119_: *mut LeanObject = core::ptr::null_mut();
            v___x_1119_ = lean_unsigned_to_nat(0);
            return v___x_1119_;
        }
        1 => {
            let mut v___x_1120_: *mut LeanObject = core::ptr::null_mut();
            v___x_1120_ = lean_unsigned_to_nat(1);
            return v___x_1120_;
        }
        2 => {
            let mut v___x_1121_: *mut LeanObject = core::ptr::null_mut();
            v___x_1121_ = lean_unsigned_to_nat(2);
            return v___x_1121_;
        }
        _ => {
            let mut v___x_1122_: *mut LeanObject = core::ptr::null_mut();
            v___x_1122_ = lean_unsigned_to_nat(3);
            return v___x_1122_;
        }
    }
}
pub unsafe fn l_Std_CancellationReason_ctorIdx___boxed(
    mut v_x_1123_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1124_: *mut LeanObject = core::ptr::null_mut();
    v_res_1124_ = l_Std_CancellationReason_ctorIdx(v_x_1123_);
    lean_dec(v_x_1123_);
    return v_res_1124_;
}
pub unsafe fn l_Std_CancellationReason_ctorElim___redArg(
    mut v_t_1125_: *mut LeanObject,
    mut v_k_1126_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_t_1125_) == 3 {
        let mut v_msg_1127_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1128_: *mut LeanObject = core::ptr::null_mut();
        v_msg_1127_ = lean_ctor_get(v_t_1125_, 0);
        lean_inc_ref(v_msg_1127_);
        lean_dec_ref_known(v_t_1125_, 1);
        v___x_1128_ = lean_apply_1(v_k_1126_, v_msg_1127_);
        return v___x_1128_;
    } else {
        lean_dec(v_t_1125_);
        return v_k_1126_;
    }
}
pub unsafe fn l_Std_CancellationReason_ctorElim(
    mut v_motive_1129_: *mut LeanObject,
    mut v_ctorIdx_1130_: *mut LeanObject,
    mut v_t_1131_: *mut LeanObject,
    mut v_h_1132_: *mut LeanObject,
    mut v_k_1133_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1134_: *mut LeanObject = core::ptr::null_mut();
    v___x_1134_ = l_Std_CancellationReason_ctorElim___redArg(v_t_1131_, v_k_1133_);
    return v___x_1134_;
}
pub unsafe fn l_Std_CancellationReason_ctorElim___boxed(
    mut v_motive_1135_: *mut LeanObject,
    mut v_ctorIdx_1136_: *mut LeanObject,
    mut v_t_1137_: *mut LeanObject,
    mut v_h_1138_: *mut LeanObject,
    mut v_k_1139_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1140_: *mut LeanObject = core::ptr::null_mut();
    v_res_1140_ = l_Std_CancellationReason_ctorElim(
        v_motive_1135_,
        v_ctorIdx_1136_,
        v_t_1137_,
        v_h_1138_,
        v_k_1139_,
    );
    lean_dec(v_ctorIdx_1136_);
    return v_res_1140_;
}
pub unsafe fn l_Std_CancellationReason_deadline_elim___redArg(
    mut v_t_1141_: *mut LeanObject,
    mut v_deadline_1142_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1143_: *mut LeanObject = core::ptr::null_mut();
    v___x_1143_ = l_Std_CancellationReason_ctorElim___redArg(v_t_1141_, v_deadline_1142_);
    return v___x_1143_;
}
pub unsafe fn l_Std_CancellationReason_deadline_elim(
    mut v_motive_1144_: *mut LeanObject,
    mut v_t_1145_: *mut LeanObject,
    mut v_h_1146_: *mut LeanObject,
    mut v_deadline_1147_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1148_: *mut LeanObject = core::ptr::null_mut();
    v___x_1148_ = l_Std_CancellationReason_ctorElim___redArg(v_t_1145_, v_deadline_1147_);
    return v___x_1148_;
}
pub unsafe fn l_Std_CancellationReason_shutdown_elim___redArg(
    mut v_t_1149_: *mut LeanObject,
    mut v_shutdown_1150_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1151_: *mut LeanObject = core::ptr::null_mut();
    v___x_1151_ = l_Std_CancellationReason_ctorElim___redArg(v_t_1149_, v_shutdown_1150_);
    return v___x_1151_;
}
pub unsafe fn l_Std_CancellationReason_shutdown_elim(
    mut v_motive_1152_: *mut LeanObject,
    mut v_t_1153_: *mut LeanObject,
    mut v_h_1154_: *mut LeanObject,
    mut v_shutdown_1155_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1156_: *mut LeanObject = core::ptr::null_mut();
    v___x_1156_ = l_Std_CancellationReason_ctorElim___redArg(v_t_1153_, v_shutdown_1155_);
    return v___x_1156_;
}
pub unsafe fn l_Std_CancellationReason_cancel_elim___redArg(
    mut v_t_1157_: *mut LeanObject,
    mut v_cancel_1158_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1159_: *mut LeanObject = core::ptr::null_mut();
    v___x_1159_ = l_Std_CancellationReason_ctorElim___redArg(v_t_1157_, v_cancel_1158_);
    return v___x_1159_;
}
pub unsafe fn l_Std_CancellationReason_cancel_elim(
    mut v_motive_1160_: *mut LeanObject,
    mut v_t_1161_: *mut LeanObject,
    mut v_h_1162_: *mut LeanObject,
    mut v_cancel_1163_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1164_: *mut LeanObject = core::ptr::null_mut();
    v___x_1164_ = l_Std_CancellationReason_ctorElim___redArg(v_t_1161_, v_cancel_1163_);
    return v___x_1164_;
}
pub unsafe fn l_Std_CancellationReason_custom_elim___redArg(
    mut v_t_1165_: *mut LeanObject,
    mut v_custom_1166_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1167_: *mut LeanObject = core::ptr::null_mut();
    v___x_1167_ = l_Std_CancellationReason_ctorElim___redArg(v_t_1165_, v_custom_1166_);
    return v___x_1167_;
}
pub unsafe fn l_Std_CancellationReason_custom_elim(
    mut v_motive_1168_: *mut LeanObject,
    mut v_t_1169_: *mut LeanObject,
    mut v_h_1170_: *mut LeanObject,
    mut v_custom_1171_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1172_: *mut LeanObject = core::ptr::null_mut();
    v___x_1172_ = l_Std_CancellationReason_ctorElim___redArg(v_t_1169_, v_custom_1171_);
    return v___x_1172_;
}
pub unsafe fn _init_l_Std_instReprCancellationReason_repr___closed__6() -> *mut LeanObject {
    let mut v___x_1182_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1183_: *mut LeanObject = core::ptr::null_mut();
    v___x_1182_ = lean_unsigned_to_nat(2);
    v___x_1183_ = lean_nat_to_int(v___x_1182_);
    return v___x_1183_;
}
pub unsafe fn _init_l_Std_instReprCancellationReason_repr___closed__7() -> *mut LeanObject {
    let mut v___x_1184_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1185_: *mut LeanObject = core::ptr::null_mut();
    v___x_1184_ = lean_unsigned_to_nat(1);
    v___x_1185_ = lean_nat_to_int(v___x_1184_);
    return v___x_1185_;
}
pub unsafe fn l_Std_instReprCancellationReason_repr(
    mut v_x_1192_: *mut LeanObject,
    mut v_prec_1193_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___y_1195_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1196_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1197_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1198_: u8 = 0;
    let mut v___x_1199_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1200_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1202_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1203_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1204_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1205_: u8 = 0;
    let mut v___x_1206_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1207_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1209_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1210_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1211_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1212_: u8 = 0;
    let mut v___x_1213_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1214_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1215_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1216_: u8 = 0;
    let mut v___x_1217_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1218_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1219_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1220_: u8 = 0;
    let mut v___x_1221_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1222_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1223_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1224_: u8 = 0;
    let mut v___x_1225_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1226_: *mut LeanObject = core::ptr::null_mut();
    let mut v_msg_1227_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1229_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1230_: u8 = 0;
    let mut v___y_1232_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1233_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1234_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1236_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1237_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1238_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1239_: u8 = 0;
    let mut v___x_1240_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1241_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1242_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1243_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1244_: u8 = 0;
    let mut v___x_1245_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1246_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1247_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => match lean_obj_tag(v_x_1192_) {
                0 => {
                    v___x_1215_ = lean_unsigned_to_nat(1024);
                    v___x_1216_ = lean_nat_dec_le(v___x_1215_, v_prec_1193_);
                    if v___x_1216_ == 0 {
                        v___x_1217_ = lean_obj_once(
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
                        v___x_1218_ = lean_obj_once(
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
                    v___x_1219_ = lean_unsigned_to_nat(1024);
                    v___x_1220_ = lean_nat_dec_le(v___x_1219_, v_prec_1193_);
                    if v___x_1220_ == 0 {
                        v___x_1221_ = lean_obj_once(
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
                        v___x_1222_ = lean_obj_once(
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
                    v___x_1223_ = lean_unsigned_to_nat(1024);
                    v___x_1224_ = lean_nat_dec_le(v___x_1223_, v_prec_1193_);
                    if v___x_1224_ == 0 {
                        v___x_1225_ = lean_obj_once(
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
                        v___x_1226_ = lean_obj_once(
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
                    v_msg_1227_ = lean_ctor_get(v_x_1192_, 0);
                    v_isSharedCheck_1247_ = (!lean_is_exclusive(v_x_1192_)) as u8;
                    if v_isSharedCheck_1247_ == 0 {
                        v___x_1229_ = v_x_1192_;
                        v_isShared_1230_ = v_isSharedCheck_1247_;
                        state = 4;
                        continue;
                    } else {
                        lean_inc(v_msg_1227_);
                        lean_dec(v_x_1192_);
                        v___x_1229_ = lean_box(0);
                        v_isShared_1230_ = v_isSharedCheck_1247_;
                        state = 4;
                        continue;
                    }
                }
            },
            1 => {
                v___x_1196_ = l_Std_instReprCancellationReason_repr___closed__1;
                lean_inc(v___y_1195_);
                v___x_1197_ = lean_alloc_ctor(4, 2, (0) as u32);
                lean_ctor_set(v___x_1197_, 0, v___y_1195_);
                lean_ctor_set(v___x_1197_, 1, v___x_1196_);
                v___x_1198_ = 0;
                v___x_1199_ = lean_alloc_ctor(6, 1, (1) as u32);
                lean_ctor_set(v___x_1199_, 0, v___x_1197_);
                lean_ctor_set_uint8(
                    v___x_1199_,
                    (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                    v___x_1198_,
                );
                v___x_1200_ = l_Repr_addAppParen(v___x_1199_, v_prec_1193_);
                return v___x_1200_;
            }
            2 => {
                v___x_1203_ = l_Std_instReprCancellationReason_repr___closed__3;
                lean_inc(v___y_1202_);
                v___x_1204_ = lean_alloc_ctor(4, 2, (0) as u32);
                lean_ctor_set(v___x_1204_, 0, v___y_1202_);
                lean_ctor_set(v___x_1204_, 1, v___x_1203_);
                v___x_1205_ = 0;
                v___x_1206_ = lean_alloc_ctor(6, 1, (1) as u32);
                lean_ctor_set(v___x_1206_, 0, v___x_1204_);
                lean_ctor_set_uint8(
                    v___x_1206_,
                    (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                    v___x_1205_,
                );
                v___x_1207_ = l_Repr_addAppParen(v___x_1206_, v_prec_1193_);
                return v___x_1207_;
            }
            3 => {
                v___x_1210_ = l_Std_instReprCancellationReason_repr___closed__5;
                lean_inc(v___y_1209_);
                v___x_1211_ = lean_alloc_ctor(4, 2, (0) as u32);
                lean_ctor_set(v___x_1211_, 0, v___y_1209_);
                lean_ctor_set(v___x_1211_, 1, v___x_1210_);
                v___x_1212_ = 0;
                v___x_1213_ = lean_alloc_ctor(6, 1, (1) as u32);
                lean_ctor_set(v___x_1213_, 0, v___x_1211_);
                lean_ctor_set_uint8(
                    v___x_1213_,
                    (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                    v___x_1212_,
                );
                v___x_1214_ = l_Repr_addAppParen(v___x_1213_, v_prec_1193_);
                return v___x_1214_;
            }
            4 => {
                v___x_1243_ = lean_unsigned_to_nat(1024);
                v___x_1244_ = lean_nat_dec_le(v___x_1243_, v_prec_1193_);
                if v___x_1244_ == 0 {
                    v___x_1245_ = lean_obj_once(
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
                    v___x_1246_ = lean_obj_once(
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
                    lean_ctor_set(v___x_1229_, 0, v___x_1234_);
                    v___x_1236_ = v___x_1229_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_1242_ = lean_alloc_ctor(3, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1242_, 0, v___x_1234_);
                    v___x_1236_ = v_reuseFailAlloc_1242_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                v___x_1237_ = lean_alloc_ctor(5, 2, (0) as u32);
                lean_ctor_set(v___x_1237_, 0, v___x_1233_);
                lean_ctor_set(v___x_1237_, 1, v___x_1236_);
                lean_inc(v___y_1232_);
                v___x_1238_ = lean_alloc_ctor(4, 2, (0) as u32);
                lean_ctor_set(v___x_1238_, 0, v___y_1232_);
                lean_ctor_set(v___x_1238_, 1, v___x_1237_);
                v___x_1239_ = 0;
                v___x_1240_ = lean_alloc_ctor(6, 1, (1) as u32);
                lean_ctor_set(v___x_1240_, 0, v___x_1238_);
                lean_ctor_set_uint8(
                    v___x_1240_,
                    (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
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
    mut v_x_1248_: *mut LeanObject,
    mut v_prec_1249_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1250_: *mut LeanObject = core::ptr::null_mut();
    v_res_1250_ = l_Std_instReprCancellationReason_repr(v_x_1248_, v_prec_1249_);
    lean_dec(v_prec_1249_);
    return v_res_1250_;
}
pub unsafe fn l_Std_instBEqCancellationReason_beq(
    mut v_x_1253_: *mut LeanObject,
    mut v_x_1254_: *mut LeanObject,
) -> u8 {
    match lean_obj_tag(v_x_1253_) {
        0 => {
            if lean_obj_tag(v_x_1254_) == 0 {
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
            if lean_obj_tag(v_x_1254_) == 1 {
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
            if lean_obj_tag(v_x_1254_) == 2 {
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
            if lean_obj_tag(v_x_1254_) == 3 {
                let mut v_msg_1261_: *mut LeanObject = core::ptr::null_mut();
                let mut v_msg_1262_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_1263_: u8 = 0;
                v_msg_1261_ = lean_ctor_get(v_x_1253_, 0);
                v_msg_1262_ = lean_ctor_get(v_x_1254_, 0);
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
    mut v_x_1265_: *mut LeanObject,
    mut v_x_1266_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1267_: u8 = 0;
    let mut v_r_1268_: *mut LeanObject = core::ptr::null_mut();
    v_res_1267_ = l_Std_instBEqCancellationReason_beq(v_x_1265_, v_x_1266_);
    lean_dec(v_x_1266_);
    lean_dec(v_x_1265_);
    v_r_1268_ = lean_box((v_res_1267_) as usize);
    return v_r_1268_;
}
pub unsafe fn l_Std_instToStringCancellationReason___lam__0(
    mut v_x_1276_: *mut LeanObject,
) -> *mut LeanObject {
    match lean_obj_tag(v_x_1276_) {
        0 => {
            let mut v___x_1277_: *mut LeanObject = core::ptr::null_mut();
            v___x_1277_ = l_Std_instToStringCancellationReason___lam__0___closed__0;
            return v___x_1277_;
        }
        1 => {
            let mut v___x_1278_: *mut LeanObject = core::ptr::null_mut();
            v___x_1278_ = l_Std_instToStringCancellationReason___lam__0___closed__1;
            return v___x_1278_;
        }
        2 => {
            let mut v___x_1279_: *mut LeanObject = core::ptr::null_mut();
            v___x_1279_ = l_Std_instToStringCancellationReason___lam__0___closed__2;
            return v___x_1279_;
        }
        _ => {
            let mut v_msg_1280_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_1281_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_1282_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_1283_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_1284_: *mut LeanObject = core::ptr::null_mut();
            v_msg_1280_ = lean_ctor_get(v_x_1276_, 0);
            v___x_1281_ = l_Std_instToStringCancellationReason___lam__0___closed__3;
            v___x_1282_ = lean_string_append(v___x_1281_, v_msg_1280_);
            v___x_1283_ = l_Std_instToStringCancellationReason___lam__0___closed__4;
            v___x_1284_ = lean_string_append(v___x_1282_, v___x_1283_);
            return v___x_1284_;
        }
    }
}
pub unsafe fn l_Std_instToStringCancellationReason___lam__0___boxed(
    mut v_x_1285_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1286_: *mut LeanObject = core::ptr::null_mut();
    v_res_1286_ = l_Std_instToStringCancellationReason___lam__0(v_x_1285_);
    lean_dec(v_x_1285_);
    return v_res_1286_;
}
pub unsafe fn l_Std_CancellationToken_Consumer_ctorIdx(
    mut v_x_1289_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_1289_) == 0 {
        let mut v___x_1290_: *mut LeanObject = core::ptr::null_mut();
        v___x_1290_ = lean_unsigned_to_nat(0);
        return v___x_1290_;
    } else {
        let mut v___x_1291_: *mut LeanObject = core::ptr::null_mut();
        v___x_1291_ = lean_unsigned_to_nat(1);
        return v___x_1291_;
    }
}
pub unsafe fn l_Std_CancellationToken_Consumer_ctorIdx___boxed(
    mut v_x_1292_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1293_: *mut LeanObject = core::ptr::null_mut();
    v_res_1293_ = l_Std_CancellationToken_Consumer_ctorIdx(v_x_1292_);
    lean_dec_ref(v_x_1292_);
    return v_res_1293_;
}
pub unsafe fn l_Std_CancellationToken_Consumer_ctorElim___redArg(
    mut v_t_1294_: *mut LeanObject,
    mut v_k_1295_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_t_1294_) == 0 {
        let mut v_promise_1296_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1297_: *mut LeanObject = core::ptr::null_mut();
        v_promise_1296_ = lean_ctor_get(v_t_1294_, 0);
        lean_inc(v_promise_1296_);
        lean_dec_ref_known(v_t_1294_, 1);
        v___x_1297_ = lean_apply_1(v_k_1295_, v_promise_1296_);
        return v___x_1297_;
    } else {
        let mut v_finished_1298_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1299_: *mut LeanObject = core::ptr::null_mut();
        v_finished_1298_ = lean_ctor_get(v_t_1294_, 0);
        lean_inc_ref(v_finished_1298_);
        lean_dec_ref_known(v_t_1294_, 1);
        v___x_1299_ = lean_apply_1(v_k_1295_, v_finished_1298_);
        return v___x_1299_;
    }
}
pub unsafe fn l_Std_CancellationToken_Consumer_ctorElim(
    mut v_motive_1300_: *mut LeanObject,
    mut v_ctorIdx_1301_: *mut LeanObject,
    mut v_t_1302_: *mut LeanObject,
    mut v_h_1303_: *mut LeanObject,
    mut v_k_1304_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1305_: *mut LeanObject = core::ptr::null_mut();
    v___x_1305_ = l_Std_CancellationToken_Consumer_ctorElim___redArg(v_t_1302_, v_k_1304_);
    return v___x_1305_;
}
pub unsafe fn l_Std_CancellationToken_Consumer_ctorElim___boxed(
    mut v_motive_1306_: *mut LeanObject,
    mut v_ctorIdx_1307_: *mut LeanObject,
    mut v_t_1308_: *mut LeanObject,
    mut v_h_1309_: *mut LeanObject,
    mut v_k_1310_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1311_: *mut LeanObject = core::ptr::null_mut();
    v_res_1311_ = l_Std_CancellationToken_Consumer_ctorElim(
        v_motive_1306_,
        v_ctorIdx_1307_,
        v_t_1308_,
        v_h_1309_,
        v_k_1310_,
    );
    lean_dec(v_ctorIdx_1307_);
    return v_res_1311_;
}
pub unsafe fn l_Std_CancellationToken_Consumer_normal_elim___redArg(
    mut v_t_1312_: *mut LeanObject,
    mut v_normal_1313_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1314_: *mut LeanObject = core::ptr::null_mut();
    v___x_1314_ = l_Std_CancellationToken_Consumer_ctorElim___redArg(v_t_1312_, v_normal_1313_);
    return v___x_1314_;
}
pub unsafe fn l_Std_CancellationToken_Consumer_normal_elim(
    mut v_motive_1315_: *mut LeanObject,
    mut v_t_1316_: *mut LeanObject,
    mut v_h_1317_: *mut LeanObject,
    mut v_normal_1318_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1319_: *mut LeanObject = core::ptr::null_mut();
    v___x_1319_ = l_Std_CancellationToken_Consumer_ctorElim___redArg(v_t_1316_, v_normal_1318_);
    return v___x_1319_;
}
pub unsafe fn l_Std_CancellationToken_Consumer_select_elim___redArg(
    mut v_t_1320_: *mut LeanObject,
    mut v_select_1321_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1322_: *mut LeanObject = core::ptr::null_mut();
    v___x_1322_ = l_Std_CancellationToken_Consumer_ctorElim___redArg(v_t_1320_, v_select_1321_);
    return v___x_1322_;
}
pub unsafe fn l_Std_CancellationToken_Consumer_select_elim(
    mut v_motive_1323_: *mut LeanObject,
    mut v_t_1324_: *mut LeanObject,
    mut v_h_1325_: *mut LeanObject,
    mut v_select_1326_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1327_: *mut LeanObject = core::ptr::null_mut();
    v___x_1327_ = l_Std_CancellationToken_Consumer_ctorElim___redArg(v_t_1324_, v_select_1326_);
    return v___x_1327_;
}
pub unsafe fn l_Std_Async_Waiter_race___at___00Std_CancellationToken_Consumer_resolve_spec__0(
    mut v_w_1330_: *mut LeanObject,
    mut v_lose_1331_: *mut LeanObject,
) -> u8 {
    let mut v_finished_1333_: *mut LeanObject = core::ptr::null_mut();
    let mut v_promise_1334_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1335_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1337_: u8 = 0;
    let mut v___x_1338_: u8 = 0;
    let mut v___x_1339_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1340_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1341_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1342_: u8 = 0;
    let mut v___x_1343_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1344_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1345_: u8 = 0;
    let mut v___x_1346_: u8 = 0;
    let mut v___x_1347_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_finished_1333_ = lean_ctor_get(v_w_1330_, 0);
                v_promise_1334_ = lean_ctor_get(v_w_1330_, 1);
                v___x_1335_ = lean_st_ref_take(v_finished_1333_);
                v___x_1345_ = (lean_unbox(v___x_1335_) as u8);
                lean_dec(v___x_1335_);
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
                v___x_1339_ = lean_box((v___x_1338_) as usize);
                v___x_1340_ = lean_st_ref_set(v_finished_1333_, v___x_1339_);
                if v___y_1337_ == 0 {
                    v___x_1341_ = lean_apply_1(v_lose_1331_, lean_box(0));
                    v___x_1342_ = (lean_unbox(v___x_1341_) as u8);
                    return v___x_1342_;
                } else {
                    lean_dec_ref(v_lose_1331_);
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
    mut v_w_1348_: *mut LeanObject,
    mut v_lose_1349_: *mut LeanObject,
    mut v___y_1350_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1351_: u8 = 0;
    let mut v_r_1352_: *mut LeanObject = core::ptr::null_mut();
    v_res_1351_ = l_Std_Async_Waiter_race___at___00Std_CancellationToken_Consumer_resolve_spec__0(
        v_w_1348_,
        v_lose_1349_,
    );
    lean_dec_ref(v_w_1348_);
    v_r_1352_ = lean_box((v_res_1351_) as usize);
    return v_r_1352_;
}
pub unsafe fn l_Std_CancellationToken_Consumer_resolve___lam__0(mut v___x_1353_: u8) -> u8 {
    return v___x_1353_;
}
pub unsafe fn l_Std_CancellationToken_Consumer_resolve___lam__0___boxed(
    mut v___x_1355_: *mut LeanObject,
    mut v___y_1356_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_408__boxed_1357_: u8 = 0;
    let mut v_res_1358_: u8 = 0;
    let mut v_r_1359_: *mut LeanObject = core::ptr::null_mut();
    v___x_408__boxed_1357_ = (lean_unbox(v___x_1355_) as u8);
    v_res_1358_ = l_Std_CancellationToken_Consumer_resolve___lam__0(v___x_408__boxed_1357_);
    v_r_1359_ = lean_box((v_res_1358_) as usize);
    return v_r_1359_;
}
pub unsafe fn l_Std_CancellationToken_Consumer_resolve(mut v_c_1363_: *mut LeanObject) -> u8 {
    if lean_obj_tag(v_c_1363_) == 0 {
        let mut v_promise_1365_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1366_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1367_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1368_: u8 = 0;
        v_promise_1365_ = lean_ctor_get(v_c_1363_, 0);
        v___x_1366_ = lean_box(0);
        v___x_1367_ = lean_io_promise_resolve(v___x_1366_, v_promise_1365_);
        v___x_1368_ = 1;
        return v___x_1368_;
    } else {
        let mut v_finished_1369_: *mut LeanObject = core::ptr::null_mut();
        let mut v_lose_1370_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1371_: u8 = 0;
        v_finished_1369_ = lean_ctor_get(v_c_1363_, 0);
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
    mut v_c_1372_: *mut LeanObject,
    mut v_a_1373_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1374_: u8 = 0;
    let mut v_r_1375_: *mut LeanObject = core::ptr::null_mut();
    v_res_1374_ = l_Std_CancellationToken_Consumer_resolve(v_c_1372_);
    lean_dec_ref(v_c_1372_);
    v_r_1375_ = lean_box((v_res_1374_) as usize);
    return v_r_1375_;
}
pub unsafe fn _init_l_Std_CancellationToken_new___closed__0() -> *mut LeanObject {
    let mut v___x_1376_: *mut LeanObject = core::ptr::null_mut();
    v___x_1376_ = l_Std_Queue_empty(lean_box(0));
    return v___x_1376_;
}
pub unsafe fn _init_l_Std_CancellationToken_new___closed__1() -> *mut LeanObject {
    let mut v___x_1377_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1378_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1379_: *mut LeanObject = core::ptr::null_mut();
    v___x_1377_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_CancellationToken_new___closed__0),
        core::ptr::addr_of_mut!(l_Std_CancellationToken_new___closed__0_once),
        _init_l_Std_CancellationToken_new___closed__0,
    );
    v___x_1378_ = lean_box(0);
    v___x_1379_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_1379_, 0, v___x_1378_);
    lean_ctor_set(v___x_1379_, 1, v___x_1377_);
    return v___x_1379_;
}
pub unsafe fn l_Std_CancellationToken_new() -> *mut LeanObject {
    let mut v___x_1381_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1382_: *mut LeanObject = core::ptr::null_mut();
    v___x_1381_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_CancellationToken_new___closed__1),
        core::ptr::addr_of_mut!(l_Std_CancellationToken_new___closed__1_once),
        _init_l_Std_CancellationToken_new___closed__1,
    );
    v___x_1382_ = l_Std_Mutex_new___redArg(v___x_1381_);
    return v___x_1382_;
}
pub unsafe fn l_Std_CancellationToken_new___boxed(
    mut v_a_1383_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1384_: *mut LeanObject = core::ptr::null_mut();
    v_res_1384_ = l_Std_CancellationToken_new();
    return v_res_1384_;
}
pub unsafe fn l_Std_Mutex_atomically___at___00Std_CancellationToken_cancel_spec__1___redArg(
    mut v_mutex_1385_: *mut LeanObject,
    mut v_k_1386_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_ref_1388_: *mut LeanObject = core::ptr::null_mut();
    let mut v_mutex_1389_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1390_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1391_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1392_: *mut LeanObject = core::ptr::null_mut();
    v_ref_1388_ = lean_ctor_get(v_mutex_1385_, 0);
    lean_inc(v_ref_1388_);
    v_mutex_1389_ = lean_ctor_get(v_mutex_1385_, 1);
    lean_inc(v_mutex_1389_);
    lean_dec_ref(v_mutex_1385_);
    v___x_1390_ = lean_io_basemutex_lock(v_mutex_1389_);
    v___x_1391_ = lean_apply_2(v_k_1386_, v_ref_1388_, lean_box(0));
    v___x_1392_ = lean_io_basemutex_unlock(v_mutex_1389_);
    lean_dec(v_mutex_1389_);
    return v___x_1391_;
}
pub unsafe fn l_Std_Mutex_atomically___at___00Std_CancellationToken_cancel_spec__1___redArg___boxed(
    mut v_mutex_1393_: *mut LeanObject,
    mut v_k_1394_: *mut LeanObject,
    mut v___y_1395_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1396_: *mut LeanObject = core::ptr::null_mut();
    v_res_1396_ = l_Std_Mutex_atomically___at___00Std_CancellationToken_cancel_spec__1___redArg(
        v_mutex_1393_,
        v_k_1394_,
    );
    return v_res_1396_;
}
pub unsafe fn l_Std_Mutex_atomically___at___00Std_CancellationToken_cancel_spec__1(
    mut v_00_u03b1_1397_: *mut LeanObject,
    mut v_00_u03b2_1398_: *mut LeanObject,
    mut v_mutex_1399_: *mut LeanObject,
    mut v_k_1400_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1402_: *mut LeanObject = core::ptr::null_mut();
    v___x_1402_ = l_Std_Mutex_atomically___at___00Std_CancellationToken_cancel_spec__1___redArg(
        v_mutex_1399_,
        v_k_1400_,
    );
    return v___x_1402_;
}
pub unsafe fn l_Std_Mutex_atomically___at___00Std_CancellationToken_cancel_spec__1___boxed(
    mut v_00_u03b1_1403_: *mut LeanObject,
    mut v_00_u03b2_1404_: *mut LeanObject,
    mut v_mutex_1405_: *mut LeanObject,
    mut v_k_1406_: *mut LeanObject,
    mut v___y_1407_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1408_: *mut LeanObject = core::ptr::null_mut();
    v_res_1408_ = l_Std_Mutex_atomically___at___00Std_CancellationToken_cancel_spec__1(
        v_00_u03b1_1403_,
        v_00_u03b2_1404_,
        v_mutex_1405_,
        v_k_1406_,
    );
    return v_res_1408_;
}
pub unsafe fn l___private_Init_While_0__whileM_erased___at___00Std_CancellationToken_cancel_spec__0___redArg(
    mut v_a_1409_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1411_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_1412_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_1413_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_1414_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1415_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                lean_inc_ref(v_a_1409_);
                v___x_1411_ = l_Std_Queue_dequeue_x3f___redArg(v_a_1409_);
                if lean_obj_tag(v___x_1411_) == 1 {
                    lean_dec_ref(v_a_1409_);
                    v_val_1412_ = lean_ctor_get(v___x_1411_, 0);
                    lean_inc(v_val_1412_);
                    lean_dec_ref_known(v___x_1411_, 1);
                    v_fst_1413_ = lean_ctor_get(v_val_1412_, 0);
                    lean_inc(v_fst_1413_);
                    v_snd_1414_ = lean_ctor_get(v_val_1412_, 1);
                    lean_inc(v_snd_1414_);
                    lean_dec(v_val_1412_);
                    v___x_1415_ = l_Std_CancellationToken_Consumer_resolve(v_fst_1413_);
                    lean_dec(v_fst_1413_);
                    v_a_1409_ = v_snd_1414_;
                    state = 0;
                    continue;
                } else {
                    lean_dec(v___x_1411_);
                    return v_a_1409_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_While_0__whileM_erased___at___00Std_CancellationToken_cancel_spec__0___redArg___boxed(
    mut v_a_1417_: *mut LeanObject,
    mut v___y_1418_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1419_: *mut LeanObject = core::ptr::null_mut();
    v_res_1419_ = l___private_Init_While_0__whileM_erased___at___00Std_CancellationToken_cancel_spec__0___redArg(v_a_1417_);
    return v_res_1419_;
}
pub unsafe fn l_Std_CancellationToken_cancel___lam__0(
    mut v_reason_1420_: *mut LeanObject,
    mut v___y_1421_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1423_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reason_1424_: *mut LeanObject = core::ptr::null_mut();
    let mut v_consumers_1425_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1427_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1428_: u8 = 0;
    let mut v___x_1429_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1430_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1431_: *mut LeanObject = core::ptr::null_mut();
    let mut v_st_1433_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1434_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1435_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1436_: u8 = 0;
    let mut v_unused_1437_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1438_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1423_ = lean_st_ref_get(v___y_1421_);
                v_reason_1424_ = lean_ctor_get(v___x_1423_, 0);
                lean_inc(v_reason_1424_);
                if lean_obj_tag(v_reason_1424_) == 0 {
                    v_consumers_1425_ = lean_ctor_get(v___x_1423_, 1);
                    v_isSharedCheck_1436_ = (!lean_is_exclusive(v___x_1423_)) as u8;
                    if v_isSharedCheck_1436_ == 0 {
                        v_unused_1437_ = lean_ctor_get(v___x_1423_, 0);
                        lean_dec(v_unused_1437_);
                        v___x_1427_ = v___x_1423_;
                        v_isShared_1428_ = v_isSharedCheck_1436_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_consumers_1425_);
                        lean_dec(v___x_1423_);
                        v___x_1427_ = lean_box(0);
                        v_isShared_1428_ = v_isSharedCheck_1436_;
                        state = 1;
                        continue;
                    }
                } else {
                    lean_dec_ref_known(v_reason_1424_, 1);
                    lean_dec(v___x_1423_);
                    lean_dec(v_reason_1420_);
                    v___x_1438_ = lean_box(0);
                    return v___x_1438_;
                }
            }
            1 => {
                v___x_1429_ = l___private_Init_While_0__whileM_erased___at___00Std_CancellationToken_cancel_spec__0___redArg(v_consumers_1425_);
                lean_dec_ref(v___x_1429_);
                v___x_1430_ = lean_alloc_ctor(1, 1, (0) as u32);
                lean_ctor_set(v___x_1430_, 0, v_reason_1420_);
                v___x_1431_ = lean_obj_once(
                    core::ptr::addr_of_mut!(l_Std_CancellationToken_new___closed__0),
                    core::ptr::addr_of_mut!(l_Std_CancellationToken_new___closed__0_once),
                    _init_l_Std_CancellationToken_new___closed__0,
                );
                if v_isShared_1428_ == 0 {
                    lean_ctor_set(v___x_1427_, 1, v___x_1431_);
                    lean_ctor_set(v___x_1427_, 0, v___x_1430_);
                    v_st_1433_ = v___x_1427_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1435_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1435_, 0, v___x_1430_);
                    lean_ctor_set(v_reuseFailAlloc_1435_, 1, v___x_1431_);
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
    mut v_reason_1439_: *mut LeanObject,
    mut v___y_1440_: *mut LeanObject,
    mut v___y_1441_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1442_: *mut LeanObject = core::ptr::null_mut();
    v_res_1442_ = l_Std_CancellationToken_cancel___lam__0(v_reason_1439_, v___y_1440_);
    lean_dec(v___y_1440_);
    return v_res_1442_;
}
pub unsafe fn l_Std_CancellationToken_cancel(
    mut v_x_1443_: *mut LeanObject,
    mut v_reason_1444_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_1446_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1447_: *mut LeanObject = core::ptr::null_mut();
    v___f_1446_ = lean_alloc_closure(
        l_Std_CancellationToken_cancel___lam__0___boxed as *mut core::ffi::c_void,
        3,
        1,
    );
    lean_closure_set(v___f_1446_, 0, v_reason_1444_);
    v___x_1447_ = l_Std_Mutex_atomically___at___00Std_CancellationToken_cancel_spec__1___redArg(
        v_x_1443_,
        v___f_1446_,
    );
    return v___x_1447_;
}
pub unsafe fn l_Std_CancellationToken_cancel___boxed(
    mut v_x_1448_: *mut LeanObject,
    mut v_reason_1449_: *mut LeanObject,
    mut v_a_1450_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1451_: *mut LeanObject = core::ptr::null_mut();
    v_res_1451_ = l_Std_CancellationToken_cancel(v_x_1448_, v_reason_1449_);
    return v_res_1451_;
}
pub unsafe fn l___private_Init_While_0__whileM_erased___at___00Std_CancellationToken_cancel_spec__0(
    mut v_inst_1452_: *mut LeanObject,
    mut v_a_1453_: *mut LeanObject,
    mut v___y_1454_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1456_: *mut LeanObject = core::ptr::null_mut();
    v___x_1456_ = l___private_Init_While_0__whileM_erased___at___00Std_CancellationToken_cancel_spec__0___redArg(v_a_1453_);
    return v___x_1456_;
}
pub unsafe fn l___private_Init_While_0__whileM_erased___at___00Std_CancellationToken_cancel_spec__0___boxed(
    mut v_inst_1457_: *mut LeanObject,
    mut v_a_1458_: *mut LeanObject,
    mut v___y_1459_: *mut LeanObject,
    mut v___y_1460_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1461_: *mut LeanObject = core::ptr::null_mut();
    v_res_1461_ =
        l___private_Init_While_0__whileM_erased___at___00Std_CancellationToken_cancel_spec__0(
            v_inst_1457_,
            v_a_1458_,
            v___y_1459_,
        );
    lean_dec(v___y_1459_);
    return v_res_1461_;
}
pub unsafe fn l_Std_CancellationToken_isCancelled___lam__0(mut v___y_1462_: *mut LeanObject) -> u8 {
    let mut v___x_1464_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reason_1465_: *mut LeanObject = core::ptr::null_mut();
    v___x_1464_ = lean_st_ref_get(v___y_1462_);
    v_reason_1465_ = lean_ctor_get(v___x_1464_, 0);
    lean_inc(v_reason_1465_);
    lean_dec(v___x_1464_);
    if lean_obj_tag(v_reason_1465_) == 0 {
        let mut v___x_1466_: u8 = 0;
        v___x_1466_ = 0;
        return v___x_1466_;
    } else {
        let mut v___x_1467_: u8 = 0;
        lean_dec_ref_known(v_reason_1465_, 1);
        v___x_1467_ = 1;
        return v___x_1467_;
    }
}
pub unsafe fn l_Std_CancellationToken_isCancelled___lam__0___boxed(
    mut v___y_1468_: *mut LeanObject,
    mut v___y_1469_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1470_: u8 = 0;
    let mut v_r_1471_: *mut LeanObject = core::ptr::null_mut();
    v_res_1470_ = l_Std_CancellationToken_isCancelled___lam__0(v___y_1468_);
    lean_dec(v___y_1468_);
    v_r_1471_ = lean_box((v_res_1470_) as usize);
    return v_r_1471_;
}
pub unsafe fn l_Std_CancellationToken_isCancelled(mut v_x_1473_: *mut LeanObject) -> u8 {
    let mut v___f_1475_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1476_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1477_: u8 = 0;
    v___f_1475_ = l_Std_CancellationToken_isCancelled___closed__0;
    v___x_1476_ = l_Std_Mutex_atomically___at___00Std_CancellationToken_cancel_spec__1___redArg(
        v_x_1473_,
        v___f_1475_,
    );
    v___x_1477_ = (lean_unbox(v___x_1476_) as u8);
    lean_dec(v___x_1476_);
    return v___x_1477_;
}
pub unsafe fn l_Std_CancellationToken_isCancelled___boxed(
    mut v_x_1478_: *mut LeanObject,
    mut v_a_1479_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1480_: u8 = 0;
    let mut v_r_1481_: *mut LeanObject = core::ptr::null_mut();
    v_res_1480_ = l_Std_CancellationToken_isCancelled(v_x_1478_);
    v_r_1481_ = lean_box((v_res_1480_) as usize);
    return v_r_1481_;
}
pub unsafe fn l_Std_CancellationToken_getCancellationReason___lam__0(
    mut v___y_1482_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1484_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reason_1485_: *mut LeanObject = core::ptr::null_mut();
    v___x_1484_ = lean_st_ref_get(v___y_1482_);
    v_reason_1485_ = lean_ctor_get(v___x_1484_, 0);
    lean_inc(v_reason_1485_);
    lean_dec(v___x_1484_);
    return v_reason_1485_;
}
pub unsafe fn l_Std_CancellationToken_getCancellationReason___lam__0___boxed(
    mut v___y_1486_: *mut LeanObject,
    mut v___y_1487_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1488_: *mut LeanObject = core::ptr::null_mut();
    v_res_1488_ = l_Std_CancellationToken_getCancellationReason___lam__0(v___y_1486_);
    lean_dec(v___y_1486_);
    return v_res_1488_;
}
pub unsafe fn l_Std_CancellationToken_getCancellationReason(
    mut v_x_1490_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_1492_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1493_: *mut LeanObject = core::ptr::null_mut();
    v___f_1492_ = l_Std_CancellationToken_getCancellationReason___closed__0;
    v___x_1493_ = l_Std_Mutex_atomically___at___00Std_CancellationToken_cancel_spec__1___redArg(
        v_x_1490_,
        v___f_1492_,
    );
    return v___x_1493_;
}
pub unsafe fn l_Std_CancellationToken_getCancellationReason___boxed(
    mut v_x_1494_: *mut LeanObject,
    mut v_a_1495_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1496_: *mut LeanObject = core::ptr::null_mut();
    v_res_1496_ = l_Std_CancellationToken_getCancellationReason(v_x_1494_);
    return v_res_1496_;
}
pub unsafe fn l_Std_Mutex_atomically___at___00Std_CancellationToken_wait_spec__0___redArg(
    mut v_mutex_1497_: *mut LeanObject,
    mut v_k_1498_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_ref_1500_: *mut LeanObject = core::ptr::null_mut();
    let mut v_mutex_1501_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1502_: *mut LeanObject = core::ptr::null_mut();
    let mut v_r_1503_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1504_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1506_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1507_: u8 = 0;
    let mut v___x_1508_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1510_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1511_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1512_: u8 = 0;
    let mut v_a_1513_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1515_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1516_: u8 = 0;
    let mut v___x_1517_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1519_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1520_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1521_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ref_1500_ = lean_ctor_get(v_mutex_1497_, 0);
                lean_inc(v_ref_1500_);
                v_mutex_1501_ = lean_ctor_get(v_mutex_1497_, 1);
                lean_inc(v_mutex_1501_);
                lean_dec_ref(v_mutex_1497_);
                v___x_1502_ = lean_io_basemutex_lock(v_mutex_1501_);
                v_r_1503_ = lean_apply_2(v_k_1498_, v_ref_1500_, lean_box(0));
                if lean_obj_tag(v_r_1503_) == 0 {
                    v_a_1504_ = lean_ctor_get(v_r_1503_, 0);
                    v_isSharedCheck_1512_ = (!lean_is_exclusive(v_r_1503_)) as u8;
                    if v_isSharedCheck_1512_ == 0 {
                        v___x_1506_ = v_r_1503_;
                        v_isShared_1507_ = v_isSharedCheck_1512_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_1504_);
                        lean_dec(v_r_1503_);
                        v___x_1506_ = lean_box(0);
                        v_isShared_1507_ = v_isSharedCheck_1512_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_1513_ = lean_ctor_get(v_r_1503_, 0);
                    v_isSharedCheck_1521_ = (!lean_is_exclusive(v_r_1503_)) as u8;
                    if v_isSharedCheck_1521_ == 0 {
                        v___x_1515_ = v_r_1503_;
                        v_isShared_1516_ = v_isSharedCheck_1521_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_1513_);
                        lean_dec(v_r_1503_);
                        v___x_1515_ = lean_box(0);
                        v_isShared_1516_ = v_isSharedCheck_1521_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v___x_1508_ = lean_io_basemutex_unlock(v_mutex_1501_);
                lean_dec(v_mutex_1501_);
                if v_isShared_1507_ == 0 {
                    v___x_1510_ = v___x_1506_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1511_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1511_, 0, v_a_1504_);
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
                lean_dec(v_mutex_1501_);
                if v_isShared_1516_ == 0 {
                    v___x_1519_ = v___x_1515_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1520_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1520_, 0, v_a_1513_);
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
    mut v_mutex_1522_: *mut LeanObject,
    mut v_k_1523_: *mut LeanObject,
    mut v___y_1524_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1525_: *mut LeanObject = core::ptr::null_mut();
    v_res_1525_ = l_Std_Mutex_atomically___at___00Std_CancellationToken_wait_spec__0___redArg(
        v_mutex_1522_,
        v_k_1523_,
    );
    return v_res_1525_;
}
pub unsafe fn l_Std_Mutex_atomically___at___00Std_CancellationToken_wait_spec__0(
    mut v_00_u03b1_1526_: *mut LeanObject,
    mut v_00_u03b2_1527_: *mut LeanObject,
    mut v_mutex_1528_: *mut LeanObject,
    mut v_k_1529_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1531_: *mut LeanObject = core::ptr::null_mut();
    v___x_1531_ = l_Std_Mutex_atomically___at___00Std_CancellationToken_wait_spec__0___redArg(
        v_mutex_1528_,
        v_k_1529_,
    );
    return v___x_1531_;
}
pub unsafe fn l_Std_Mutex_atomically___at___00Std_CancellationToken_wait_spec__0___boxed(
    mut v_00_u03b1_1532_: *mut LeanObject,
    mut v_00_u03b2_1533_: *mut LeanObject,
    mut v_mutex_1534_: *mut LeanObject,
    mut v_k_1535_: *mut LeanObject,
    mut v___y_1536_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1537_: *mut LeanObject = core::ptr::null_mut();
    v_res_1537_ = l_Std_Mutex_atomically___at___00Std_CancellationToken_wait_spec__0(
        v_00_u03b1_1532_,
        v_00_u03b2_1533_,
        v_mutex_1534_,
        v_k_1535_,
    );
    return v_res_1537_;
}
pub unsafe fn _init_l_Std_CancellationToken_wait___lam__0___closed__1() -> *mut LeanObject {
    let mut v___x_1539_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1540_: *mut LeanObject = core::ptr::null_mut();
    v___x_1539_ = l_Std_CancellationToken_wait___lam__0___closed__0;
    v___x_1540_ = lean_mk_io_user_error(v___x_1539_);
    return v___x_1540_;
}
pub unsafe fn _init_l_Std_CancellationToken_wait___lam__0___closed__2() -> *mut LeanObject {
    let mut v___x_1541_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1542_: *mut LeanObject = core::ptr::null_mut();
    v___x_1541_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_CancellationToken_wait___lam__0___closed__1),
        core::ptr::addr_of_mut!(l_Std_CancellationToken_wait___lam__0___closed__1_once),
        _init_l_Std_CancellationToken_wait___lam__0___closed__1,
    );
    v___x_1542_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_1542_, 0, v___x_1541_);
    return v___x_1542_;
}
pub unsafe fn _init_l_Std_CancellationToken_wait___lam__0___closed__3() -> *mut LeanObject {
    let mut v___x_1543_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1544_: *mut LeanObject = core::ptr::null_mut();
    v___x_1543_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_CancellationToken_wait___lam__0___closed__2),
        core::ptr::addr_of_mut!(l_Std_CancellationToken_wait___lam__0___closed__2_once),
        _init_l_Std_CancellationToken_wait___lam__0___closed__2,
    );
    v___x_1544_ = lean_task_pure(v___x_1543_);
    return v___x_1544_;
}
pub unsafe fn _init_l_Std_CancellationToken_wait___lam__0___closed__4() -> *mut LeanObject {
    let mut v___x_1545_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1546_: *mut LeanObject = core::ptr::null_mut();
    v___x_1545_ =
        l_Std_Async_Waiter_race___at___00Std_CancellationToken_Consumer_resolve_spec__0___closed__0;
    v___x_1546_ = lean_task_pure(v___x_1545_);
    return v___x_1546_;
}
pub unsafe fn l_Std_CancellationToken_wait___lam__0(
    mut v_a_1547_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_a_1547_) == 0 {
        let mut v___x_1549_: *mut LeanObject = core::ptr::null_mut();
        v___x_1549_ = lean_obj_once(
            core::ptr::addr_of_mut!(l_Std_CancellationToken_wait___lam__0___closed__3),
            core::ptr::addr_of_mut!(l_Std_CancellationToken_wait___lam__0___closed__3_once),
            _init_l_Std_CancellationToken_wait___lam__0___closed__3,
        );
        return v___x_1549_;
    } else {
        let mut v___x_1550_: *mut LeanObject = core::ptr::null_mut();
        v___x_1550_ = lean_obj_once(
            core::ptr::addr_of_mut!(l_Std_CancellationToken_wait___lam__0___closed__4),
            core::ptr::addr_of_mut!(l_Std_CancellationToken_wait___lam__0___closed__4_once),
            _init_l_Std_CancellationToken_wait___lam__0___closed__4,
        );
        return v___x_1550_;
    }
}
pub unsafe fn l_Std_CancellationToken_wait___lam__0___boxed(
    mut v_a_1551_: *mut LeanObject,
    mut v___y_1552_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1553_: *mut LeanObject = core::ptr::null_mut();
    v_res_1553_ = l_Std_CancellationToken_wait___lam__0(v_a_1551_);
    lean_dec(v_a_1551_);
    return v_res_1553_;
}
pub unsafe fn l_Std_CancellationToken_wait___lam__1(
    mut v___f_1554_: *mut LeanObject,
    mut v___y_1555_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1557_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reason_1558_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1559_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1560_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reason_1561_: *mut LeanObject = core::ptr::null_mut();
    let mut v_consumers_1562_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1564_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1565_: u8 = 0;
    let mut v___x_1566_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1567_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1569_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1570_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1571_: u8 = 0;
    let mut v___x_1572_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1573_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1574_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1575_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1576_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1577_: u8 = 0;
    let mut v___x_1579_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1580_: u8 = 0;
    let mut v___x_1581_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1583_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1584_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1585_: u8 = 0;
    let mut v_unused_1586_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1557_ = lean_st_ref_get(v___y_1555_);
                v_reason_1558_ = lean_ctor_get(v___x_1557_, 0);
                lean_inc(v_reason_1558_);
                lean_dec(v___x_1557_);
                if lean_obj_tag(v_reason_1558_) == 0 {
                    v___x_1559_ = lean_io_promise_new();
                    v___x_1560_ = lean_st_ref_take(v___y_1555_);
                    v_reason_1561_ = lean_ctor_get(v___x_1560_, 0);
                    v_consumers_1562_ = lean_ctor_get(v___x_1560_, 1);
                    v_isSharedCheck_1577_ = (!lean_is_exclusive(v___x_1560_)) as u8;
                    if v_isSharedCheck_1577_ == 0 {
                        v___x_1564_ = v___x_1560_;
                        v_isShared_1565_ = v_isSharedCheck_1577_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_consumers_1562_);
                        lean_inc(v_reason_1561_);
                        lean_dec(v___x_1560_);
                        v___x_1564_ = lean_box(0);
                        v_isShared_1565_ = v_isSharedCheck_1577_;
                        state = 1;
                        continue;
                    }
                } else {
                    lean_dec_ref(v___f_1554_);
                    v_isSharedCheck_1585_ = (!lean_is_exclusive(v_reason_1558_)) as u8;
                    if v_isSharedCheck_1585_ == 0 {
                        v_unused_1586_ = lean_ctor_get(v_reason_1558_, 0);
                        lean_dec(v_unused_1586_);
                        v___x_1579_ = v_reason_1558_;
                        v_isShared_1580_ = v_isSharedCheck_1585_;
                        state = 3;
                        continue;
                    } else {
                        lean_dec(v_reason_1558_);
                        v___x_1579_ = lean_box(0);
                        v_isShared_1580_ = v_isSharedCheck_1585_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                lean_inc(v___x_1559_);
                v___x_1566_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_1566_, 0, v___x_1559_);
                v___x_1567_ = l_Std_Queue_enqueue___redArg(v___x_1566_, v_consumers_1562_);
                if v_isShared_1565_ == 0 {
                    lean_ctor_set(v___x_1564_, 1, v___x_1567_);
                    v___x_1569_ = v___x_1564_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1576_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1576_, 0, v_reason_1561_);
                    lean_ctor_set(v_reuseFailAlloc_1576_, 1, v___x_1567_);
                    v___x_1569_ = v_reuseFailAlloc_1576_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_1570_ = lean_st_ref_set(v___y_1555_, v___x_1569_);
                v___x_1571_ = 0;
                v___x_1572_ = lean_io_promise_result_opt(v___x_1559_);
                lean_dec(v___x_1559_);
                v___x_1573_ = lean_unsigned_to_nat(0);
                v___x_1574_ = lean_io_bind_task(v___x_1572_, v___f_1554_, v___x_1573_, v___x_1571_);
                v___x_1575_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_1575_, 0, v___x_1574_);
                return v___x_1575_;
            }
            3 => {
                v___x_1581_ = lean_obj_once(
                    core::ptr::addr_of_mut!(l_Std_CancellationToken_wait___lam__0___closed__4),
                    core::ptr::addr_of_mut!(l_Std_CancellationToken_wait___lam__0___closed__4_once),
                    _init_l_Std_CancellationToken_wait___lam__0___closed__4,
                );
                if v_isShared_1580_ == 0 {
                    lean_ctor_set_tag(v___x_1579_, 0);
                    lean_ctor_set(v___x_1579_, 0, v___x_1581_);
                    v___x_1583_ = v___x_1579_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1584_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1584_, 0, v___x_1581_);
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
    mut v___f_1587_: *mut LeanObject,
    mut v___y_1588_: *mut LeanObject,
    mut v___y_1589_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1590_: *mut LeanObject = core::ptr::null_mut();
    v_res_1590_ = l_Std_CancellationToken_wait___lam__1(v___f_1587_, v___y_1588_);
    lean_dec(v___y_1588_);
    return v_res_1590_;
}
pub unsafe fn l_Std_CancellationToken_wait(mut v_x_1594_: *mut LeanObject) -> *mut LeanObject {
    let mut v___f_1596_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1597_: *mut LeanObject = core::ptr::null_mut();
    v___f_1596_ = l_Std_CancellationToken_wait___closed__1;
    v___x_1597_ = l_Std_Mutex_atomically___at___00Std_CancellationToken_wait_spec__0___redArg(
        v_x_1594_,
        v___f_1596_,
    );
    return v___x_1597_;
}
pub unsafe fn l_Std_CancellationToken_wait___boxed(
    mut v_x_1598_: *mut LeanObject,
    mut v_a_1599_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1600_: *mut LeanObject = core::ptr::null_mut();
    v_res_1600_ = l_Std_CancellationToken_wait(v_x_1598_);
    return v_res_1600_;
}
pub unsafe fn l_Std_Async_Waiter_race___at___00Std_CancellationToken_selector_spec__0___lam__0(
    mut v___x_1601_: u8,
    mut v_x_1602_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_1604_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1606_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1607_: u8 = 0;
    let mut v___x_1609_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1610_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1611_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1612_: u8 = 0;
    let mut v___x_1614_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1615_: u8 = 0;
    let mut v___x_1616_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1618_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1619_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1620_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1621_: u8 = 0;
    let mut v_unused_1622_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_1602_) == 0 {
                    v_a_1604_ = lean_ctor_get(v_x_1602_, 0);
                    v_isSharedCheck_1612_ = (!lean_is_exclusive(v_x_1602_)) as u8;
                    if v_isSharedCheck_1612_ == 0 {
                        v___x_1606_ = v_x_1602_;
                        v_isShared_1607_ = v_isSharedCheck_1612_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_1604_);
                        lean_dec(v_x_1602_);
                        v___x_1606_ = lean_box(0);
                        v_isShared_1607_ = v_isSharedCheck_1612_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_isSharedCheck_1621_ = (!lean_is_exclusive(v_x_1602_)) as u8;
                    if v_isSharedCheck_1621_ == 0 {
                        v_unused_1622_ = lean_ctor_get(v_x_1602_, 0);
                        lean_dec(v_unused_1622_);
                        v___x_1614_ = v_x_1602_;
                        v_isShared_1615_ = v_isSharedCheck_1621_;
                        state = 3;
                        continue;
                    } else {
                        lean_dec(v_x_1602_);
                        v___x_1614_ = lean_box(0);
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
                    v_reuseFailAlloc_1611_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1611_, 0, v_a_1604_);
                    v___x_1609_ = v_reuseFailAlloc_1611_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_1610_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_1610_, 0, v___x_1609_);
                return v___x_1610_;
            }
            3 => {
                v___x_1616_ = lean_box((v___x_1601_) as usize);
                if v_isShared_1615_ == 0 {
                    lean_ctor_set(v___x_1614_, 0, v___x_1616_);
                    v___x_1618_ = v___x_1614_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1620_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1620_, 0, v___x_1616_);
                    v___x_1618_ = v_reuseFailAlloc_1620_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_1619_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_1619_, 0, v___x_1618_);
                return v___x_1619_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Async_Waiter_race___at___00Std_CancellationToken_selector_spec__0___lam__0___boxed(
    mut v___x_1623_: *mut LeanObject,
    mut v_x_1624_: *mut LeanObject,
    mut v___y_1625_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6814__boxed_1626_: u8 = 0;
    let mut v_res_1627_: *mut LeanObject = core::ptr::null_mut();
    v___x_6814__boxed_1626_ = (lean_unbox(v___x_1623_) as u8);
    v_res_1627_ = l_Std_Async_Waiter_race___at___00Std_CancellationToken_selector_spec__0___lam__0(
        v___x_6814__boxed_1626_,
        v_x_1624_,
    );
    return v_res_1627_;
}
pub unsafe fn l_Std_Async_Waiter_race___at___00Std_CancellationToken_selector_spec__0___lam__1(
    mut v_lose_1628_: *mut LeanObject,
    mut v___y_1629_: *mut LeanObject,
    mut v_promise_1630_: *mut LeanObject,
    mut v___f_1631_: *mut LeanObject,
    mut v_x_1632_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1634_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1635_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1637_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1638_: u8 = 0;
    let mut v___x_1639_: u8 = 0;
    let mut v___x_1640_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1641_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1642_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1644_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1645_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1646_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1647_: u8 = 0;
    let mut v___x_1648_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1649_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1650_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_1632_) == 0 {
                    lean_dec_ref(v___f_1631_);
                    lean_dec_ref(v_lose_1628_);
                    v___x_1634_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_1634_, 0, v_x_1632_);
                    return v___x_1634_;
                } else {
                    v_a_1635_ = lean_ctor_get(v_x_1632_, 0);
                    v_isSharedCheck_1650_ = (!lean_is_exclusive(v_x_1632_)) as u8;
                    if v_isSharedCheck_1650_ == 0 {
                        v___x_1637_ = v_x_1632_;
                        v_isShared_1638_ = v_isSharedCheck_1650_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_1635_);
                        lean_dec(v_x_1632_);
                        v___x_1637_ = lean_box(0);
                        v_isShared_1638_ = v_isSharedCheck_1650_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_1639_ = (lean_unbox(v_a_1635_) as u8);
                lean_dec(v_a_1635_);
                if v___x_1639_ == 0 {
                    lean_del_object(v___x_1637_);
                    lean_dec_ref(v___f_1631_);
                    lean_inc(v___y_1629_);
                    v___x_1640_ = lean_apply_2(v_lose_1628_, v___y_1629_, lean_box(0));
                    return v___x_1640_;
                } else {
                    lean_dec_ref(v_lose_1628_);
                    v___x_1641_ = l_Std_Async_Waiter_race___at___00Std_CancellationToken_Consumer_resolve_spec__0___closed__0;
                    v___x_1642_ = lean_io_promise_resolve(v___x_1641_, v_promise_1630_);
                    if v_isShared_1638_ == 0 {
                        lean_ctor_set(v___x_1637_, 0, v___x_1642_);
                        v___x_1644_ = v___x_1637_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_1649_ = lean_alloc_ctor(1, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_1649_, 0, v___x_1642_);
                        v___x_1644_ = v_reuseFailAlloc_1649_;
                        state = 2;
                        continue;
                    }
                }
            }
            2 => {
                v___x_1645_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_1645_, 0, v___x_1644_);
                v___x_1646_ = lean_unsigned_to_nat(0);
                v___x_1647_ = 0;
                v___x_1648_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(
                    lean_box(0),
                    lean_box(0),
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
    mut v_lose_1651_: *mut LeanObject,
    mut v___y_1652_: *mut LeanObject,
    mut v_promise_1653_: *mut LeanObject,
    mut v___f_1654_: *mut LeanObject,
    mut v_x_1655_: *mut LeanObject,
    mut v___y_1656_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1657_: *mut LeanObject = core::ptr::null_mut();
    v_res_1657_ = l_Std_Async_Waiter_race___at___00Std_CancellationToken_selector_spec__0___lam__1(
        v_lose_1651_,
        v___y_1652_,
        v_promise_1653_,
        v___f_1654_,
        v_x_1655_,
    );
    lean_dec(v_promise_1653_);
    lean_dec(v___y_1652_);
    return v_res_1657_;
}
pub unsafe fn l_Std_Async_Waiter_race___at___00Std_CancellationToken_selector_spec__0(
    mut v_w_1661_: *mut LeanObject,
    mut v_lose_1662_: *mut LeanObject,
    mut v___y_1663_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_finished_1665_: *mut LeanObject = core::ptr::null_mut();
    let mut v_promise_1666_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1667_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1668_: u8 = 0;
    let mut v___f_1669_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_1670_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1672_: u8 = 0;
    let mut v___x_1673_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1674_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1675_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1676_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1677_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1678_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1679_: u8 = 0;
    let mut v___x_1680_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1681_: u8 = 0;
    let mut v___x_1682_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_finished_1665_ = lean_ctor_get(v_w_1661_, 0);
                lean_inc(v_finished_1665_);
                v_promise_1666_ = lean_ctor_get(v_w_1661_, 1);
                lean_inc(v_promise_1666_);
                lean_dec_ref(v_w_1661_);
                v___x_1667_ = lean_st_ref_take(v_finished_1665_);
                v___x_1668_ = 1;
                v___f_1669_ = l_Std_Async_Waiter_race___at___00Std_CancellationToken_selector_spec__0___closed__0;
                lean_inc(v___y_1663_);
                v___f_1670_ = lean_alloc_closure(l_Std_Async_Waiter_race___at___00Std_CancellationToken_selector_spec__0___lam__1___boxed as *mut core::ffi::c_void, 6, 4);
                lean_closure_set(v___f_1670_, 0, v_lose_1662_);
                lean_closure_set(v___f_1670_, 1, v___y_1663_);
                lean_closure_set(v___f_1670_, 2, v_promise_1666_);
                lean_closure_set(v___f_1670_, 3, v___f_1669_);
                v___x_1681_ = (lean_unbox(v___x_1667_) as u8);
                lean_dec(v___x_1667_);
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
                v___x_1673_ = lean_box((v___x_1668_) as usize);
                v___x_1674_ = lean_st_ref_set(v_finished_1665_, v___x_1673_);
                lean_dec(v_finished_1665_);
                v___x_1675_ = lean_box((v___y_1672_) as usize);
                v___x_1676_ = lean_alloc_ctor(1, 1, (0) as u32);
                lean_ctor_set(v___x_1676_, 0, v___x_1675_);
                v___x_1677_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_1677_, 0, v___x_1676_);
                v___x_1678_ = lean_unsigned_to_nat(0);
                v___x_1679_ = 0;
                v___x_1680_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(
                    lean_box(0),
                    lean_box(0),
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
    mut v_w_1683_: *mut LeanObject,
    mut v_lose_1684_: *mut LeanObject,
    mut v___y_1685_: *mut LeanObject,
    mut v___y_1686_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1687_: *mut LeanObject = core::ptr::null_mut();
    v_res_1687_ = l_Std_Async_Waiter_race___at___00Std_CancellationToken_selector_spec__0(
        v_w_1683_,
        v_lose_1684_,
        v___y_1685_,
    );
    lean_dec(v___y_1685_);
    return v_res_1687_;
}
pub unsafe fn l_Std_Mutex_atomically___at___00Std_CancellationToken_selector_spec__1___redArg___lam__0(
    mut v_mutex_1688_: *mut LeanObject,
    mut v_x_1689_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1691_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1692_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1693_: *mut LeanObject = core::ptr::null_mut();
    v___x_1691_ = lean_io_basemutex_unlock(v_mutex_1688_);
    v___x_1692_ = lean_alloc_ctor(1, 1, (0) as u32);
    lean_ctor_set(v___x_1692_, 0, v___x_1691_);
    v___x_1693_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_1693_, 0, v___x_1692_);
    return v___x_1693_;
}
pub unsafe fn l_Std_Mutex_atomically___at___00Std_CancellationToken_selector_spec__1___redArg___lam__0___boxed(
    mut v_mutex_1694_: *mut LeanObject,
    mut v_x_1695_: *mut LeanObject,
    mut v___y_1696_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1697_: *mut LeanObject = core::ptr::null_mut();
    v_res_1697_ =
        l_Std_Mutex_atomically___at___00Std_CancellationToken_selector_spec__1___redArg___lam__0(
            v_mutex_1694_,
            v_x_1695_,
        );
    lean_dec(v_x_1695_);
    lean_dec(v_mutex_1694_);
    return v_res_1697_;
}
pub unsafe fn l_Std_Mutex_atomically___at___00Std_CancellationToken_selector_spec__1___redArg___lam__1(
    mut v_k_1698_: *mut LeanObject,
    mut v_ref_1699_: *mut LeanObject,
    mut v_x_1700_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_1702_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1704_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1705_: u8 = 0;
    let mut v___x_1707_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1708_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1709_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1710_: u8 = 0;
    let mut v___x_1711_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_1700_) == 0 {
                    lean_dec(v_ref_1699_);
                    lean_dec_ref(v_k_1698_);
                    v_a_1702_ = lean_ctor_get(v_x_1700_, 0);
                    v_isSharedCheck_1710_ = (!lean_is_exclusive(v_x_1700_)) as u8;
                    if v_isSharedCheck_1710_ == 0 {
                        v___x_1704_ = v_x_1700_;
                        v_isShared_1705_ = v_isSharedCheck_1710_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_1702_);
                        lean_dec(v_x_1700_);
                        v___x_1704_ = lean_box(0);
                        v_isShared_1705_ = v_isSharedCheck_1710_;
                        state = 1;
                        continue;
                    }
                } else {
                    lean_dec_ref_known(v_x_1700_, 1);
                    v___x_1711_ = lean_apply_2(v_k_1698_, v_ref_1699_, lean_box(0));
                    return v___x_1711_;
                }
            }
            1 => {
                if v_isShared_1705_ == 0 {
                    v___x_1707_ = v___x_1704_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1709_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1709_, 0, v_a_1702_);
                    v___x_1707_ = v_reuseFailAlloc_1709_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_1708_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_1708_, 0, v___x_1707_);
                return v___x_1708_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Mutex_atomically___at___00Std_CancellationToken_selector_spec__1___redArg___lam__1___boxed(
    mut v_k_1712_: *mut LeanObject,
    mut v_ref_1713_: *mut LeanObject,
    mut v_x_1714_: *mut LeanObject,
    mut v___y_1715_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1716_: *mut LeanObject = core::ptr::null_mut();
    v_res_1716_ =
        l_Std_Mutex_atomically___at___00Std_CancellationToken_selector_spec__1___redArg___lam__1(
            v_k_1712_,
            v_ref_1713_,
            v_x_1714_,
        );
    return v_res_1716_;
}
pub unsafe fn l_Std_Mutex_atomically___at___00Std_CancellationToken_selector_spec__1___redArg___lam__2(
    mut v_mutex_1717_: *mut LeanObject,
    mut v___f_1718_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1720_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1721_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1722_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1723_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1724_: u8 = 0;
    let mut v___x_1725_: *mut LeanObject = core::ptr::null_mut();
    v___x_1720_ = lean_io_basemutex_lock(v_mutex_1717_);
    v___x_1721_ = lean_alloc_ctor(1, 1, (0) as u32);
    lean_ctor_set(v___x_1721_, 0, v___x_1720_);
    v___x_1722_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_1722_, 0, v___x_1721_);
    v___x_1723_ = lean_unsigned_to_nat(0);
    v___x_1724_ = 0;
    v___x_1725_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(
        lean_box(0),
        lean_box(0),
        v___x_1723_,
        v___x_1724_,
        v___x_1722_,
        v___f_1718_,
    );
    return v___x_1725_;
}
pub unsafe fn l_Std_Mutex_atomically___at___00Std_CancellationToken_selector_spec__1___redArg___lam__2___boxed(
    mut v_mutex_1726_: *mut LeanObject,
    mut v___f_1727_: *mut LeanObject,
    mut v___y_1728_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1729_: *mut LeanObject = core::ptr::null_mut();
    v_res_1729_ =
        l_Std_Mutex_atomically___at___00Std_CancellationToken_selector_spec__1___redArg___lam__2(
            v_mutex_1726_,
            v___f_1727_,
        );
    lean_dec(v_mutex_1726_);
    return v_res_1729_;
}
pub unsafe fn l_Std_Mutex_atomically___at___00Std_CancellationToken_selector_spec__1___redArg___lam__3(
    mut v___y_1730_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_1731_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1733_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1734_: u8 = 0;
    let mut v___x_1736_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1737_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1738_: u8 = 0;
    let mut v_a_1739_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1741_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1742_: u8 = 0;
    let mut v_fst_1743_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1745_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1746_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1747_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v___y_1730_) == 0 {
                    v_a_1731_ = lean_ctor_get(v___y_1730_, 0);
                    v_isSharedCheck_1738_ = (!lean_is_exclusive(v___y_1730_)) as u8;
                    if v_isSharedCheck_1738_ == 0 {
                        v___x_1733_ = v___y_1730_;
                        v_isShared_1734_ = v_isSharedCheck_1738_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_1731_);
                        lean_dec(v___y_1730_);
                        v___x_1733_ = lean_box(0);
                        v_isShared_1734_ = v_isSharedCheck_1738_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_1739_ = lean_ctor_get(v___y_1730_, 0);
                    v_isSharedCheck_1747_ = (!lean_is_exclusive(v___y_1730_)) as u8;
                    if v_isSharedCheck_1747_ == 0 {
                        v___x_1741_ = v___y_1730_;
                        v_isShared_1742_ = v_isSharedCheck_1747_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_1739_);
                        lean_dec(v___y_1730_);
                        v___x_1741_ = lean_box(0);
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
                    v_reuseFailAlloc_1737_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1737_, 0, v_a_1731_);
                    v___x_1736_ = v_reuseFailAlloc_1737_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1736_;
            }
            3 => {
                v_fst_1743_ = lean_ctor_get(v_a_1739_, 0);
                lean_inc(v_fst_1743_);
                lean_dec(v_a_1739_);
                if v_isShared_1742_ == 0 {
                    lean_ctor_set(v___x_1741_, 0, v_fst_1743_);
                    v___x_1745_ = v___x_1741_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1746_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1746_, 0, v_fst_1743_);
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
    mut v_mutex_1749_: *mut LeanObject,
    mut v_k_1750_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_ref_1752_: *mut LeanObject = core::ptr::null_mut();
    let mut v_mutex_1753_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_1754_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_1755_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_1756_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1757_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1758_: u8 = 0;
    let mut v___x_1759_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1761_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1762_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1763_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1764_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1766_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1767_: u8 = 0;
    let mut v___x_1769_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1770_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1771_: u8 = 0;
    let mut v_a_1772_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1774_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1775_: u8 = 0;
    let mut v_fst_1776_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1778_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1779_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1780_: u8 = 0;
    let mut v_a_1781_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1783_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1784_: u8 = 0;
    let mut v___f_1785_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1786_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1788_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1789_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1790_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ref_1752_ = lean_ctor_get(v_mutex_1749_, 0);
                lean_inc(v_ref_1752_);
                v_mutex_1753_ = lean_ctor_get(v_mutex_1749_, 1);
                lean_inc_n(v_mutex_1753_, 2);
                lean_dec_ref(v_mutex_1749_);
                v___f_1754_ = lean_alloc_closure(l_Std_Mutex_atomically___at___00Std_CancellationToken_selector_spec__1___redArg___lam__0___boxed as *mut core::ffi::c_void, 3, 1);
                lean_closure_set(v___f_1754_, 0, v_mutex_1753_);
                v___f_1755_ = lean_alloc_closure(l_Std_Mutex_atomically___at___00Std_CancellationToken_selector_spec__1___redArg___lam__1___boxed as *mut core::ffi::c_void, 4, 2);
                lean_closure_set(v___f_1755_, 0, v_k_1750_);
                lean_closure_set(v___f_1755_, 1, v_ref_1752_);
                v___f_1756_ = lean_alloc_closure(l_Std_Mutex_atomically___at___00Std_CancellationToken_selector_spec__1___redArg___lam__2___boxed as *mut core::ffi::c_void, 3, 2);
                lean_closure_set(v___f_1756_, 0, v_mutex_1753_);
                lean_closure_set(v___f_1756_, 1, v___f_1755_);
                v___x_1757_ = lean_unsigned_to_nat(0);
                v___x_1758_ = 0;
                v___x_1759_ = l_Std_Async_EAsync_tryFinally_x27___redArg(
                    v___f_1756_,
                    v___f_1754_,
                    v___x_1757_,
                    v___x_1758_,
                );
                if lean_obj_tag(v___x_1759_) == 0 {
                    v_a_1763_ = lean_ctor_get(v___x_1759_, 0);
                    lean_inc(v_a_1763_);
                    lean_dec_ref_known(v___x_1759_, 1);
                    if lean_obj_tag(v_a_1763_) == 0 {
                        v_a_1764_ = lean_ctor_get(v_a_1763_, 0);
                        v_isSharedCheck_1771_ = (!lean_is_exclusive(v_a_1763_)) as u8;
                        if v_isSharedCheck_1771_ == 0 {
                            v___x_1766_ = v_a_1763_;
                            v_isShared_1767_ = v_isSharedCheck_1771_;
                            state = 2;
                            continue;
                        } else {
                            lean_inc(v_a_1764_);
                            lean_dec(v_a_1763_);
                            v___x_1766_ = lean_box(0);
                            v_isShared_1767_ = v_isSharedCheck_1771_;
                            state = 2;
                            continue;
                        }
                    } else {
                        v_a_1772_ = lean_ctor_get(v_a_1763_, 0);
                        v_isSharedCheck_1780_ = (!lean_is_exclusive(v_a_1763_)) as u8;
                        if v_isSharedCheck_1780_ == 0 {
                            v___x_1774_ = v_a_1763_;
                            v_isShared_1775_ = v_isSharedCheck_1780_;
                            state = 4;
                            continue;
                        } else {
                            lean_inc(v_a_1772_);
                            lean_dec(v_a_1763_);
                            v___x_1774_ = lean_box(0);
                            v_isShared_1775_ = v_isSharedCheck_1780_;
                            state = 4;
                            continue;
                        }
                    }
                } else {
                    v_a_1781_ = lean_ctor_get(v___x_1759_, 0);
                    v_isSharedCheck_1790_ = (!lean_is_exclusive(v___x_1759_)) as u8;
                    if v_isSharedCheck_1790_ == 0 {
                        v___x_1783_ = v___x_1759_;
                        v_isShared_1784_ = v_isSharedCheck_1790_;
                        state = 6;
                        continue;
                    } else {
                        lean_inc(v_a_1781_);
                        lean_dec(v___x_1759_);
                        v___x_1783_ = lean_box(0);
                        v_isShared_1784_ = v_isSharedCheck_1790_;
                        state = 6;
                        continue;
                    }
                }
            }
            1 => {
                v___x_1762_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_1762_, 0, v___y_1761_);
                return v___x_1762_;
            }
            2 => {
                if v_isShared_1767_ == 0 {
                    v___x_1769_ = v___x_1766_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_1770_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1770_, 0, v_a_1764_);
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
                v_fst_1776_ = lean_ctor_get(v_a_1772_, 0);
                lean_inc(v_fst_1776_);
                lean_dec(v_a_1772_);
                if v_isShared_1775_ == 0 {
                    lean_ctor_set(v___x_1774_, 0, v_fst_1776_);
                    v___x_1778_ = v___x_1774_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_1779_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1779_, 0, v_fst_1776_);
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
                    lean_ctor_set(v___x_1783_, 0, v___x_1786_);
                    v___x_1788_ = v___x_1783_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_1789_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1789_, 0, v___x_1786_);
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
    mut v_mutex_1791_: *mut LeanObject,
    mut v_k_1792_: *mut LeanObject,
    mut v___y_1793_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1794_: *mut LeanObject = core::ptr::null_mut();
    v_res_1794_ = l_Std_Mutex_atomically___at___00Std_CancellationToken_selector_spec__1___redArg(
        v_mutex_1791_,
        v_k_1792_,
    );
    return v_res_1794_;
}
pub unsafe fn l_Std_Mutex_atomically___at___00Std_CancellationToken_selector_spec__1(
    mut v_00_u03b1_1795_: *mut LeanObject,
    mut v_00_u03b2_1796_: *mut LeanObject,
    mut v_mutex_1797_: *mut LeanObject,
    mut v_k_1798_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1800_: *mut LeanObject = core::ptr::null_mut();
    v___x_1800_ = l_Std_Mutex_atomically___at___00Std_CancellationToken_selector_spec__1___redArg(
        v_mutex_1797_,
        v_k_1798_,
    );
    return v___x_1800_;
}
pub unsafe fn l_Std_Mutex_atomically___at___00Std_CancellationToken_selector_spec__1___boxed(
    mut v_00_u03b1_1801_: *mut LeanObject,
    mut v_00_u03b2_1802_: *mut LeanObject,
    mut v_mutex_1803_: *mut LeanObject,
    mut v_k_1804_: *mut LeanObject,
    mut v___y_1805_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1806_: *mut LeanObject = core::ptr::null_mut();
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
    mut v___y_1808_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1810_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1811_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1812_: *mut LeanObject = core::ptr::null_mut();
    v___x_1810_ = lean_box((v___x_1807_) as usize);
    v___x_1811_ = lean_alloc_ctor(1, 1, (0) as u32);
    lean_ctor_set(v___x_1811_, 0, v___x_1810_);
    v___x_1812_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_1812_, 0, v___x_1811_);
    return v___x_1812_;
}
pub unsafe fn l_Std_CancellationToken_selector___lam__0___boxed(
    mut v___x_1813_: *mut LeanObject,
    mut v___y_1814_: *mut LeanObject,
    mut v___y_1815_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_7132__boxed_1816_: u8 = 0;
    let mut v_res_1817_: *mut LeanObject = core::ptr::null_mut();
    v___x_7132__boxed_1816_ = (lean_unbox(v___x_1813_) as u8);
    v_res_1817_ = l_Std_CancellationToken_selector___lam__0(v___x_7132__boxed_1816_, v___y_1814_);
    lean_dec(v___y_1814_);
    return v_res_1817_;
}
pub unsafe fn l_Std_CancellationToken_selector___lam__1(
    mut v___x_1818_: *mut LeanObject,
    mut v___y_1819_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_1820_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1822_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1823_: u8 = 0;
    let mut v___x_1825_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1826_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1827_: u8 = 0;
    let mut v___x_1829_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1830_: u8 = 0;
    let mut v___x_1832_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1833_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1834_: u8 = 0;
    let mut v_unused_1835_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v___y_1819_) == 0 {
                    v_a_1820_ = lean_ctor_get(v___y_1819_, 0);
                    v_isSharedCheck_1827_ = (!lean_is_exclusive(v___y_1819_)) as u8;
                    if v_isSharedCheck_1827_ == 0 {
                        v___x_1822_ = v___y_1819_;
                        v_isShared_1823_ = v_isSharedCheck_1827_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_1820_);
                        lean_dec(v___y_1819_);
                        v___x_1822_ = lean_box(0);
                        v_isShared_1823_ = v_isSharedCheck_1827_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_isSharedCheck_1834_ = (!lean_is_exclusive(v___y_1819_)) as u8;
                    if v_isSharedCheck_1834_ == 0 {
                        v_unused_1835_ = lean_ctor_get(v___y_1819_, 0);
                        lean_dec(v_unused_1835_);
                        v___x_1829_ = v___y_1819_;
                        v_isShared_1830_ = v_isSharedCheck_1834_;
                        state = 3;
                        continue;
                    } else {
                        lean_dec(v___y_1819_);
                        v___x_1829_ = lean_box(0);
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
                    v_reuseFailAlloc_1826_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1826_, 0, v_a_1820_);
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
                    lean_ctor_set(v___x_1829_, 0, v___x_1818_);
                    v___x_1832_ = v___x_1829_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1833_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1833_, 0, v___x_1818_);
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
    mut v___y_1843_: *mut LeanObject,
    mut v_waiter_1844_: *mut LeanObject,
    mut v_x_1845_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_1847_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1849_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1850_: u8 = 0;
    let mut v___x_1852_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1853_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1854_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1855_: u8 = 0;
    let mut v_a_1856_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reason_1857_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1858_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reason_1859_: *mut LeanObject = core::ptr::null_mut();
    let mut v_consumers_1860_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1862_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1863_: u8 = 0;
    let mut v___x_1864_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1865_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1867_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1868_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1869_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1870_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1871_: u8 = 0;
    let mut v___x_1873_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1874_: u8 = 0;
    let mut v___x_1875_: u8 = 0;
    let mut v___f_1876_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1877_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1879_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1881_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1882_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1883_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1884_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1886_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1887_: u8 = 0;
    let mut v___x_1889_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1890_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1891_: u8 = 0;
    let mut v___x_1892_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1893_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1895_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1896_: u8 = 0;
    let mut v___f_1897_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1898_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1899_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1901_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1902_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1903_: u8 = 0;
    let mut v_isSharedCheck_1904_: u8 = 0;
    let mut v_unused_1905_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_1845_) == 0 {
                    lean_dec_ref(v_waiter_1844_);
                    v_a_1847_ = lean_ctor_get(v_x_1845_, 0);
                    v_isSharedCheck_1855_ = (!lean_is_exclusive(v_x_1845_)) as u8;
                    if v_isSharedCheck_1855_ == 0 {
                        v___x_1849_ = v_x_1845_;
                        v_isShared_1850_ = v_isSharedCheck_1855_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_1847_);
                        lean_dec(v_x_1845_);
                        v___x_1849_ = lean_box(0);
                        v_isShared_1850_ = v_isSharedCheck_1855_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_1856_ = lean_ctor_get(v_x_1845_, 0);
                    lean_inc(v_a_1856_);
                    lean_dec_ref_known(v_x_1845_, 1);
                    v_reason_1857_ = lean_ctor_get(v_a_1856_, 0);
                    lean_inc(v_reason_1857_);
                    lean_dec(v_a_1856_);
                    if lean_obj_tag(v_reason_1857_) == 0 {
                        v___x_1858_ = lean_st_ref_take(v___y_1843_);
                        v_reason_1859_ = lean_ctor_get(v___x_1858_, 0);
                        v_consumers_1860_ = lean_ctor_get(v___x_1858_, 1);
                        v_isSharedCheck_1871_ = (!lean_is_exclusive(v___x_1858_)) as u8;
                        if v_isSharedCheck_1871_ == 0 {
                            v___x_1862_ = v___x_1858_;
                            v_isShared_1863_ = v_isSharedCheck_1871_;
                            state = 3;
                            continue;
                        } else {
                            lean_inc(v_consumers_1860_);
                            lean_inc(v_reason_1859_);
                            lean_dec(v___x_1858_);
                            v___x_1862_ = lean_box(0);
                            v_isShared_1863_ = v_isSharedCheck_1871_;
                            state = 3;
                            continue;
                        }
                    } else {
                        v_isSharedCheck_1904_ = (!lean_is_exclusive(v_reason_1857_)) as u8;
                        if v_isSharedCheck_1904_ == 0 {
                            v_unused_1905_ = lean_ctor_get(v_reason_1857_, 0);
                            lean_dec(v_unused_1905_);
                            v___x_1873_ = v_reason_1857_;
                            v_isShared_1874_ = v_isSharedCheck_1904_;
                            state = 5;
                            continue;
                        } else {
                            lean_dec(v_reason_1857_);
                            v___x_1873_ = lean_box(0);
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
                    v_reuseFailAlloc_1854_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1854_, 0, v_a_1847_);
                    v___x_1852_ = v_reuseFailAlloc_1854_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_1853_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_1853_, 0, v___x_1852_);
                return v___x_1853_;
            }
            3 => {
                v___x_1864_ = lean_alloc_ctor(1, 1, (0) as u32);
                lean_ctor_set(v___x_1864_, 0, v_waiter_1844_);
                v___x_1865_ = l_Std_Queue_enqueue___redArg(v___x_1864_, v_consumers_1860_);
                if v_isShared_1863_ == 0 {
                    lean_ctor_set(v___x_1862_, 1, v___x_1865_);
                    v___x_1867_ = v___x_1862_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1870_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1870_, 0, v_reason_1859_);
                    lean_ctor_set(v_reuseFailAlloc_1870_, 1, v___x_1865_);
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
                if lean_obj_tag(v___x_1877_) == 0 {
                    v_a_1883_ = lean_ctor_get(v___x_1877_, 0);
                    lean_inc(v_a_1883_);
                    lean_dec_ref_known(v___x_1877_, 1);
                    if lean_obj_tag(v_a_1883_) == 0 {
                        v_a_1884_ = lean_ctor_get(v_a_1883_, 0);
                        v_isSharedCheck_1891_ = (!lean_is_exclusive(v_a_1883_)) as u8;
                        if v_isSharedCheck_1891_ == 0 {
                            v___x_1886_ = v_a_1883_;
                            v_isShared_1887_ = v_isSharedCheck_1891_;
                            state = 8;
                            continue;
                        } else {
                            lean_inc(v_a_1884_);
                            lean_dec(v_a_1883_);
                            v___x_1886_ = lean_box(0);
                            v_isShared_1887_ = v_isSharedCheck_1891_;
                            state = 8;
                            continue;
                        }
                    } else {
                        lean_dec_ref_known(v_a_1883_, 1);
                        v___x_1892_ = l_Std_Async_Waiter_race___at___00Std_CancellationToken_Consumer_resolve_spec__0___closed__0;
                        v___y_1879_ = v___x_1892_;
                        state = 6;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_1873_);
                    v_a_1893_ = lean_ctor_get(v___x_1877_, 0);
                    v_isSharedCheck_1903_ = (!lean_is_exclusive(v___x_1877_)) as u8;
                    if v_isSharedCheck_1903_ == 0 {
                        v___x_1895_ = v___x_1877_;
                        v_isShared_1896_ = v_isSharedCheck_1903_;
                        state = 10;
                        continue;
                    } else {
                        lean_inc(v_a_1893_);
                        lean_dec(v___x_1877_);
                        v___x_1895_ = lean_box(0);
                        v_isShared_1896_ = v_isSharedCheck_1903_;
                        state = 10;
                        continue;
                    }
                }
            }
            6 => {
                if v_isShared_1874_ == 0 {
                    lean_ctor_set_tag(v___x_1873_, 0);
                    lean_ctor_set(v___x_1873_, 0, v___y_1879_);
                    v___x_1881_ = v___x_1873_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_1882_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1882_, 0, v___y_1879_);
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
                    v_reuseFailAlloc_1890_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1890_, 0, v_a_1884_);
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
                v___x_1898_ = lean_unsigned_to_nat(0);
                v___x_1899_ = lean_task_map(v___f_1897_, v_a_1893_, v___x_1898_, v___x_1875_);
                if v_isShared_1896_ == 0 {
                    lean_ctor_set(v___x_1895_, 0, v___x_1899_);
                    v___x_1901_ = v___x_1895_;
                    state = 11;
                    continue;
                } else {
                    v_reuseFailAlloc_1902_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1902_, 0, v___x_1899_);
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
    mut v___y_1906_: *mut LeanObject,
    mut v_waiter_1907_: *mut LeanObject,
    mut v_x_1908_: *mut LeanObject,
    mut v___y_1909_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1910_: *mut LeanObject = core::ptr::null_mut();
    v_res_1910_ = l_Std_CancellationToken_selector___lam__2(v___y_1906_, v_waiter_1907_, v_x_1908_);
    lean_dec(v___y_1906_);
    return v_res_1910_;
}
pub unsafe fn l_Std_CancellationToken_selector___lam__3(
    mut v_waiter_1911_: *mut LeanObject,
    mut v___y_1912_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1914_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_1915_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1916_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1917_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1918_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1919_: u8 = 0;
    let mut v___x_1920_: *mut LeanObject = core::ptr::null_mut();
    v___x_1914_ = lean_st_ref_get(v___y_1912_);
    lean_inc(v___y_1912_);
    v___f_1915_ = lean_alloc_closure(
        l_Std_CancellationToken_selector___lam__2___boxed as *mut core::ffi::c_void,
        4,
        2,
    );
    lean_closure_set(v___f_1915_, 0, v___y_1912_);
    lean_closure_set(v___f_1915_, 1, v_waiter_1911_);
    v___x_1916_ = lean_alloc_ctor(1, 1, (0) as u32);
    lean_ctor_set(v___x_1916_, 0, v___x_1914_);
    v___x_1917_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_1917_, 0, v___x_1916_);
    v___x_1918_ = lean_unsigned_to_nat(0);
    v___x_1919_ = 0;
    v___x_1920_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(
        lean_box(0),
        lean_box(0),
        v___x_1918_,
        v___x_1919_,
        v___x_1917_,
        v___f_1915_,
    );
    return v___x_1920_;
}
pub unsafe fn l_Std_CancellationToken_selector___lam__3___boxed(
    mut v_waiter_1921_: *mut LeanObject,
    mut v___y_1922_: *mut LeanObject,
    mut v___y_1923_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1924_: *mut LeanObject = core::ptr::null_mut();
    v_res_1924_ = l_Std_CancellationToken_selector___lam__3(v_waiter_1921_, v___y_1922_);
    lean_dec(v___y_1922_);
    return v_res_1924_;
}
pub unsafe fn l_Std_CancellationToken_selector___lam__4(
    mut v_token_1925_: *mut LeanObject,
    mut v_waiter_1926_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_1928_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1929_: *mut LeanObject = core::ptr::null_mut();
    v___f_1928_ = lean_alloc_closure(
        l_Std_CancellationToken_selector___lam__3___boxed as *mut core::ffi::c_void,
        3,
        1,
    );
    lean_closure_set(v___f_1928_, 0, v_waiter_1926_);
    v___x_1929_ = l_Std_Mutex_atomically___at___00Std_CancellationToken_selector_spec__1___redArg(
        v_token_1925_,
        v___f_1928_,
    );
    return v___x_1929_;
}
pub unsafe fn l_Std_CancellationToken_selector___lam__4___boxed(
    mut v_token_1930_: *mut LeanObject,
    mut v_waiter_1931_: *mut LeanObject,
    mut v___y_1932_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1933_: *mut LeanObject = core::ptr::null_mut();
    v_res_1933_ = l_Std_CancellationToken_selector___lam__4(v_token_1930_, v_waiter_1931_);
    return v_res_1933_;
}
pub unsafe fn l_Std_CancellationToken_selector___lam__5(
    mut v_x_1944_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_1946_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1948_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1949_: u8 = 0;
    let mut v___x_1951_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1952_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1953_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1954_: u8 = 0;
    let mut v_a_1955_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1956_: u8 = 0;
    let mut v___x_1957_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1958_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_1944_) == 0 {
                    v_a_1946_ = lean_ctor_get(v_x_1944_, 0);
                    v_isSharedCheck_1954_ = (!lean_is_exclusive(v_x_1944_)) as u8;
                    if v_isSharedCheck_1954_ == 0 {
                        v___x_1948_ = v_x_1944_;
                        v_isShared_1949_ = v_isSharedCheck_1954_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_1946_);
                        lean_dec(v_x_1944_);
                        v___x_1948_ = lean_box(0);
                        v_isShared_1949_ = v_isSharedCheck_1954_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_1955_ = lean_ctor_get(v_x_1944_, 0);
                    lean_inc(v_a_1955_);
                    lean_dec_ref_known(v_x_1944_, 1);
                    v___x_1956_ = (lean_unbox(v_a_1955_) as u8);
                    lean_dec(v_a_1955_);
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
                    v_reuseFailAlloc_1953_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1953_, 0, v_a_1946_);
                    v___x_1951_ = v_reuseFailAlloc_1953_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_1952_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_1952_, 0, v___x_1951_);
                return v___x_1952_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_CancellationToken_selector___lam__5___boxed(
    mut v_x_1959_: *mut LeanObject,
    mut v___y_1960_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1961_: *mut LeanObject = core::ptr::null_mut();
    v_res_1961_ = l_Std_CancellationToken_selector___lam__5(v_x_1959_);
    return v_res_1961_;
}
pub unsafe fn l_Std_CancellationToken_selector___lam__6(
    mut v_token_1962_: *mut LeanObject,
    mut v___f_1963_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1965_: u8 = 0;
    let mut v___x_1966_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1967_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1968_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1969_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1970_: u8 = 0;
    let mut v___x_1971_: *mut LeanObject = core::ptr::null_mut();
    v___x_1965_ = l_Std_CancellationToken_isCancelled(v_token_1962_);
    v___x_1966_ = lean_box((v___x_1965_) as usize);
    v___x_1967_ = lean_alloc_ctor(1, 1, (0) as u32);
    lean_ctor_set(v___x_1967_, 0, v___x_1966_);
    v___x_1968_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_1968_, 0, v___x_1967_);
    v___x_1969_ = lean_unsigned_to_nat(0);
    v___x_1970_ = 0;
    v___x_1971_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(
        lean_box(0),
        lean_box(0),
        v___x_1969_,
        v___x_1970_,
        v___x_1968_,
        v___f_1963_,
    );
    return v___x_1971_;
}
pub unsafe fn l_Std_CancellationToken_selector___lam__6___boxed(
    mut v_token_1972_: *mut LeanObject,
    mut v___f_1973_: *mut LeanObject,
    mut v___y_1974_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1975_: *mut LeanObject = core::ptr::null_mut();
    v_res_1975_ = l_Std_CancellationToken_selector___lam__6(v_token_1972_, v___f_1973_);
    return v_res_1975_;
}
pub unsafe fn l_Std_CancellationToken_selector___lam__7(
    mut v_reason_1976_: *mut LeanObject,
    mut v___y_1977_: *mut LeanObject,
    mut v_x_1978_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_1980_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1982_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1983_: u8 = 0;
    let mut v___x_1985_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1986_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1987_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1988_: u8 = 0;
    let mut v_a_1989_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1991_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1992_: u8 = 0;
    let mut v___x_1993_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1994_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1996_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1997_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1998_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1999_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_1978_) == 0 {
                    lean_dec(v_reason_1976_);
                    v_a_1980_ = lean_ctor_get(v_x_1978_, 0);
                    v_isSharedCheck_1988_ = (!lean_is_exclusive(v_x_1978_)) as u8;
                    if v_isSharedCheck_1988_ == 0 {
                        v___x_1982_ = v_x_1978_;
                        v_isShared_1983_ = v_isSharedCheck_1988_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_1980_);
                        lean_dec(v_x_1978_);
                        v___x_1982_ = lean_box(0);
                        v_isShared_1983_ = v_isSharedCheck_1988_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_1989_ = lean_ctor_get(v_x_1978_, 0);
                    v_isSharedCheck_1999_ = (!lean_is_exclusive(v_x_1978_)) as u8;
                    if v_isSharedCheck_1999_ == 0 {
                        v___x_1991_ = v_x_1978_;
                        v_isShared_1992_ = v_isSharedCheck_1999_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_1989_);
                        lean_dec(v_x_1978_);
                        v___x_1991_ = lean_box(0);
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
                    v_reuseFailAlloc_1987_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1987_, 0, v_a_1980_);
                    v___x_1985_ = v_reuseFailAlloc_1987_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_1986_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_1986_, 0, v___x_1985_);
                return v___x_1986_;
            }
            3 => {
                v___x_1993_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_1993_, 0, v_reason_1976_);
                lean_ctor_set(v___x_1993_, 1, v_a_1989_);
                v___x_1994_ = lean_st_ref_set(v___y_1977_, v___x_1993_);
                if v_isShared_1992_ == 0 {
                    lean_ctor_set(v___x_1991_, 0, v___x_1994_);
                    v___x_1996_ = v___x_1991_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1998_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1998_, 0, v___x_1994_);
                    v___x_1996_ = v_reuseFailAlloc_1998_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_1997_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_1997_, 0, v___x_1996_);
                return v___x_1997_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_CancellationToken_selector___lam__7___boxed(
    mut v_reason_2000_: *mut LeanObject,
    mut v___y_2001_: *mut LeanObject,
    mut v_x_2002_: *mut LeanObject,
    mut v___y_2003_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2004_: *mut LeanObject = core::ptr::null_mut();
    v_res_2004_ = l_Std_CancellationToken_selector___lam__7(v_reason_2000_, v___y_2001_, v_x_2002_);
    lean_dec(v___y_2001_);
    return v_res_2004_;
}
pub unsafe fn l_Std_Queue_filterM___at___00Std_CancellationToken_selector_spec__2___lam__0(
    mut v_x_2005_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2007_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2008_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2010_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2011_: u8 = 0;
    let mut v___x_2012_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2014_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2015_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2016_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2017_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_2005_) == 0 {
                    v___x_2007_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_2007_, 0, v_x_2005_);
                    return v___x_2007_;
                } else {
                    v_a_2008_ = lean_ctor_get(v_x_2005_, 0);
                    v_isSharedCheck_2017_ = (!lean_is_exclusive(v_x_2005_)) as u8;
                    if v_isSharedCheck_2017_ == 0 {
                        v___x_2010_ = v_x_2005_;
                        v_isShared_2011_ = v_isSharedCheck_2017_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_2008_);
                        lean_dec(v_x_2005_);
                        v___x_2010_ = lean_box(0);
                        v_isShared_2011_ = v_isSharedCheck_2017_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_2012_ = l_List_reverse___redArg(v_a_2008_);
                if v_isShared_2011_ == 0 {
                    lean_ctor_set(v___x_2010_, 0, v___x_2012_);
                    v___x_2014_ = v___x_2010_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2016_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2016_, 0, v___x_2012_);
                    v___x_2014_ = v_reuseFailAlloc_2016_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_2015_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_2015_, 0, v___x_2014_);
                return v___x_2015_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Queue_filterM___at___00Std_CancellationToken_selector_spec__2___lam__0___boxed(
    mut v_x_2018_: *mut LeanObject,
    mut v___y_2019_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2020_: *mut LeanObject = core::ptr::null_mut();
    v_res_2020_ =
        l_Std_Queue_filterM___at___00Std_CancellationToken_selector_spec__2___lam__0(v_x_2018_);
    return v_res_2020_;
}
pub unsafe fn l_Std_Queue_filterM___at___00Std_CancellationToken_selector_spec__2___lam__2(
    mut v_a_2021_: *mut LeanObject,
    mut v___x_2022_: *mut LeanObject,
    mut v_x_2023_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_2025_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2027_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2028_: u8 = 0;
    let mut v___x_2030_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2031_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2032_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2033_: u8 = 0;
    let mut v_a_2034_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2036_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2037_: u8 = 0;
    let mut v___x_2038_: u8 = 0;
    let mut v___x_2039_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2041_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2042_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2043_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2044_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2045_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2047_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2048_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2049_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2050_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_2023_) == 0 {
                    lean_dec(v___x_2022_);
                    lean_dec(v_a_2021_);
                    v_a_2025_ = lean_ctor_get(v_x_2023_, 0);
                    v_isSharedCheck_2033_ = (!lean_is_exclusive(v_x_2023_)) as u8;
                    if v_isSharedCheck_2033_ == 0 {
                        v___x_2027_ = v_x_2023_;
                        v_isShared_2028_ = v_isSharedCheck_2033_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_2025_);
                        lean_dec(v_x_2023_);
                        v___x_2027_ = lean_box(0);
                        v_isShared_2028_ = v_isSharedCheck_2033_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_2034_ = lean_ctor_get(v_x_2023_, 0);
                    v_isSharedCheck_2050_ = (!lean_is_exclusive(v_x_2023_)) as u8;
                    if v_isSharedCheck_2050_ == 0 {
                        v___x_2036_ = v_x_2023_;
                        v_isShared_2037_ = v_isSharedCheck_2050_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_2034_);
                        lean_dec(v_x_2023_);
                        v___x_2036_ = lean_box(0);
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
                    v_reuseFailAlloc_2032_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2032_, 0, v_a_2025_);
                    v___x_2030_ = v_reuseFailAlloc_2032_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_2031_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_2031_, 0, v___x_2030_);
                return v___x_2031_;
            }
            3 => {
                v___x_2038_ = l_List_isEmpty___redArg(v_a_2021_);
                if v___x_2038_ == 0 {
                    lean_dec(v___x_2022_);
                    v___x_2039_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v___x_2039_, 0, v_a_2034_);
                    lean_ctor_set(v___x_2039_, 1, v_a_2021_);
                    if v_isShared_2037_ == 0 {
                        lean_ctor_set(v___x_2036_, 0, v___x_2039_);
                        v___x_2041_ = v___x_2036_;
                        state = 4;
                        continue;
                    } else {
                        v_reuseFailAlloc_2043_ = lean_alloc_ctor(1, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_2043_, 0, v___x_2039_);
                        v___x_2041_ = v_reuseFailAlloc_2043_;
                        state = 4;
                        continue;
                    }
                } else {
                    lean_dec(v_a_2021_);
                    v___x_2044_ = l_List_reverse___redArg(v_a_2034_);
                    v___x_2045_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v___x_2045_, 0, v___x_2022_);
                    lean_ctor_set(v___x_2045_, 1, v___x_2044_);
                    if v_isShared_2037_ == 0 {
                        lean_ctor_set(v___x_2036_, 0, v___x_2045_);
                        v___x_2047_ = v___x_2036_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_2049_ = lean_alloc_ctor(1, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_2049_, 0, v___x_2045_);
                        v___x_2047_ = v_reuseFailAlloc_2049_;
                        state = 5;
                        continue;
                    }
                }
            }
            4 => {
                v___x_2042_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_2042_, 0, v___x_2041_);
                return v___x_2042_;
            }
            5 => {
                v___x_2048_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_2048_, 0, v___x_2047_);
                return v___x_2048_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Queue_filterM___at___00Std_CancellationToken_selector_spec__2___lam__2___boxed(
    mut v_a_2051_: *mut LeanObject,
    mut v___x_2052_: *mut LeanObject,
    mut v_x_2053_: *mut LeanObject,
    mut v___y_2054_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2055_: *mut LeanObject = core::ptr::null_mut();
    v_res_2055_ = l_Std_Queue_filterM___at___00Std_CancellationToken_selector_spec__2___lam__2(
        v_a_2051_,
        v___x_2052_,
        v_x_2053_,
    );
    return v_res_2055_;
}
pub unsafe fn l_List_filterAuxM___at___00Std_Queue_filterM___at___00Std_CancellationToken_selector_spec__2_spec__2___redArg___lam__1(
    mut v_x_2056_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___y_2059_: u8 = 0;
    let mut v___x_2060_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2061_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2062_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2063_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2064_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2065_: u8 = 0;
    let mut v___x_2066_: u8 = 0;
    let mut v___x_2067_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_2056_) == 0 {
                    v___x_2063_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_2063_, 0, v_x_2056_);
                    return v___x_2063_;
                } else {
                    v_a_2064_ = lean_ctor_get(v_x_2056_, 0);
                    lean_inc(v_a_2064_);
                    lean_dec_ref_known(v_x_2056_, 1);
                    v___x_2065_ = (lean_unbox(v_a_2064_) as u8);
                    lean_dec(v_a_2064_);
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
                v___x_2060_ = lean_box((v___y_2059_) as usize);
                v___x_2061_ = lean_alloc_ctor(1, 1, (0) as u32);
                lean_ctor_set(v___x_2061_, 0, v___x_2060_);
                v___x_2062_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_2062_, 0, v___x_2061_);
                return v___x_2062_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_filterAuxM___at___00Std_Queue_filterM___at___00Std_CancellationToken_selector_spec__2_spec__2___redArg___lam__1___boxed(
    mut v_x_2068_: *mut LeanObject,
    mut v___y_2069_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2070_: *mut LeanObject = core::ptr::null_mut();
    v_res_2070_ = l_List_filterAuxM___at___00Std_Queue_filterM___at___00Std_CancellationToken_selector_spec__2_spec__2___redArg___lam__1(v_x_2068_);
    return v_res_2070_;
}
pub unsafe fn l_List_filterAuxM___at___00Std_Queue_filterM___at___00Std_CancellationToken_selector_spec__2_spec__2___redArg___lam__0___boxed(
    mut v_tail_2071_: *mut LeanObject,
    mut v_x_2072_: *mut LeanObject,
    mut v_head_2073_: *mut LeanObject,
    mut v_x_2074_: *mut LeanObject,
    mut v___y_2075_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2076_: *mut LeanObject = core::ptr::null_mut();
    v_res_2076_ = l_List_filterAuxM___at___00Std_Queue_filterM___at___00Std_CancellationToken_selector_spec__2_spec__2___redArg___lam__0(v_tail_2071_, v_x_2072_, v_head_2073_, v_x_2074_);
    return v_res_2076_;
}
pub unsafe fn l_List_filterAuxM___at___00Std_Queue_filterM___at___00Std_CancellationToken_selector_spec__2_spec__2___redArg(
    mut v_x_2083_: *mut LeanObject,
    mut v_x_2084_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2086_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2087_: *mut LeanObject = core::ptr::null_mut();
    let mut v_head_2088_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_2089_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2090_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_2092_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2093_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2094_: u8 = 0;
    let mut v___x_2095_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2096_: *mut LeanObject = core::ptr::null_mut();
    let mut v_finished_2097_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2099_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2100_: u8 = 0;
    let mut v_finished_2101_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2102_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2103_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2105_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2106_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2107_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2108_: u8 = 0;
    let mut v___x_2109_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2110_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2111_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_2083_) == 0 {
                    v___x_2086_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v___x_2086_, 0, v_x_2084_);
                    v___x_2087_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_2087_, 0, v___x_2086_);
                    return v___x_2087_;
                } else {
                    v_head_2088_ = lean_ctor_get(v_x_2083_, 0);
                    lean_inc_n(v_head_2088_, 2);
                    v_tail_2089_ = lean_ctor_get(v_x_2083_, 1);
                    lean_inc(v_tail_2089_);
                    lean_dec_ref_known(v_x_2083_, 2);
                    v___f_2090_ = lean_alloc_closure(l_List_filterAuxM___at___00Std_Queue_filterM___at___00Std_CancellationToken_selector_spec__2_spec__2___redArg___lam__0___boxed as *mut core::ffi::c_void, 5, 3);
                    lean_closure_set(v___f_2090_, 0, v_tail_2089_);
                    lean_closure_set(v___f_2090_, 1, v_x_2084_);
                    lean_closure_set(v___f_2090_, 2, v_head_2088_);
                    if lean_obj_tag(v_head_2088_) == 0 {
                        lean_dec_ref_known(v_head_2088_, 1);
                        v___x_2096_ = l_List_filterAuxM___at___00Std_Queue_filterM___at___00Std_CancellationToken_selector_spec__2_spec__2___redArg___closed__1;
                        v_val_2092_ = v___x_2096_;
                        state = 1;
                        continue;
                    } else {
                        v_finished_2097_ = lean_ctor_get(v_head_2088_, 0);
                        v_isSharedCheck_2111_ = (!lean_is_exclusive(v_head_2088_)) as u8;
                        if v_isSharedCheck_2111_ == 0 {
                            v___x_2099_ = v_head_2088_;
                            v_isShared_2100_ = v_isSharedCheck_2111_;
                            state = 2;
                            continue;
                        } else {
                            lean_inc(v_finished_2097_);
                            lean_dec(v_head_2088_);
                            v___x_2099_ = lean_box(0);
                            v_isShared_2100_ = v_isSharedCheck_2111_;
                            state = 2;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v___x_2093_ = lean_unsigned_to_nat(0);
                v___x_2094_ = 0;
                v___x_2095_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(
                    lean_box(0),
                    lean_box(0),
                    v___x_2093_,
                    v___x_2094_,
                    v_val_2092_,
                    v___f_2090_,
                );
                return v___x_2095_;
            }
            2 => {
                v_finished_2101_ = lean_ctor_get(v_finished_2097_, 0);
                lean_inc(v_finished_2101_);
                lean_dec_ref(v_finished_2097_);
                v___x_2102_ = lean_st_ref_get(v_finished_2101_);
                lean_dec(v_finished_2101_);
                v___f_2103_ = l_List_filterAuxM___at___00Std_Queue_filterM___at___00Std_CancellationToken_selector_spec__2_spec__2___redArg___closed__2;
                if v_isShared_2100_ == 0 {
                    lean_ctor_set(v___x_2099_, 0, v___x_2102_);
                    v___x_2105_ = v___x_2099_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_2110_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2110_, 0, v___x_2102_);
                    v___x_2105_ = v_reuseFailAlloc_2110_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_2106_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_2106_, 0, v___x_2105_);
                v___x_2107_ = lean_unsigned_to_nat(0);
                v___x_2108_ = 0;
                v___x_2109_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(
                    lean_box(0),
                    lean_box(0),
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
    mut v_tail_2112_: *mut LeanObject,
    mut v_x_2113_: *mut LeanObject,
    mut v_head_2114_: *mut LeanObject,
    mut v_x_2115_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_2117_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2119_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2120_: u8 = 0;
    let mut v___x_2122_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2123_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2124_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2125_: u8 = 0;
    let mut v_a_2126_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2127_: u8 = 0;
    let mut v___x_2128_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2129_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2130_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_2115_) == 0 {
                    lean_dec_ref(v_head_2114_);
                    lean_dec(v_x_2113_);
                    lean_dec(v_tail_2112_);
                    v_a_2117_ = lean_ctor_get(v_x_2115_, 0);
                    v_isSharedCheck_2125_ = (!lean_is_exclusive(v_x_2115_)) as u8;
                    if v_isSharedCheck_2125_ == 0 {
                        v___x_2119_ = v_x_2115_;
                        v_isShared_2120_ = v_isSharedCheck_2125_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_2117_);
                        lean_dec(v_x_2115_);
                        v___x_2119_ = lean_box(0);
                        v_isShared_2120_ = v_isSharedCheck_2125_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_2126_ = lean_ctor_get(v_x_2115_, 0);
                    lean_inc(v_a_2126_);
                    lean_dec_ref_known(v_x_2115_, 1);
                    v___x_2127_ = (lean_unbox(v_a_2126_) as u8);
                    lean_dec(v_a_2126_);
                    if v___x_2127_ == 0 {
                        lean_dec_ref(v_head_2114_);
                        v___x_2128_ = l_List_filterAuxM___at___00Std_Queue_filterM___at___00Std_CancellationToken_selector_spec__2_spec__2___redArg(v_tail_2112_, v_x_2113_);
                        return v___x_2128_;
                    } else {
                        v___x_2129_ = lean_alloc_ctor(1, 2, (0) as u32);
                        lean_ctor_set(v___x_2129_, 0, v_head_2114_);
                        lean_ctor_set(v___x_2129_, 1, v_x_2113_);
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
                    v_reuseFailAlloc_2124_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2124_, 0, v_a_2117_);
                    v___x_2122_ = v_reuseFailAlloc_2124_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_2123_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_2123_, 0, v___x_2122_);
                return v___x_2123_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_filterAuxM___at___00Std_Queue_filterM___at___00Std_CancellationToken_selector_spec__2_spec__2___redArg___boxed(
    mut v_x_2131_: *mut LeanObject,
    mut v_x_2132_: *mut LeanObject,
    mut v___y_2133_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2134_: *mut LeanObject = core::ptr::null_mut();
    v_res_2134_ = l_List_filterAuxM___at___00Std_Queue_filterM___at___00Std_CancellationToken_selector_spec__2_spec__2___redArg(v_x_2131_, v_x_2132_);
    return v_res_2134_;
}
pub unsafe fn l_Std_Queue_filterM___at___00Std_CancellationToken_selector_spec__2___lam__1(
    mut v_eList_2135_: *mut LeanObject,
    mut v___x_2136_: *mut LeanObject,
    mut v___f_2137_: *mut LeanObject,
    mut v_x_2138_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_2140_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2142_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2143_: u8 = 0;
    let mut v___x_2145_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2146_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2147_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2148_: u8 = 0;
    let mut v_a_2149_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2150_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2151_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2152_: u8 = 0;
    let mut v___x_2153_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2154_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2155_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_2138_) == 0 {
                    lean_dec_ref(v___f_2137_);
                    lean_dec(v___x_2136_);
                    lean_dec(v_eList_2135_);
                    v_a_2140_ = lean_ctor_get(v_x_2138_, 0);
                    v_isSharedCheck_2148_ = (!lean_is_exclusive(v_x_2138_)) as u8;
                    if v_isSharedCheck_2148_ == 0 {
                        v___x_2142_ = v_x_2138_;
                        v_isShared_2143_ = v_isSharedCheck_2148_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_2140_);
                        lean_dec(v_x_2138_);
                        v___x_2142_ = lean_box(0);
                        v_isShared_2143_ = v_isSharedCheck_2148_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_2149_ = lean_ctor_get(v_x_2138_, 0);
                    lean_inc(v_a_2149_);
                    lean_dec_ref_known(v_x_2138_, 1);
                    lean_inc(v___x_2136_);
                    v___x_2150_ = l_List_filterAuxM___at___00Std_Queue_filterM___at___00Std_CancellationToken_selector_spec__2_spec__2___redArg(v_eList_2135_, v___x_2136_);
                    v___x_2151_ = lean_unsigned_to_nat(0);
                    v___x_2152_ = 0;
                    v___x_2153_ =
                        l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(
                            lean_box(0),
                            lean_box(0),
                            v___x_2151_,
                            v___x_2152_,
                            v___x_2150_,
                            v___f_2137_,
                        );
                    v___f_2154_ = lean_alloc_closure(l_Std_Queue_filterM___at___00Std_CancellationToken_selector_spec__2___lam__2___boxed as *mut core::ffi::c_void, 4, 2);
                    lean_closure_set(v___f_2154_, 0, v_a_2149_);
                    lean_closure_set(v___f_2154_, 1, v___x_2136_);
                    v___x_2155_ =
                        l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(
                            lean_box(0),
                            lean_box(0),
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
                    v_reuseFailAlloc_2147_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2147_, 0, v_a_2140_);
                    v___x_2145_ = v_reuseFailAlloc_2147_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_2146_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_2146_, 0, v___x_2145_);
                return v___x_2146_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Queue_filterM___at___00Std_CancellationToken_selector_spec__2___lam__1___boxed(
    mut v_eList_2156_: *mut LeanObject,
    mut v___x_2157_: *mut LeanObject,
    mut v___f_2158_: *mut LeanObject,
    mut v_x_2159_: *mut LeanObject,
    mut v___y_2160_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2161_: *mut LeanObject = core::ptr::null_mut();
    v_res_2161_ = l_Std_Queue_filterM___at___00Std_CancellationToken_selector_spec__2___lam__1(
        v_eList_2156_,
        v___x_2157_,
        v___f_2158_,
        v_x_2159_,
    );
    return v_res_2161_;
}
pub unsafe fn l_Std_Queue_filterM___at___00Std_CancellationToken_selector_spec__2(
    mut v_q_2163_: *mut LeanObject,
    mut v___y_2164_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_eList_2166_: *mut LeanObject = core::ptr::null_mut();
    let mut v_dList_2167_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2168_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2169_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2170_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2171_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2172_: u8 = 0;
    let mut v___x_2173_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2174_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2175_: *mut LeanObject = core::ptr::null_mut();
    v_eList_2166_ = lean_ctor_get(v_q_2163_, 0);
    lean_inc(v_eList_2166_);
    v_dList_2167_ = lean_ctor_get(v_q_2163_, 1);
    lean_inc(v_dList_2167_);
    lean_dec_ref(v_q_2163_);
    v___x_2168_ = lean_box(0);
    v___x_2169_ = l_List_filterAuxM___at___00Std_Queue_filterM___at___00Std_CancellationToken_selector_spec__2_spec__2___redArg(v_dList_2167_, v___x_2168_);
    v___f_2170_ = l_Std_Queue_filterM___at___00Std_CancellationToken_selector_spec__2___closed__0;
    v___x_2171_ = lean_unsigned_to_nat(0);
    v___x_2172_ = 0;
    v___x_2173_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(
        lean_box(0),
        lean_box(0),
        v___x_2171_,
        v___x_2172_,
        v___x_2169_,
        v___f_2170_,
    );
    v___f_2174_ = lean_alloc_closure(
        l_Std_Queue_filterM___at___00Std_CancellationToken_selector_spec__2___lam__1___boxed
            as *mut core::ffi::c_void,
        5,
        3,
    );
    lean_closure_set(v___f_2174_, 0, v_eList_2166_);
    lean_closure_set(v___f_2174_, 1, v___x_2168_);
    lean_closure_set(v___f_2174_, 2, v___f_2170_);
    v___x_2175_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(
        lean_box(0),
        lean_box(0),
        v___x_2171_,
        v___x_2172_,
        v___x_2173_,
        v___f_2174_,
    );
    return v___x_2175_;
}
pub unsafe fn l_Std_Queue_filterM___at___00Std_CancellationToken_selector_spec__2___boxed(
    mut v_q_2176_: *mut LeanObject,
    mut v___y_2177_: *mut LeanObject,
    mut v___y_2178_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2179_: *mut LeanObject = core::ptr::null_mut();
    v_res_2179_ =
        l_Std_Queue_filterM___at___00Std_CancellationToken_selector_spec__2(v_q_2176_, v___y_2177_);
    lean_dec(v___y_2177_);
    return v_res_2179_;
}
pub unsafe fn l_Std_CancellationToken_selector___lam__8(
    mut v___y_2180_: *mut LeanObject,
    mut v_x_2181_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_2183_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2185_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2186_: u8 = 0;
    let mut v___x_2188_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2189_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2190_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2191_: u8 = 0;
    let mut v_a_2192_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reason_2193_: *mut LeanObject = core::ptr::null_mut();
    let mut v_consumers_2194_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2195_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2196_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2197_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2198_: u8 = 0;
    let mut v___x_2199_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_2181_) == 0 {
                    v_a_2183_ = lean_ctor_get(v_x_2181_, 0);
                    v_isSharedCheck_2191_ = (!lean_is_exclusive(v_x_2181_)) as u8;
                    if v_isSharedCheck_2191_ == 0 {
                        v___x_2185_ = v_x_2181_;
                        v_isShared_2186_ = v_isSharedCheck_2191_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_2183_);
                        lean_dec(v_x_2181_);
                        v___x_2185_ = lean_box(0);
                        v_isShared_2186_ = v_isSharedCheck_2191_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_2192_ = lean_ctor_get(v_x_2181_, 0);
                    lean_inc(v_a_2192_);
                    lean_dec_ref_known(v_x_2181_, 1);
                    v_reason_2193_ = lean_ctor_get(v_a_2192_, 0);
                    lean_inc(v_reason_2193_);
                    v_consumers_2194_ = lean_ctor_get(v_a_2192_, 1);
                    lean_inc_ref(v_consumers_2194_);
                    lean_dec(v_a_2192_);
                    v___x_2195_ =
                        l_Std_Queue_filterM___at___00Std_CancellationToken_selector_spec__2(
                            v_consumers_2194_,
                            v___y_2180_,
                        );
                    lean_inc(v___y_2180_);
                    v___f_2196_ = lean_alloc_closure(
                        l_Std_CancellationToken_selector___lam__7___boxed as *mut core::ffi::c_void,
                        4,
                        2,
                    );
                    lean_closure_set(v___f_2196_, 0, v_reason_2193_);
                    lean_closure_set(v___f_2196_, 1, v___y_2180_);
                    v___x_2197_ = lean_unsigned_to_nat(0);
                    v___x_2198_ = 0;
                    v___x_2199_ =
                        l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(
                            lean_box(0),
                            lean_box(0),
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
                    v_reuseFailAlloc_2190_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2190_, 0, v_a_2183_);
                    v___x_2188_ = v_reuseFailAlloc_2190_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_2189_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_2189_, 0, v___x_2188_);
                return v___x_2189_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_CancellationToken_selector___lam__8___boxed(
    mut v___y_2200_: *mut LeanObject,
    mut v_x_2201_: *mut LeanObject,
    mut v___y_2202_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2203_: *mut LeanObject = core::ptr::null_mut();
    v_res_2203_ = l_Std_CancellationToken_selector___lam__8(v___y_2200_, v_x_2201_);
    lean_dec(v___y_2200_);
    return v_res_2203_;
}
pub unsafe fn l_Std_CancellationToken_selector___lam__9(
    mut v___y_2204_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2206_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2207_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2208_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2209_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2210_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2211_: u8 = 0;
    let mut v___x_2212_: *mut LeanObject = core::ptr::null_mut();
    v___x_2206_ = lean_st_ref_get(v___y_2204_);
    lean_inc(v___y_2204_);
    v___f_2207_ = lean_alloc_closure(
        l_Std_CancellationToken_selector___lam__8___boxed as *mut core::ffi::c_void,
        3,
        1,
    );
    lean_closure_set(v___f_2207_, 0, v___y_2204_);
    v___x_2208_ = lean_alloc_ctor(1, 1, (0) as u32);
    lean_ctor_set(v___x_2208_, 0, v___x_2206_);
    v___x_2209_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_2209_, 0, v___x_2208_);
    v___x_2210_ = lean_unsigned_to_nat(0);
    v___x_2211_ = 0;
    v___x_2212_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(
        lean_box(0),
        lean_box(0),
        v___x_2210_,
        v___x_2211_,
        v___x_2209_,
        v___f_2207_,
    );
    return v___x_2212_;
}
pub unsafe fn l_Std_CancellationToken_selector___lam__9___boxed(
    mut v___y_2213_: *mut LeanObject,
    mut v___y_2214_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2215_: *mut LeanObject = core::ptr::null_mut();
    v_res_2215_ = l_Std_CancellationToken_selector___lam__9(v___y_2213_);
    lean_dec(v___y_2213_);
    return v_res_2215_;
}
pub unsafe fn l_Std_CancellationToken_selector(
    mut v_token_2218_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_2219_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2220_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2221_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2222_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2223_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2224_: *mut LeanObject = core::ptr::null_mut();
    lean_inc_ref_n(v_token_2218_, 2);
    v___f_2219_ = lean_alloc_closure(
        l_Std_CancellationToken_selector___lam__4___boxed as *mut core::ffi::c_void,
        3,
        1,
    );
    lean_closure_set(v___f_2219_, 0, v_token_2218_);
    v___f_2220_ = l_Std_CancellationToken_selector___closed__0;
    v___f_2221_ = lean_alloc_closure(
        l_Std_CancellationToken_selector___lam__6___boxed as *mut core::ffi::c_void,
        3,
        2,
    );
    lean_closure_set(v___f_2221_, 0, v_token_2218_);
    lean_closure_set(v___f_2221_, 1, v___f_2220_);
    v___f_2222_ = l_Std_CancellationToken_selector___closed__1;
    v___x_2223_ = lean_alloc_closure(
        l_Std_Mutex_atomically___at___00Std_CancellationToken_selector_spec__1___boxed
            as *mut core::ffi::c_void,
        5,
        4,
    );
    lean_closure_set(v___x_2223_, 0, lean_box(0));
    lean_closure_set(v___x_2223_, 1, lean_box(0));
    lean_closure_set(v___x_2223_, 2, v_token_2218_);
    lean_closure_set(v___x_2223_, 3, v___f_2222_);
    v___x_2224_ = lean_alloc_ctor(0, 3, (0) as u32);
    lean_ctor_set(v___x_2224_, 0, v___f_2221_);
    lean_ctor_set(v___x_2224_, 1, v___f_2219_);
    lean_ctor_set(v___x_2224_, 2, v___x_2223_);
    return v___x_2224_;
}
pub unsafe fn l_List_filterAuxM___at___00Std_Queue_filterM___at___00Std_CancellationToken_selector_spec__2_spec__2(
    mut v_x_2225_: *mut LeanObject,
    mut v_x_2226_: *mut LeanObject,
    mut v___y_2227_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2229_: *mut LeanObject = core::ptr::null_mut();
    v___x_2229_ = l_List_filterAuxM___at___00Std_Queue_filterM___at___00Std_CancellationToken_selector_spec__2_spec__2___redArg(v_x_2225_, v_x_2226_);
    return v___x_2229_;
}
pub unsafe fn l_List_filterAuxM___at___00Std_Queue_filterM___at___00Std_CancellationToken_selector_spec__2_spec__2___boxed(
    mut v_x_2230_: *mut LeanObject,
    mut v_x_2231_: *mut LeanObject,
    mut v___y_2232_: *mut LeanObject,
    mut v___y_2233_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2234_: *mut LeanObject = core::ptr::null_mut();
    v_res_2234_ = l_List_filterAuxM___at___00Std_Queue_filterM___at___00Std_CancellationToken_selector_spec__2_spec__2(v_x_2230_, v_x_2231_, v___y_2232_);
    lean_dec(v___y_2232_);
    return v_res_2234_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Std_Sync_CancellationToken(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Std_Data(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
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
    res = runtime_initialize_Init_Data_ToString_Macro(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Std_Sync_CancellationToken(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_meta_initialized = true;
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Std_Sync_CancellationToken(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Std_Data(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
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
    res = initialize_Init_Data_ToString_Macro(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Std_Sync_CancellationToken(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Std_Sync_CancellationToken(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Std_Sync_CancellationToken(builtin);
}
