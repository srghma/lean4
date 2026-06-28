// Lean compiler output
// Module: Std.Sync.Channel
// Imports: Init.Data.Queue Std.Sync.Mutex Std.Async.IO Init.Data.Vector.Basic Init.Data.Option.BasicAux Init.Omega
use crate::r#gen::Init::Control::Except::l_Except_mapError;
use crate::r#gen::Init::Data::Array::Basic::{
    l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold, l_Array_range,
};
use crate::r#gen::Init::Data::List::Basic::{l_List_isEmpty___redArg, l_List_reverse___redArg};
use crate::r#gen::Init::Data::Option::BasicAux::{
    initialize_Init_Data_Option_BasicAux, runtime_initialize_Init_Data_Option_BasicAux,
};
use crate::r#gen::Init::Data::Queue::{
    initialize_Init_Data_Queue, l_Std_Queue_dequeue_x3f___redArg, l_Std_Queue_empty,
    l_Std_Queue_enqueue___redArg, l_Std_Queue_isEmpty___redArg, l_Std_Queue_toArray___redArg,
    runtime_initialize_Init_Data_Queue,
};
use crate::r#gen::Init::Data::Repr::l_Repr_addAppParen;
use crate::r#gen::Init::Data::Vector::Basic::{
    initialize_Init_Data_Vector_Basic, runtime_initialize_Init_Data_Vector_Basic,
};
use crate::r#gen::Init::Omega::{initialize_Init_Omega, runtime_initialize_Init_Omega};
use crate::r#gen::Init::Prelude::{
    l_Function_comp, l_instInhabitedOfMonad___redArg, l_panic___redArg,
};
use crate::r#gen::Init::System::IO::{l_EIO_chainTask___redArg, l_instMonadBaseIO};
use crate::r#gen::Init::System::IOError::lean_mk_io_user_error;
use crate::r#gen::Init::System::Promise::l_IO_Promise_resolve___boxed;
use crate::r#gen::Init::System::ST::{
    l_ST_Prim_Ref_get___boxed, l_ST_Prim_Ref_set___boxed, l_ST_Prim_Ref_swap___boxed,
};
use crate::r#gen::Init::Util::l_mkPanicMessageWithDecl;
use crate::r#gen::Std::Async::Basic::{
    l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask,
    l_Std_Async_EAsync_instMonad, l_Std_Async_EAsync_tryFinally_x27___redArg,
};
use crate::r#gen::Std::Async::IO::{initialize_Std_Async_IO, runtime_initialize_Std_Async_IO};
use crate::r#gen::Std::Sync::Mutex::{
    initialize_Std_Sync_Mutex, l_Std_Mutex_new___redArg, runtime_initialize_Std_Sync_Mutex,
};
use crate::lean_imports_rs::Init::Core::{lean_task_map, lean_task_pure};
use crate::lean_imports_rs::Init::Data::Array::Basic::{lean_array_size, lean_array_uget_borrowed};
use crate::lean_imports_rs::Init::Data::Int::Basic::lean_nat_to_int;
use crate::lean_imports_rs::Init::Data::UInt::BasicAux::{
    lean_usize_add, lean_usize_dec_lt, lean_usize_of_nat,
};
use crate::lean_imports_rs::Init::Prelude::{
    lean_array_fget, lean_array_fget_borrowed, lean_array_get_size, lean_array_push,
    lean_mk_empty_array_with_capacity, lean_nat_add, lean_nat_dec_eq, lean_nat_dec_le,
    lean_nat_dec_lt, lean_nat_sub, lean_panic_fn_borrowed,
};
use crate::lean_imports_rs::Init::System::IO::{lean_io_bind_task, lean_io_wait};
use crate::lean_imports_rs::Init::System::Promise::{
    lean_io_promise_new, lean_io_promise_resolve, lean_io_promise_result_opt,
};
use crate::lean_imports_rs::Init::System::ST::{
    lean_st_mk_ref, lean_st_ref_get, lean_st_ref_set, lean_st_ref_swap, lean_st_ref_take,
};
use crate::lean_imports_rs::Std::Sync::Mutex::{lean_io_basemutex_lock, lean_io_basemutex_unlock};
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_alloc_closure, lean_alloc_ctor, lean_apply_1,
    lean_apply_2, lean_apply_3, lean_apply_4, lean_box, lean_box_uint64, lean_closure_set,
    lean_ctor_get, lean_ctor_get_uint8, lean_ctor_set, lean_ctor_set_tag, lean_ctor_set_uint8,
    lean_dec, lean_dec_ref, lean_dec_ref_known, lean_del_object, lean_inc, lean_inc_n,
    lean_inc_ref, lean_inc_ref_n, lean_io_result_is_error, lean_io_result_mk_ok, lean_is_exclusive,
    lean_obj_once, lean_obj_tag, lean_unbox, lean_unbox_usize, lean_unsigned_to_nat,
};
pub static l_Std_CloseableChannel_instReprError_repr___closed__0_value: LeanStringObject<34> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 34,
        m_capacity: 34,
        m_length: 33,
        m_data: [
            83, 116, 100, 46, 67, 108, 111, 115, 101, 97, 98, 108, 101, 67, 104, 97, 110, 110, 101,
            108, 46, 69, 114, 114, 111, 114, 46, 99, 108, 111, 115, 101, 100, 0,
        ],
    };
static mut l_Std_CloseableChannel_instReprError_repr___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Std_CloseableChannel_instReprError_repr___closed__0_value)
        as *mut LeanObject;
pub static l_Std_CloseableChannel_instReprError_repr___closed__1_value: LeanCtorObject<1> =
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
            core::ptr::addr_of!(l_Std_CloseableChannel_instReprError_repr___closed__0_value)
                as *mut LeanObject,
        ],
    };
static mut l_Std_CloseableChannel_instReprError_repr___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Std_CloseableChannel_instReprError_repr___closed__1_value)
        as *mut LeanObject;
pub static l_Std_CloseableChannel_instReprError_repr___closed__2_value: LeanStringObject<41> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 41,
        m_capacity: 41,
        m_length: 40,
        m_data: [
            83, 116, 100, 46, 67, 108, 111, 115, 101, 97, 98, 108, 101, 67, 104, 97, 110, 110, 101,
            108, 46, 69, 114, 114, 111, 114, 46, 97, 108, 114, 101, 97, 100, 121, 67, 108, 111,
            115, 101, 100, 0,
        ],
    };
static mut l_Std_CloseableChannel_instReprError_repr___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Std_CloseableChannel_instReprError_repr___closed__2_value)
        as *mut LeanObject;
pub static l_Std_CloseableChannel_instReprError_repr___closed__3_value: LeanCtorObject<1> =
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
            core::ptr::addr_of!(l_Std_CloseableChannel_instReprError_repr___closed__2_value)
                as *mut LeanObject,
        ],
    };
static mut l_Std_CloseableChannel_instReprError_repr___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Std_CloseableChannel_instReprError_repr___closed__3_value)
        as *mut LeanObject;
static mut l_Std_CloseableChannel_instReprError_repr___closed__4_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_CloseableChannel_instReprError_repr___closed__4: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Std_CloseableChannel_instReprError_repr___closed__5_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_CloseableChannel_instReprError_repr___closed__5: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Std_CloseableChannel_instReprError___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_Std_CloseableChannel_instReprError_repr___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Std_CloseableChannel_instReprError___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Std_CloseableChannel_instReprError___closed__0_value) as *mut LeanObject;
pub static mut l_Std_CloseableChannel_instReprError: *mut LeanObject =
    core::ptr::addr_of!(l_Std_CloseableChannel_instReprError___closed__0_value) as *mut LeanObject;
pub static l_Std_CloseableChannel_instHashableError___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_Std_CloseableChannel_instHashableError_hash___boxed as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Std_CloseableChannel_instHashableError___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Std_CloseableChannel_instHashableError___closed__0_value)
        as *mut LeanObject;
pub static mut l_Std_CloseableChannel_instHashableError: *mut LeanObject =
    core::ptr::addr_of!(l_Std_CloseableChannel_instHashableError___closed__0_value)
        as *mut LeanObject;
pub static l_Std_CloseableChannel_instToStringError___lam__0___closed__0_value: LeanStringObject<
    44,
> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 44,
    m_capacity: 44,
    m_length: 43,
    m_data: [
        116, 114, 121, 105, 110, 103, 32, 116, 111, 32, 115, 101, 110, 100, 32, 111, 110, 32, 97,
        110, 32, 97, 108, 114, 101, 97, 100, 121, 32, 99, 108, 111, 115, 101, 100, 32, 99, 104, 97,
        110, 110, 101, 108, 0,
    ],
};
static mut l_Std_CloseableChannel_instToStringError___lam__0___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Std_CloseableChannel_instToStringError___lam__0___closed__0_value)
        as *mut LeanObject;
pub static l_Std_CloseableChannel_instToStringError___lam__0___closed__1_value: LeanStringObject<
    42,
> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 42,
    m_capacity: 42,
    m_length: 41,
    m_data: [
        116, 114, 121, 105, 110, 103, 32, 116, 111, 32, 99, 108, 111, 115, 101, 32, 97, 110, 32,
        97, 108, 114, 101, 97, 100, 121, 32, 99, 108, 111, 115, 101, 100, 32, 99, 104, 97, 110,
        110, 101, 108, 0,
    ],
};
static mut l_Std_CloseableChannel_instToStringError___lam__0___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Std_CloseableChannel_instToStringError___lam__0___closed__1_value)
        as *mut LeanObject;
pub static l_Std_CloseableChannel_instToStringError___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_Std_CloseableChannel_instToStringError___lam__0___boxed
            as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Std_CloseableChannel_instToStringError___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Std_CloseableChannel_instToStringError___closed__0_value)
        as *mut LeanObject;
pub static mut l_Std_CloseableChannel_instToStringError: *mut LeanObject =
    core::ptr::addr_of!(l_Std_CloseableChannel_instToStringError___closed__0_value)
        as *mut LeanObject;
pub static l_Std_CloseableChannel_instMonadLiftEIOErrorIO___lam__0___closed__0_value:
    LeanCtorObject<1> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 18,
    },
    m_objs: [core::ptr::addr_of!(
        l_Std_CloseableChannel_instToStringError___lam__0___closed__0_value
    ) as *mut LeanObject],
};
static mut l_Std_CloseableChannel_instMonadLiftEIOErrorIO___lam__0___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Std_CloseableChannel_instMonadLiftEIOErrorIO___lam__0___closed__0_value)
        as *mut LeanObject;
pub static l_Std_CloseableChannel_instMonadLiftEIOErrorIO___lam__0___closed__1_value:
    LeanCtorObject<1> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 18,
    },
    m_objs: [core::ptr::addr_of!(
        l_Std_CloseableChannel_instToStringError___lam__0___closed__1_value
    ) as *mut LeanObject],
};
static mut l_Std_CloseableChannel_instMonadLiftEIOErrorIO___lam__0___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Std_CloseableChannel_instMonadLiftEIOErrorIO___lam__0___closed__1_value)
        as *mut LeanObject;
pub static l_Std_CloseableChannel_instMonadLiftEIOErrorIO___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_Std_CloseableChannel_instMonadLiftEIOErrorIO___lam__0___boxed
            as *const core::ffi::c_void,
        m_arity: 3,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Std_CloseableChannel_instMonadLiftEIOErrorIO___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Std_CloseableChannel_instMonadLiftEIOErrorIO___closed__0_value)
        as *mut LeanObject;
pub static mut l_Std_CloseableChannel_instMonadLiftEIOErrorIO: *mut LeanObject =
    core::ptr::addr_of!(l_Std_CloseableChannel_instMonadLiftEIOErrorIO___closed__0_value)
        as *mut LeanObject;
pub static l___private_Std_Sync_Channel_0__Std_CloseableChannel_Consumer_resolve___redArg___closed__0_value: LeanClosureObject<1> = LeanClosureObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut LeanObject>()*1) as u16, other: 0, tag: 245 }, m_fun: l___private_Std_Sync_Channel_0__Std_CloseableChannel_Consumer_resolve___redArg___lam__0___boxed as *const core::ffi::c_void, m_arity: 2, m_num_fixed: 1, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Std_Sync_Channel_0__Std_CloseableChannel_Consumer_resolve___redArg___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Consumer_resolve___redArg___closed__0_value) as *mut LeanObject;
static mut l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_new___redArg___closed__0_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_new___redArg___closed__0: *mut LeanObject = core::ptr::null_mut();
static mut l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_new___redArg___closed__1_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_new___redArg___closed__1: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_send___redArg___closed__0_value: LeanCtorObject<1> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*1 + 0) as u16, other: 1, tag: 0 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_send___redArg___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_send___redArg___closed__0_value) as *mut LeanObject;
static mut l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_send___redArg___closed__1_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_send___redArg___closed__1: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_send___redArg___closed__2_value: LeanCtorObject<1> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*1 + 0) as u16, other: 1, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_send___redArg___closed__2: *mut LeanObject = core::ptr::addr_of!(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_send___redArg___closed__2_value) as *mut LeanObject;
static mut l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_send___redArg___closed__3_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_send___redArg___closed__3: *mut LeanObject = core::ptr::null_mut();
static mut l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_close___redArg___lam__0___closed__0_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_close___redArg___lam__0___closed__0: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_close___redArg___closed__0_value: LeanClosureObject<0> = LeanClosureObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_close___redArg___lam__0___boxed as *const core::ffi::c_void, m_arity: 2, m_num_fixed: 0, m_objs: [] };
static mut l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_close___redArg___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_close___redArg___closed__0_value) as *mut LeanObject;
pub static l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_isClosed___redArg___closed__0_value: LeanClosureObject<0> = LeanClosureObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_isClosed___redArg___lam__0___boxed as *const core::ffi::c_void, m_arity: 2, m_num_fixed: 0, m_objs: [] };
static mut l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_isClosed___redArg___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_isClosed___redArg___closed__0_value) as *mut LeanObject;
pub static l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_tryRecv___redArg___closed__0_value: LeanClosureObject<0> = LeanClosureObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_tryRecv_spec__0___redArg___boxed as *const core::ffi::c_void, m_arity: 2, m_num_fixed: 0, m_objs: [] };
static mut l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_tryRecv___redArg___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_tryRecv___redArg___closed__0_value) as *mut LeanObject;
static mut l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recv___redArg___lam__1___closed__0_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recv___redArg___lam__1___closed__0: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recv___redArg___closed__0_value: LeanClosureObject<0> = LeanClosureObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recv___redArg___lam__0___boxed as *const core::ffi::c_void, m_arity: 1, m_num_fixed: 0, m_objs: [] };
static mut l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recv___redArg___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recv___redArg___closed__0_value) as *mut LeanObject;
pub static l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recv___redArg___closed__1_value: LeanClosureObject<1> = LeanClosureObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut LeanObject>()*1) as u16, other: 0, tag: 245 }, m_fun: l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recv___redArg___lam__1___boxed as *const core::ffi::c_void, m_arity: 3, m_num_fixed: 1, m_objs: [core::ptr::addr_of!(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recv___redArg___closed__0_value) as *mut LeanObject] };
static mut l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recv___redArg___closed__1: *mut LeanObject = core::ptr::addr_of!(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recv___redArg___closed__1_value) as *mut LeanObject;
pub static l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__0___redArg___lam__1___closed__0_value: LeanCtorObject<1> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*1 + 0) as u16, other: 1, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__0___redArg___lam__1___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__0___redArg___lam__1___closed__0_value) as *mut LeanObject;
pub static l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__0___redArg___lam__1___closed__1_value: LeanCtorObject<1> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*1 + 0) as u16, other: 1, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__0___redArg___lam__1___closed__0_value) as *mut LeanObject] };
static mut l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__0___redArg___lam__1___closed__1: *mut LeanObject = core::ptr::addr_of!(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__0___redArg___lam__1___closed__1_value) as *mut LeanObject;
pub static l_Std_Mutex_atomically___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__2___redArg___closed__0_value: LeanClosureObject<0> = LeanClosureObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Std_Mutex_atomically___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__2___redArg___lam__3 as *const core::ffi::c_void, m_arity: 1, m_num_fixed: 0, m_objs: [] };
static mut l_Std_Mutex_atomically___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__2___redArg___closed__0: *mut LeanObject = core::ptr::addr_of!(l_Std_Mutex_atomically___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__2___redArg___closed__0_value) as *mut LeanObject;
pub static l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector___redArg___lam__3___closed__0_value: LeanCtorObject<1> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*1 + 0) as u16, other: 1, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector___redArg___lam__3___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector___redArg___lam__3___closed__0_value) as *mut LeanObject;
pub static l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector___redArg___lam__3___closed__1_value: LeanCtorObject<1> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*1 + 0) as u16, other: 1, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector___redArg___lam__3___closed__0_value) as *mut LeanObject] };
static mut l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector___redArg___lam__3___closed__1: *mut LeanObject = core::ptr::addr_of!(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector___redArg___lam__3___closed__1_value) as *mut LeanObject;
pub static l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector___redArg___lam__3___closed__2_value: LeanClosureObject<1> = LeanClosureObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut LeanObject>()*1) as u16, other: 0, tag: 245 }, m_fun: l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector___redArg___lam__2___boxed as *const core::ffi::c_void, m_arity: 3, m_num_fixed: 1, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector___redArg___lam__3___closed__2: *mut LeanObject = core::ptr::addr_of!(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector___redArg___lam__3___closed__2_value) as *mut LeanObject;
pub static l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector___redArg___lam__7___closed__0_value: LeanCtorObject<1> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*1 + 0) as u16, other: 1, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector___redArg___lam__7___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector___redArg___lam__7___closed__0_value) as *mut LeanObject;
pub static l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector___redArg___lam__7___closed__1_value: LeanCtorObject<1> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*1 + 0) as u16, other: 1, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector___redArg___lam__7___closed__0_value) as *mut LeanObject] };
static mut l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector___redArg___lam__7___closed__1: *mut LeanObject = core::ptr::addr_of!(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector___redArg___lam__7___closed__1_value) as *mut LeanObject;
pub static l_List_filterAuxM___at___00Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__3_spec__3___redArg___closed__0_value: LeanCtorObject<1> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*1 + 0) as u16, other: 1, tag: 1 }, m_objs: [((( 1 as usize) << 1) | 1) as *mut LeanObject] };
static mut l_List_filterAuxM___at___00Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__3_spec__3___redArg___closed__0: *mut LeanObject = core::ptr::addr_of!(l_List_filterAuxM___at___00Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__3_spec__3___redArg___closed__0_value) as *mut LeanObject;
pub static l_List_filterAuxM___at___00Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__3_spec__3___redArg___closed__1_value: LeanCtorObject<1> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*1 + 0) as u16, other: 1, tag: 0 }, m_objs: [core::ptr::addr_of!(l_List_filterAuxM___at___00Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__3_spec__3___redArg___closed__0_value) as *mut LeanObject] };
static mut l_List_filterAuxM___at___00Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__3_spec__3___redArg___closed__1: *mut LeanObject = core::ptr::addr_of!(l_List_filterAuxM___at___00Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__3_spec__3___redArg___closed__1_value) as *mut LeanObject;
pub static l_List_filterAuxM___at___00Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__3_spec__3___redArg___closed__2_value: LeanClosureObject<0> = LeanClosureObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_List_filterAuxM___at___00Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__3_spec__3___redArg___lam__1___boxed as *const core::ffi::c_void, m_arity: 2, m_num_fixed: 0, m_objs: [] };
static mut l_List_filterAuxM___at___00Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__3_spec__3___redArg___closed__2: *mut LeanObject = core::ptr::addr_of!(l_List_filterAuxM___at___00Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__3_spec__3___redArg___closed__2_value) as *mut LeanObject;
pub static l_Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__3___redArg___closed__0_value: LeanClosureObject<0> = LeanClosureObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__3___redArg___lam__0___boxed as *const core::ffi::c_void, m_arity: 2, m_num_fixed: 0, m_objs: [] };
static mut l_Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__3___redArg___closed__0: *mut LeanObject = core::ptr::addr_of!(l_Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__3___redArg___closed__0_value) as *mut LeanObject;
pub static l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector___redArg___closed__0_value: LeanClosureObject<0> = LeanClosureObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector___redArg___lam__0___boxed as *const core::ffi::c_void, m_arity: 2, m_num_fixed: 0, m_objs: [] };
static mut l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector___redArg___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector___redArg___closed__0_value) as *mut LeanObject;
pub static l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector___redArg___closed__1_value: LeanClosureObject<0> = LeanClosureObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector___redArg___lam__1___boxed as *const core::ffi::c_void, m_arity: 2, m_num_fixed: 0, m_objs: [] };
static mut l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector___redArg___closed__1: *mut LeanObject = core::ptr::addr_of!(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector___redArg___closed__1_value) as *mut LeanObject;
pub static l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector___redArg___closed__2_value: LeanClosureObject<2> = LeanClosureObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut LeanObject>()*2) as u16, other: 0, tag: 245 }, m_fun: l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector___redArg___lam__6___boxed as *const core::ffi::c_void, m_arity: 4, m_num_fixed: 2, m_objs: [core::ptr::addr_of!(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector___redArg___closed__1_value) as *mut LeanObject,core::ptr::addr_of!(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector___redArg___closed__0_value) as *mut LeanObject] };
static mut l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector___redArg___closed__2: *mut LeanObject = core::ptr::addr_of!(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector___redArg___closed__2_value) as *mut LeanObject;
pub static l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector___redArg___closed__3_value: LeanClosureObject<0> = LeanClosureObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector___redArg___lam__10___boxed as *const core::ffi::c_void, m_arity: 2, m_num_fixed: 0, m_objs: [] };
static mut l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector___redArg___closed__3: *mut LeanObject = core::ptr::addr_of!(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector___redArg___closed__3_value) as *mut LeanObject;
static mut l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_new___redArg___closed__0_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_new___redArg___closed__0:
    *mut LeanObject = core::ptr::null_mut();
static mut l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_new___redArg___closed__1_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_new___redArg___closed__1:
    *mut LeanObject = core::ptr::null_mut();
pub static l___private_Init_While_0__whileM_erased___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_trySend_x27_spec__0___redArg___closed__0_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,((( 0 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Init_While_0__whileM_erased___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_trySend_x27_spec__0___redArg___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Init_While_0__whileM_erased___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_trySend_x27_spec__0___redArg___closed__0_value) as *mut LeanObject;
pub static l___private_Init_While_0__whileM_erased___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_trySend_x27_spec__0___redArg___closed__1_value: LeanCtorObject<1> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*1 + 0) as u16, other: 1, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Init_While_0__whileM_erased___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_trySend_x27_spec__0___redArg___closed__1: *mut LeanObject = core::ptr::addr_of!(l___private_Init_While_0__whileM_erased___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_trySend_x27_spec__0___redArg___closed__1_value) as *mut LeanObject;
pub static l___private_Init_While_0__whileM_erased___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_trySend_x27_spec__0___redArg___closed__2_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Init_While_0__whileM_erased___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_trySend_x27_spec__0___redArg___closed__1_value) as *mut LeanObject,((( 0 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Init_While_0__whileM_erased___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_trySend_x27_spec__0___redArg___closed__2: *mut LeanObject = core::ptr::addr_of!(l___private_Init_While_0__whileM_erased___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_trySend_x27_spec__0___redArg___closed__2_value) as *mut LeanObject;
pub static l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_send___redArg___closed__0_value: LeanClosureObject<0> = LeanClosureObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_send___redArg___lam__0___boxed as *const core::ffi::c_void, m_arity: 1, m_num_fixed: 0, m_objs: [] };
static mut l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_send___redArg___closed__0:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_send___redArg___closed__0_value
) as *mut LeanObject;
pub static l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_close___redArg___closed__0_value: LeanClosureObject<0> = LeanClosureObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_close___redArg___lam__0___boxed as *const core::ffi::c_void, m_arity: 2, m_num_fixed: 0, m_objs: [] };
static mut l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_close___redArg___closed__0:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_close___redArg___closed__0_value
) as *mut LeanObject;
pub static l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_isClosed___redArg___closed__0_value: LeanClosureObject<0> = LeanClosureObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_isClosed___redArg___lam__0___boxed as *const core::ffi::c_void, m_arity: 2, m_num_fixed: 0, m_objs: [] };
static mut l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_isClosed___redArg___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_isClosed___redArg___closed__0_value) as *mut LeanObject;
pub static l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_tryRecv___redArg___closed__0_value: LeanClosureObject<0> = LeanClosureObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_tryRecv_spec__0___redArg___boxed as *const core::ffi::c_void, m_arity: 2, m_num_fixed: 0, m_objs: [] };
static mut l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_tryRecv___redArg___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_tryRecv___redArg___closed__0_value) as *mut LeanObject;
pub static l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recv___redArg___closed__0_value: LeanClosureObject<1> = LeanClosureObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut LeanObject>()*1) as u16, other: 0, tag: 245 }, m_fun: l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recv___redArg___lam__1___boxed as *const core::ffi::c_void, m_arity: 3, m_num_fixed: 1, m_objs: [core::ptr::addr_of!(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recv___redArg___closed__0_value) as *mut LeanObject] };
static mut l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recv___redArg___closed__0:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recv___redArg___closed__0_value
) as *mut LeanObject;
pub static l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector___redArg___closed__0_value: LeanClosureObject<0> = LeanClosureObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector___redArg___lam__1___boxed as *const core::ffi::c_void, m_arity: 2, m_num_fixed: 0, m_objs: [] };
static mut l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector___redArg___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector___redArg___closed__0_value) as *mut LeanObject;
pub static l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector___redArg___closed__1_value: LeanClosureObject<2> = LeanClosureObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut LeanObject>()*2) as u16, other: 0, tag: 245 }, m_fun: l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector___redArg___lam__4___boxed as *const core::ffi::c_void, m_arity: 4, m_num_fixed: 2, m_objs: [core::ptr::addr_of!(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector___redArg___closed__0_value) as *mut LeanObject,core::ptr::addr_of!(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector___redArg___closed__0_value) as *mut LeanObject] };
static mut l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector___redArg___closed__1: *mut LeanObject = core::ptr::addr_of!(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector___redArg___closed__1_value) as *mut LeanObject;
pub static l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector___redArg___closed__2_value: LeanClosureObject<0> = LeanClosureObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector___redArg___lam__8___boxed as *const core::ffi::c_void, m_arity: 2, m_num_fixed: 0, m_objs: [] };
static mut l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector___redArg___closed__2: *mut LeanObject = core::ptr::addr_of!(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector___redArg___closed__2_value) as *mut LeanObject;
pub static l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_new___redArg___closed__0_value: LeanClosureObject<0> = LeanClosureObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_new___redArg___lam__0___boxed as *const core::ffi::c_void, m_arity: 2, m_num_fixed: 0, m_objs: [] };
static mut l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_new___redArg___closed__0:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_new___redArg___closed__0_value
) as *mut LeanObject;
pub static l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_new___redArg___closed__1_value: LeanArrayObject<0> = LeanArrayObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<usize>()*2 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 246 }, m_size: 0, m_capacity: 0, m_data: [] };
static mut l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_new___redArg___closed__1:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_new___redArg___closed__1_value
) as *mut LeanObject;
static mut l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_close___redArg___lam__0___closed__0_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_close___redArg___lam__0___closed__0: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_close___redArg___closed__0_value: LeanClosureObject<0> = LeanClosureObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_close___redArg___lam__0___boxed as *const core::ffi::c_void, m_arity: 2, m_num_fixed: 0, m_objs: [] };
static mut l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_close___redArg___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_close___redArg___closed__0_value) as *mut LeanObject;
pub static l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_isClosed___redArg___closed__0_value: LeanClosureObject<0> = LeanClosureObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_isClosed___redArg___lam__0___boxed as *const core::ffi::c_void, m_arity: 2, m_num_fixed: 0, m_objs: [] };
static mut l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_isClosed___redArg___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_isClosed___redArg___closed__0_value) as *mut LeanObject;
pub static l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv___redArg___closed__0_value: LeanClosureObject<0> = LeanClosureObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_spec__0___redArg___boxed as *const core::ffi::c_void, m_arity: 2, m_num_fixed: 0, m_objs: [] };
static mut l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv___redArg___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv___redArg___closed__0_value) as *mut LeanObject;
pub static l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_registerAux___redArg___lam__1___closed__0_value: LeanClosureObject<1> = LeanClosureObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut LeanObject>()*1) as u16, other: 0, tag: 245 }, m_fun: l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_registerAux___redArg___lam__0___boxed as *const core::ffi::c_void, m_arity: 2, m_num_fixed: 1, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_registerAux___redArg___lam__1___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_registerAux___redArg___lam__1___closed__0_value) as *mut LeanObject;
pub static l_Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_spec__1___redArg___closed__0_value: LeanClosureObject<0> = LeanClosureObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_spec__1___redArg___lam__0___boxed as *const core::ffi::c_void, m_arity: 2, m_num_fixed: 0, m_objs: [] };
static mut l_Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_spec__1___redArg___closed__0: *mut LeanObject = core::ptr::addr_of!(l_Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_spec__1___redArg___closed__0_value) as *mut LeanObject;
pub static l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector___redArg___closed__0_value: LeanClosureObject<0> = LeanClosureObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector___redArg___lam__0___boxed as *const core::ffi::c_void, m_arity: 2, m_num_fixed: 0, m_objs: [] };
static mut l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector___redArg___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector___redArg___closed__0_value) as *mut LeanObject;
pub static l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector___redArg___closed__1_value: LeanClosureObject<2> = LeanClosureObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut LeanObject>()*2) as u16, other: 0, tag: 245 }, m_fun: l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector___redArg___lam__3___boxed as *const core::ffi::c_void, m_arity: 4, m_num_fixed: 2, m_objs: [core::ptr::addr_of!(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector___redArg___closed__0_value) as *mut LeanObject,core::ptr::addr_of!(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector___redArg___closed__0_value) as *mut LeanObject] };
static mut l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector___redArg___closed__1: *mut LeanObject = core::ptr::addr_of!(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector___redArg___closed__1_value) as *mut LeanObject;
pub static l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector___redArg___closed__2_value: LeanClosureObject<0> = LeanClosureObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector___redArg___lam__6___boxed as *const core::ffi::c_void, m_arity: 2, m_num_fixed: 0, m_objs: [] };
static mut l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector___redArg___closed__2: *mut LeanObject = core::ptr::addr_of!(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector___redArg___closed__2_value) as *mut LeanObject;
static mut l_Std_CloseableChannel_forAsync___redArg___lam__0___closed__0_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_CloseableChannel_forAsync___redArg___lam__0___closed__0: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Std_CloseableChannel_instAsyncStreamOptionOfInhabited___closed__0_value:
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
    m_fun: l_Std_CloseableChannel_recvSelector___redArg as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_CloseableChannel_instAsyncStreamOptionOfInhabited___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Std_CloseableChannel_instAsyncStreamOptionOfInhabited___closed__0_value)
        as *mut LeanObject;
pub static l_Std_CloseableChannel_instAsyncStreamOptionOfInhabited___closed__1_value:
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
    m_fun: l_Std_CloseableChannel_instAsyncStreamOptionOfInhabited___lam__0___boxed
        as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_CloseableChannel_instAsyncStreamOptionOfInhabited___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Std_CloseableChannel_instAsyncStreamOptionOfInhabited___closed__1_value)
        as *mut LeanObject;
pub static l_Std_CloseableChannel_instAsyncStreamOptionOfInhabited___closed__2_value:
    LeanCtorObject<2> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 0,
    },
    m_objs: [
        core::ptr::addr_of!(
            l_Std_CloseableChannel_instAsyncStreamOptionOfInhabited___closed__0_value
        ) as *mut LeanObject,
        core::ptr::addr_of!(
            l_Std_CloseableChannel_instAsyncStreamOptionOfInhabited___closed__1_value
        ) as *mut LeanObject,
    ],
};
static mut l_Std_CloseableChannel_instAsyncStreamOptionOfInhabited___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Std_CloseableChannel_instAsyncStreamOptionOfInhabited___closed__2_value)
        as *mut LeanObject;
pub static l_Std_CloseableChannel_instAsyncReadOptionOfInhabited___closed__0_value:
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
    m_fun: l_Std_CloseableChannel_instAsyncReadOptionOfInhabited___lam__0
        as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_CloseableChannel_instAsyncReadOptionOfInhabited___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Std_CloseableChannel_instAsyncReadOptionOfInhabited___closed__0_value)
        as *mut LeanObject;
pub static l_Std_CloseableChannel_instAsyncReadOptionOfInhabited___closed__1_value:
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
    m_fun: l_Std_CloseableChannel_instAsyncReadOptionOfInhabited___lam__1___boxed
        as *const core::ffi::c_void,
    m_arity: 3,
    m_num_fixed: 1,
    m_objs: [core::ptr::addr_of!(
        l_Std_CloseableChannel_instAsyncReadOptionOfInhabited___closed__0_value
    ) as *mut LeanObject],
};
static mut l_Std_CloseableChannel_instAsyncReadOptionOfInhabited___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Std_CloseableChannel_instAsyncReadOptionOfInhabited___closed__1_value)
        as *mut LeanObject;
pub static l_Std_CloseableChannel_instAsyncReadOptionOfInhabited___closed__2_value:
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
    m_fun: l_Std_CloseableChannel_instAsyncReadOptionOfInhabited___lam__2___boxed
        as *const core::ffi::c_void,
    m_arity: 3,
    m_num_fixed: 1,
    m_objs: [core::ptr::addr_of!(
        l_Std_CloseableChannel_instAsyncReadOptionOfInhabited___closed__1_value
    ) as *mut LeanObject],
};
static mut l_Std_CloseableChannel_instAsyncReadOptionOfInhabited___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Std_CloseableChannel_instAsyncReadOptionOfInhabited___closed__2_value)
        as *mut LeanObject;
pub static l_Std_CloseableChannel_instAsyncWriteOfInhabited___lam__1___closed__0_value:
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
    m_fun: lean_mk_io_user_error as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_CloseableChannel_instAsyncWriteOfInhabited___lam__1___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Std_CloseableChannel_instAsyncWriteOfInhabited___lam__1___closed__0_value)
        as *mut LeanObject;
pub static l_Std_CloseableChannel_instAsyncWriteOfInhabited___closed__0_value: LeanClosureObject<
    1,
> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 1) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Std_CloseableChannel_instAsyncWriteOfInhabited___lam__1___boxed
        as *const core::ffi::c_void,
    m_arity: 3,
    m_num_fixed: 1,
    m_objs: [
        core::ptr::addr_of!(l_Std_CloseableChannel_instToStringError___closed__0_value)
            as *mut LeanObject,
    ],
};
static mut l_Std_CloseableChannel_instAsyncWriteOfInhabited___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Std_CloseableChannel_instAsyncWriteOfInhabited___closed__0_value)
        as *mut LeanObject;
pub static l_Std_CloseableChannel_instAsyncWriteOfInhabited___closed__1_value: LeanClosureObject<
    1,
> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 1) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Std_CloseableChannel_instAsyncWriteOfInhabited___lam__0___boxed
        as *const core::ffi::c_void,
    m_arity: 4,
    m_num_fixed: 1,
    m_objs: [
        core::ptr::addr_of!(l_Std_CloseableChannel_instAsyncWriteOfInhabited___closed__0_value)
            as *mut LeanObject,
    ],
};
static mut l_Std_CloseableChannel_instAsyncWriteOfInhabited___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Std_CloseableChannel_instAsyncWriteOfInhabited___closed__1_value)
        as *mut LeanObject;
pub static l_Std_CloseableChannel_instAsyncWriteOfInhabited___closed__2_value: LeanClosureObject<
    0,
> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Std_CloseableChannel_instAsyncWriteOfInhabited___lam__2___boxed
        as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_CloseableChannel_instAsyncWriteOfInhabited___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Std_CloseableChannel_instAsyncWriteOfInhabited___closed__2_value)
        as *mut LeanObject;
static mut l_Std_CloseableChannel_instAsyncWriteOfInhabited___closed__3_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_CloseableChannel_instAsyncWriteOfInhabited___closed__3: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Std_CloseableChannel_instAsyncWriteOfInhabited___closed__4_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_CloseableChannel_instAsyncWriteOfInhabited___closed__4: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Std_CloseableChannel_instAsyncWriteOfInhabited___closed__5_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_CloseableChannel_instAsyncWriteOfInhabited___closed__5: *mut LeanObject =
    core::ptr::null_mut();
static mut l_panic___at___00Std_Channel_send_spec__0___closed__0_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_panic___at___00Std_Channel_send_spec__0___closed__0: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Std_Channel_send___redArg___lam__0___closed__0_value: LeanStringObject<17> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 17,
        m_capacity: 17,
        m_length: 16,
        m_data: [
            83, 116, 100, 46, 83, 121, 110, 99, 46, 67, 104, 97, 110, 110, 101, 108, 0,
        ],
    };
static mut l_Std_Channel_send___redArg___lam__0___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Channel_send___redArg___lam__0___closed__0_value) as *mut LeanObject;
pub static l_Std_Channel_send___redArg___lam__0___closed__1_value: LeanStringObject<17> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 17,
        m_capacity: 17,
        m_length: 16,
        m_data: [
            83, 116, 100, 46, 67, 104, 97, 110, 110, 101, 108, 46, 115, 101, 110, 100, 0,
        ],
    };
static mut l_Std_Channel_send___redArg___lam__0___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Channel_send___redArg___lam__0___closed__1_value) as *mut LeanObject;
pub static l_Std_Channel_send___redArg___lam__0___closed__2_value: LeanStringObject<34> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 34,
        m_capacity: 34,
        m_length: 33,
        m_data: [
            117, 110, 114, 101, 97, 99, 104, 97, 98, 108, 101, 32, 99, 111, 100, 101, 32, 104, 97,
            115, 32, 98, 101, 101, 110, 32, 114, 101, 97, 99, 104, 101, 100, 0,
        ],
    };
static mut l_Std_Channel_send___redArg___lam__0___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Channel_send___redArg___lam__0___closed__2_value) as *mut LeanObject;
static mut l_Std_Channel_send___redArg___lam__0___closed__3_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_Channel_send___redArg___lam__0___closed__3: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Std_Channel_send___redArg___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_Std_Channel_send___redArg___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Std_Channel_send___redArg___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Channel_send___redArg___closed__0_value) as *mut LeanObject;
pub static l_Std_Channel_recv___redArg___lam__0___closed__0_value: LeanStringObject<17> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 17,
        m_capacity: 17,
        m_length: 16,
        m_data: [
            83, 116, 100, 46, 67, 104, 97, 110, 110, 101, 108, 46, 114, 101, 99, 118, 0,
        ],
    };
static mut l_Std_Channel_recv___redArg___lam__0___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Channel_recv___redArg___lam__0___closed__0_value) as *mut LeanObject;
static mut l_Std_Channel_recv___redArg___lam__0___closed__1_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_Channel_recv___redArg___lam__0___closed__1: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Std_Channel_recvSelector___redArg___lam__1___closed__0_value: LeanStringObject<26> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 26,
        m_capacity: 26,
        m_length: 25,
        m_data: [
            73, 110, 105, 116, 46, 68, 97, 116, 97, 46, 79, 112, 116, 105, 111, 110, 46, 66, 97,
            115, 105, 99, 65, 117, 120, 0,
        ],
    };
static mut l_Std_Channel_recvSelector___redArg___lam__1___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Channel_recvSelector___redArg___lam__1___closed__0_value)
        as *mut LeanObject;
pub static l_Std_Channel_recvSelector___redArg___lam__1___closed__1_value: LeanStringObject<12> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 12,
        m_capacity: 12,
        m_length: 11,
        m_data: [79, 112, 116, 105, 111, 110, 46, 103, 101, 116, 33, 0],
    };
static mut l_Std_Channel_recvSelector___redArg___lam__1___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Channel_recvSelector___redArg___lam__1___closed__1_value)
        as *mut LeanObject;
pub static l_Std_Channel_recvSelector___redArg___lam__1___closed__2_value: LeanStringObject<14> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 14,
        m_capacity: 14,
        m_length: 13,
        m_data: [
            118, 97, 108, 117, 101, 32, 105, 115, 32, 110, 111, 110, 101, 0,
        ],
    };
static mut l_Std_Channel_recvSelector___redArg___lam__1___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Channel_recvSelector___redArg___lam__1___closed__2_value)
        as *mut LeanObject;
static mut l_Std_Channel_recvSelector___redArg___lam__1___closed__3_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Channel_recvSelector___redArg___lam__1___closed__3: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Std_Channel_instAsyncReadOfInhabited___redArg___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_Std_Channel_instAsyncReadOfInhabited___redArg___lam__0 as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Std_Channel_instAsyncReadOfInhabited___redArg___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Channel_instAsyncReadOfInhabited___redArg___closed__0_value)
        as *mut LeanObject;
pub static l_Std_Channel_instAsyncReadOfInhabited___redArg___closed__1_value: LeanClosureObject<1> =
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
        m_fun: l_Std_Channel_instAsyncReadOfInhabited___redArg___lam__1___boxed
            as *const core::ffi::c_void,
        m_arity: 3,
        m_num_fixed: 1,
        m_objs: [core::ptr::addr_of!(
            l_Std_Channel_instAsyncReadOfInhabited___redArg___closed__0_value
        ) as *mut LeanObject],
    };
static mut l_Std_Channel_instAsyncReadOfInhabited___redArg___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Channel_instAsyncReadOfInhabited___redArg___closed__1_value)
        as *mut LeanObject;
pub static l_Std_Channel_instAsyncWriteOfInhabited___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_Std_Channel_instAsyncWriteOfInhabited___lam__0 as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Std_Channel_instAsyncWriteOfInhabited___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Channel_instAsyncWriteOfInhabited___closed__0_value)
        as *mut LeanObject;
pub static l_Std_Channel_instAsyncWriteOfInhabited___closed__1_value: LeanClosureObject<1> =
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
        m_fun: l_Std_Channel_instAsyncWriteOfInhabited___lam__1___boxed as *const core::ffi::c_void,
        m_arity: 3,
        m_num_fixed: 1,
        m_objs: [
            core::ptr::addr_of!(l_Std_Channel_instAsyncWriteOfInhabited___closed__0_value)
                as *mut LeanObject,
        ],
    };
static mut l_Std_Channel_instAsyncWriteOfInhabited___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Channel_instAsyncWriteOfInhabited___closed__1_value)
        as *mut LeanObject;
pub static l_Std_Channel_instAsyncWriteOfInhabited___closed__2_value: LeanClosureObject<1> =
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
        m_fun: l_Std_Channel_instAsyncWriteOfInhabited___lam__2___boxed as *const core::ffi::c_void,
        m_arity: 4,
        m_num_fixed: 1,
        m_objs: [
            core::ptr::addr_of!(l_Std_Channel_instAsyncWriteOfInhabited___closed__1_value)
                as *mut LeanObject,
        ],
    };
static mut l_Std_Channel_instAsyncWriteOfInhabited___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Channel_instAsyncWriteOfInhabited___closed__2_value)
        as *mut LeanObject;
static mut l_Std_Channel_instAsyncWriteOfInhabited___closed__3_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_Channel_instAsyncWriteOfInhabited___closed__3: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Std_Channel_instAsyncWriteOfInhabited___closed__4_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_Channel_instAsyncWriteOfInhabited___closed__4: *mut LeanObject =
    core::ptr::null_mut();
pub unsafe fn l_Std_CloseableChannel_Error_ctorIdx(mut v_x_5540_: u8) -> *mut LeanObject {
    if v_x_5540_ == 0 {
        let mut v___x_5541_: *mut LeanObject = core::ptr::null_mut();
        v___x_5541_ = lean_unsigned_to_nat(0);
        return v___x_5541_;
    } else {
        let mut v___x_5542_: *mut LeanObject = core::ptr::null_mut();
        v___x_5542_ = lean_unsigned_to_nat(1);
        return v___x_5542_;
    }
}
pub unsafe fn l_Std_CloseableChannel_Error_ctorIdx___boxed(
    mut v_x_5543_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_x_boxed_5544_: u8 = 0;
    let mut v_res_5545_: *mut LeanObject = core::ptr::null_mut();
    v_x_boxed_5544_ = (lean_unbox(v_x_5543_) as u8);
    v_res_5545_ = l_Std_CloseableChannel_Error_ctorIdx(v_x_boxed_5544_);
    return v_res_5545_;
}
pub unsafe fn l_Std_CloseableChannel_Error_toCtorIdx(mut v_x_5546_: u8) -> *mut LeanObject {
    let mut v___x_5547_: *mut LeanObject = core::ptr::null_mut();
    v___x_5547_ = l_Std_CloseableChannel_Error_ctorIdx(v_x_5546_);
    return v___x_5547_;
}
pub unsafe fn l_Std_CloseableChannel_Error_toCtorIdx___boxed(
    mut v_x_5548_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_x_4__boxed_5549_: u8 = 0;
    let mut v_res_5550_: *mut LeanObject = core::ptr::null_mut();
    v_x_4__boxed_5549_ = (lean_unbox(v_x_5548_) as u8);
    v_res_5550_ = l_Std_CloseableChannel_Error_toCtorIdx(v_x_4__boxed_5549_);
    return v_res_5550_;
}
pub unsafe fn l_Std_CloseableChannel_Error_ctorElim___redArg(
    mut v_k_5551_: *mut LeanObject,
) -> *mut LeanObject {
    lean_inc(v_k_5551_);
    return v_k_5551_;
}
pub unsafe fn l_Std_CloseableChannel_Error_ctorElim___redArg___boxed(
    mut v_k_5552_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5553_: *mut LeanObject = core::ptr::null_mut();
    v_res_5553_ = l_Std_CloseableChannel_Error_ctorElim___redArg(v_k_5552_);
    lean_dec(v_k_5552_);
    return v_res_5553_;
}
pub unsafe fn l_Std_CloseableChannel_Error_ctorElim(
    mut v_motive_5554_: *mut LeanObject,
    mut v_ctorIdx_5555_: *mut LeanObject,
    mut v_t_5556_: u8,
    mut v_h_5557_: *mut LeanObject,
    mut v_k_5558_: *mut LeanObject,
) -> *mut LeanObject {
    lean_inc(v_k_5558_);
    return v_k_5558_;
}
pub unsafe fn l_Std_CloseableChannel_Error_ctorElim___boxed(
    mut v_motive_5559_: *mut LeanObject,
    mut v_ctorIdx_5560_: *mut LeanObject,
    mut v_t_5561_: *mut LeanObject,
    mut v_h_5562_: *mut LeanObject,
    mut v_k_5563_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_t_boxed_5564_: u8 = 0;
    let mut v_res_5565_: *mut LeanObject = core::ptr::null_mut();
    v_t_boxed_5564_ = (lean_unbox(v_t_5561_) as u8);
    v_res_5565_ = l_Std_CloseableChannel_Error_ctorElim(
        v_motive_5559_,
        v_ctorIdx_5560_,
        v_t_boxed_5564_,
        v_h_5562_,
        v_k_5563_,
    );
    lean_dec(v_k_5563_);
    lean_dec(v_ctorIdx_5560_);
    return v_res_5565_;
}
pub unsafe fn l_Std_CloseableChannel_Error_closed_elim___redArg(
    mut v_closed_5566_: *mut LeanObject,
) -> *mut LeanObject {
    lean_inc(v_closed_5566_);
    return v_closed_5566_;
}
pub unsafe fn l_Std_CloseableChannel_Error_closed_elim___redArg___boxed(
    mut v_closed_5567_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5568_: *mut LeanObject = core::ptr::null_mut();
    v_res_5568_ = l_Std_CloseableChannel_Error_closed_elim___redArg(v_closed_5567_);
    lean_dec(v_closed_5567_);
    return v_res_5568_;
}
pub unsafe fn l_Std_CloseableChannel_Error_closed_elim(
    mut v_motive_5569_: *mut LeanObject,
    mut v_t_5570_: u8,
    mut v_h_5571_: *mut LeanObject,
    mut v_closed_5572_: *mut LeanObject,
) -> *mut LeanObject {
    lean_inc(v_closed_5572_);
    return v_closed_5572_;
}
pub unsafe fn l_Std_CloseableChannel_Error_closed_elim___boxed(
    mut v_motive_5573_: *mut LeanObject,
    mut v_t_5574_: *mut LeanObject,
    mut v_h_5575_: *mut LeanObject,
    mut v_closed_5576_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_t_boxed_5577_: u8 = 0;
    let mut v_res_5578_: *mut LeanObject = core::ptr::null_mut();
    v_t_boxed_5577_ = (lean_unbox(v_t_5574_) as u8);
    v_res_5578_ = l_Std_CloseableChannel_Error_closed_elim(
        v_motive_5573_,
        v_t_boxed_5577_,
        v_h_5575_,
        v_closed_5576_,
    );
    lean_dec(v_closed_5576_);
    return v_res_5578_;
}
pub unsafe fn l_Std_CloseableChannel_Error_alreadyClosed_elim___redArg(
    mut v_alreadyClosed_5579_: *mut LeanObject,
) -> *mut LeanObject {
    lean_inc(v_alreadyClosed_5579_);
    return v_alreadyClosed_5579_;
}
pub unsafe fn l_Std_CloseableChannel_Error_alreadyClosed_elim___redArg___boxed(
    mut v_alreadyClosed_5580_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5581_: *mut LeanObject = core::ptr::null_mut();
    v_res_5581_ = l_Std_CloseableChannel_Error_alreadyClosed_elim___redArg(v_alreadyClosed_5580_);
    lean_dec(v_alreadyClosed_5580_);
    return v_res_5581_;
}
pub unsafe fn l_Std_CloseableChannel_Error_alreadyClosed_elim(
    mut v_motive_5582_: *mut LeanObject,
    mut v_t_5583_: u8,
    mut v_h_5584_: *mut LeanObject,
    mut v_alreadyClosed_5585_: *mut LeanObject,
) -> *mut LeanObject {
    lean_inc(v_alreadyClosed_5585_);
    return v_alreadyClosed_5585_;
}
pub unsafe fn l_Std_CloseableChannel_Error_alreadyClosed_elim___boxed(
    mut v_motive_5586_: *mut LeanObject,
    mut v_t_5587_: *mut LeanObject,
    mut v_h_5588_: *mut LeanObject,
    mut v_alreadyClosed_5589_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_t_boxed_5590_: u8 = 0;
    let mut v_res_5591_: *mut LeanObject = core::ptr::null_mut();
    v_t_boxed_5590_ = (lean_unbox(v_t_5587_) as u8);
    v_res_5591_ = l_Std_CloseableChannel_Error_alreadyClosed_elim(
        v_motive_5586_,
        v_t_boxed_5590_,
        v_h_5588_,
        v_alreadyClosed_5589_,
    );
    lean_dec(v_alreadyClosed_5589_);
    return v_res_5591_;
}
pub unsafe fn _init_l_Std_CloseableChannel_instReprError_repr___closed__4() -> *mut LeanObject {
    let mut v___x_5598_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5599_: *mut LeanObject = core::ptr::null_mut();
    v___x_5598_ = lean_unsigned_to_nat(2);
    v___x_5599_ = lean_nat_to_int(v___x_5598_);
    return v___x_5599_;
}
pub unsafe fn _init_l_Std_CloseableChannel_instReprError_repr___closed__5() -> *mut LeanObject {
    let mut v___x_5600_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5601_: *mut LeanObject = core::ptr::null_mut();
    v___x_5600_ = lean_unsigned_to_nat(1);
    v___x_5601_ = lean_nat_to_int(v___x_5600_);
    return v___x_5601_;
}
pub unsafe fn l_Std_CloseableChannel_instReprError_repr(
    mut v_x_5602_: u8,
    mut v_prec_5603_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___y_5605_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5606_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5607_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5608_: u8 = 0;
    let mut v___x_5609_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5610_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5612_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5613_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5614_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5615_: u8 = 0;
    let mut v___x_5616_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5617_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5618_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5619_: u8 = 0;
    let mut v___x_5620_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5621_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5622_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5623_: u8 = 0;
    let mut v___x_5624_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5625_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if v_x_5602_ == 0 {
                    v___x_5618_ = lean_unsigned_to_nat(1024);
                    v___x_5619_ = lean_nat_dec_le(v___x_5618_, v_prec_5603_);
                    if v___x_5619_ == 0 {
                        v___x_5620_ = lean_obj_once(
                            core::ptr::addr_of_mut!(
                                l_Std_CloseableChannel_instReprError_repr___closed__4
                            ),
                            core::ptr::addr_of_mut!(
                                l_Std_CloseableChannel_instReprError_repr___closed__4_once
                            ),
                            _init_l_Std_CloseableChannel_instReprError_repr___closed__4,
                        );
                        v___y_5605_ = v___x_5620_;
                        state = 1;
                        continue;
                    } else {
                        v___x_5621_ = lean_obj_once(
                            core::ptr::addr_of_mut!(
                                l_Std_CloseableChannel_instReprError_repr___closed__5
                            ),
                            core::ptr::addr_of_mut!(
                                l_Std_CloseableChannel_instReprError_repr___closed__5_once
                            ),
                            _init_l_Std_CloseableChannel_instReprError_repr___closed__5,
                        );
                        v___y_5605_ = v___x_5621_;
                        state = 1;
                        continue;
                    }
                } else {
                    v___x_5622_ = lean_unsigned_to_nat(1024);
                    v___x_5623_ = lean_nat_dec_le(v___x_5622_, v_prec_5603_);
                    if v___x_5623_ == 0 {
                        v___x_5624_ = lean_obj_once(
                            core::ptr::addr_of_mut!(
                                l_Std_CloseableChannel_instReprError_repr___closed__4
                            ),
                            core::ptr::addr_of_mut!(
                                l_Std_CloseableChannel_instReprError_repr___closed__4_once
                            ),
                            _init_l_Std_CloseableChannel_instReprError_repr___closed__4,
                        );
                        v___y_5612_ = v___x_5624_;
                        state = 2;
                        continue;
                    } else {
                        v___x_5625_ = lean_obj_once(
                            core::ptr::addr_of_mut!(
                                l_Std_CloseableChannel_instReprError_repr___closed__5
                            ),
                            core::ptr::addr_of_mut!(
                                l_Std_CloseableChannel_instReprError_repr___closed__5_once
                            ),
                            _init_l_Std_CloseableChannel_instReprError_repr___closed__5,
                        );
                        v___y_5612_ = v___x_5625_;
                        state = 2;
                        continue;
                    }
                }
            }
            1 => {
                v___x_5606_ = l_Std_CloseableChannel_instReprError_repr___closed__1;
                lean_inc(v___y_5605_);
                v___x_5607_ = lean_alloc_ctor(4, 2, (0) as u32);
                lean_ctor_set(v___x_5607_, 0, v___y_5605_);
                lean_ctor_set(v___x_5607_, 1, v___x_5606_);
                v___x_5608_ = 0;
                v___x_5609_ = lean_alloc_ctor(6, 1, (1) as u32);
                lean_ctor_set(v___x_5609_, 0, v___x_5607_);
                lean_ctor_set_uint8(
                    v___x_5609_,
                    (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                    v___x_5608_,
                );
                v___x_5610_ = l_Repr_addAppParen(v___x_5609_, v_prec_5603_);
                return v___x_5610_;
            }
            2 => {
                v___x_5613_ = l_Std_CloseableChannel_instReprError_repr___closed__3;
                lean_inc(v___y_5612_);
                v___x_5614_ = lean_alloc_ctor(4, 2, (0) as u32);
                lean_ctor_set(v___x_5614_, 0, v___y_5612_);
                lean_ctor_set(v___x_5614_, 1, v___x_5613_);
                v___x_5615_ = 0;
                v___x_5616_ = lean_alloc_ctor(6, 1, (1) as u32);
                lean_ctor_set(v___x_5616_, 0, v___x_5614_);
                lean_ctor_set_uint8(
                    v___x_5616_,
                    (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                    v___x_5615_,
                );
                v___x_5617_ = l_Repr_addAppParen(v___x_5616_, v_prec_5603_);
                return v___x_5617_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_CloseableChannel_instReprError_repr___boxed(
    mut v_x_5626_: *mut LeanObject,
    mut v_prec_5627_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_x_121__boxed_5628_: u8 = 0;
    let mut v_res_5629_: *mut LeanObject = core::ptr::null_mut();
    v_x_121__boxed_5628_ = (lean_unbox(v_x_5626_) as u8);
    v_res_5629_ = l_Std_CloseableChannel_instReprError_repr(v_x_121__boxed_5628_, v_prec_5627_);
    lean_dec(v_prec_5627_);
    return v_res_5629_;
}
pub unsafe fn l_Std_CloseableChannel_Error_ofNat(mut v_n_5632_: *mut LeanObject) -> u8 {
    let mut v___x_5633_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5634_: u8 = 0;
    v___x_5633_ = lean_unsigned_to_nat(0);
    v___x_5634_ = lean_nat_dec_le(v_n_5632_, v___x_5633_);
    if v___x_5634_ == 0 {
        let mut v___x_5635_: u8 = 0;
        v___x_5635_ = 1;
        return v___x_5635_;
    } else {
        let mut v___x_5636_: u8 = 0;
        v___x_5636_ = 0;
        return v___x_5636_;
    }
}
pub unsafe fn l_Std_CloseableChannel_Error_ofNat___boxed(
    mut v_n_5637_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5638_: u8 = 0;
    let mut v_r_5639_: *mut LeanObject = core::ptr::null_mut();
    v_res_5638_ = l_Std_CloseableChannel_Error_ofNat(v_n_5637_);
    lean_dec(v_n_5637_);
    v_r_5639_ = lean_box((v_res_5638_) as usize);
    return v_r_5639_;
}
pub unsafe fn l_Std_CloseableChannel_instDecidableEqError(
    mut v_x_5640_: u8,
    mut v_y_5641_: u8,
) -> u8 {
    let mut v___x_5642_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5643_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5644_: u8 = 0;
    v___x_5642_ = l_Std_CloseableChannel_Error_ctorIdx(v_x_5640_);
    v___x_5643_ = l_Std_CloseableChannel_Error_ctorIdx(v_y_5641_);
    v___x_5644_ = lean_nat_dec_eq(v___x_5642_, v___x_5643_);
    lean_dec(v___x_5643_);
    lean_dec(v___x_5642_);
    return v___x_5644_;
}
pub unsafe fn l_Std_CloseableChannel_instDecidableEqError___boxed(
    mut v_x_5645_: *mut LeanObject,
    mut v_y_5646_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_x_13__boxed_5647_: u8 = 0;
    let mut v_y_14__boxed_5648_: u8 = 0;
    let mut v_res_5649_: u8 = 0;
    let mut v_r_5650_: *mut LeanObject = core::ptr::null_mut();
    v_x_13__boxed_5647_ = (lean_unbox(v_x_5645_) as u8);
    v_y_14__boxed_5648_ = (lean_unbox(v_y_5646_) as u8);
    v_res_5649_ =
        l_Std_CloseableChannel_instDecidableEqError(v_x_13__boxed_5647_, v_y_14__boxed_5648_);
    v_r_5650_ = lean_box((v_res_5649_) as usize);
    return v_r_5650_;
}
pub unsafe fn l_Std_CloseableChannel_instHashableError_hash(mut v_x_5651_: u8) -> u64 {
    if v_x_5651_ == 0 {
        let mut v___x_5652_: u64 = 0;
        v___x_5652_ = 0u64;
        return v___x_5652_;
    } else {
        let mut v___x_5653_: u64 = 0;
        v___x_5653_ = 1u64;
        return v___x_5653_;
    }
}
pub unsafe fn l_Std_CloseableChannel_instHashableError_hash___boxed(
    mut v_x_5654_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_x_28__boxed_5655_: u8 = 0;
    let mut v_res_5656_: u64 = 0;
    let mut v_r_5657_: *mut LeanObject = core::ptr::null_mut();
    v_x_28__boxed_5655_ = (lean_unbox(v_x_5654_) as u8);
    v_res_5656_ = l_Std_CloseableChannel_instHashableError_hash(v_x_28__boxed_5655_);
    v_r_5657_ = lean_box_uint64(v_res_5656_);
    return v_r_5657_;
}
pub unsafe fn l_Std_CloseableChannel_instToStringError___lam__0(
    mut v_x_5662_: u8,
) -> *mut LeanObject {
    if v_x_5662_ == 0 {
        let mut v___x_5663_: *mut LeanObject = core::ptr::null_mut();
        v___x_5663_ = l_Std_CloseableChannel_instToStringError___lam__0___closed__0;
        return v___x_5663_;
    } else {
        let mut v___x_5664_: *mut LeanObject = core::ptr::null_mut();
        v___x_5664_ = l_Std_CloseableChannel_instToStringError___lam__0___closed__1;
        return v___x_5664_;
    }
}
pub unsafe fn l_Std_CloseableChannel_instToStringError___lam__0___boxed(
    mut v_x_5665_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_x_26__boxed_5666_: u8 = 0;
    let mut v_res_5667_: *mut LeanObject = core::ptr::null_mut();
    v_x_26__boxed_5666_ = (lean_unbox(v_x_5665_) as u8);
    v_res_5667_ = l_Std_CloseableChannel_instToStringError___lam__0(v_x_26__boxed_5666_);
    return v_res_5667_;
}
pub unsafe fn l_Std_CloseableChannel_instMonadLiftEIOErrorIO___lam__0(
    mut v_00_u03b1_5674_: *mut LeanObject,
    mut v_x_5675_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5677_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5678_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5680_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5681_: u8 = 0;
    let mut v___x_5683_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5684_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5685_: u8 = 0;
    let mut v_a_5686_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5688_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5689_: u8 = 0;
    let mut v___x_5690_: u8 = 0;
    let mut v___x_5691_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5693_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5694_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5695_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5697_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5698_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5699_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5677_ = lean_apply_1(v_x_5675_, lean_box(0));
                if lean_obj_tag(v___x_5677_) == 0 {
                    v_a_5678_ = lean_ctor_get(v___x_5677_, 0);
                    v_isSharedCheck_5685_ = (!lean_is_exclusive(v___x_5677_)) as u8;
                    if v_isSharedCheck_5685_ == 0 {
                        v___x_5680_ = v___x_5677_;
                        v_isShared_5681_ = v_isSharedCheck_5685_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_5678_);
                        lean_dec(v___x_5677_);
                        v___x_5680_ = lean_box(0);
                        v_isShared_5681_ = v_isSharedCheck_5685_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_5686_ = lean_ctor_get(v___x_5677_, 0);
                    v_isSharedCheck_5699_ = (!lean_is_exclusive(v___x_5677_)) as u8;
                    if v_isSharedCheck_5699_ == 0 {
                        v___x_5688_ = v___x_5677_;
                        v_isShared_5689_ = v_isSharedCheck_5699_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_5686_);
                        lean_dec(v___x_5677_);
                        v___x_5688_ = lean_box(0);
                        v_isShared_5689_ = v_isSharedCheck_5699_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_5681_ == 0 {
                    v___x_5683_ = v___x_5680_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_5684_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5684_, 0, v_a_5678_);
                    v___x_5683_ = v_reuseFailAlloc_5684_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_5683_;
            }
            3 => {
                v___x_5690_ = (lean_unbox(v_a_5686_) as u8);
                lean_dec(v_a_5686_);
                if v___x_5690_ == 0 {
                    v___x_5691_ =
                        l_Std_CloseableChannel_instMonadLiftEIOErrorIO___lam__0___closed__0;
                    if v_isShared_5689_ == 0 {
                        lean_ctor_set(v___x_5688_, 0, v___x_5691_);
                        v___x_5693_ = v___x_5688_;
                        state = 4;
                        continue;
                    } else {
                        v_reuseFailAlloc_5694_ = lean_alloc_ctor(1, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_5694_, 0, v___x_5691_);
                        v___x_5693_ = v_reuseFailAlloc_5694_;
                        state = 4;
                        continue;
                    }
                } else {
                    v___x_5695_ =
                        l_Std_CloseableChannel_instMonadLiftEIOErrorIO___lam__0___closed__1;
                    if v_isShared_5689_ == 0 {
                        lean_ctor_set(v___x_5688_, 0, v___x_5695_);
                        v___x_5697_ = v___x_5688_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_5698_ = lean_alloc_ctor(1, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_5698_, 0, v___x_5695_);
                        v___x_5697_ = v_reuseFailAlloc_5698_;
                        state = 5;
                        continue;
                    }
                }
            }
            4 => {
                return v___x_5693_;
            }
            5 => {
                return v___x_5697_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_CloseableChannel_instMonadLiftEIOErrorIO___lam__0___boxed(
    mut v_00_u03b1_5700_: *mut LeanObject,
    mut v_x_5701_: *mut LeanObject,
    mut v___y_5702_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5703_: *mut LeanObject = core::ptr::null_mut();
    v_res_5703_ =
        l_Std_CloseableChannel_instMonadLiftEIOErrorIO___lam__0(v_00_u03b1_5700_, v_x_5701_);
    return v_res_5703_;
}
pub unsafe fn l___private_Std_Sync_Channel_0__Std_CloseableChannel_Consumer_ctorIdx___redArg(
    mut v_x_5706_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_5706_) == 0 {
        let mut v___x_5707_: *mut LeanObject = core::ptr::null_mut();
        v___x_5707_ = lean_unsigned_to_nat(0);
        return v___x_5707_;
    } else {
        let mut v___x_5708_: *mut LeanObject = core::ptr::null_mut();
        v___x_5708_ = lean_unsigned_to_nat(1);
        return v___x_5708_;
    }
}
pub unsafe fn l___private_Std_Sync_Channel_0__Std_CloseableChannel_Consumer_ctorIdx___redArg___boxed(
    mut v_x_5709_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5710_: *mut LeanObject = core::ptr::null_mut();
    v_res_5710_ =
        l___private_Std_Sync_Channel_0__Std_CloseableChannel_Consumer_ctorIdx___redArg(v_x_5709_);
    lean_dec_ref(v_x_5709_);
    return v_res_5710_;
}
pub unsafe fn l___private_Std_Sync_Channel_0__Std_CloseableChannel_Consumer_ctorIdx(
    mut v_00_u03b1_5711_: *mut LeanObject,
    mut v_x_5712_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5713_: *mut LeanObject = core::ptr::null_mut();
    v___x_5713_ =
        l___private_Std_Sync_Channel_0__Std_CloseableChannel_Consumer_ctorIdx___redArg(v_x_5712_);
    return v___x_5713_;
}
pub unsafe fn l___private_Std_Sync_Channel_0__Std_CloseableChannel_Consumer_ctorIdx___boxed(
    mut v_00_u03b1_5714_: *mut LeanObject,
    mut v_x_5715_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5716_: *mut LeanObject = core::ptr::null_mut();
    v_res_5716_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Consumer_ctorIdx(
        v_00_u03b1_5714_,
        v_x_5715_,
    );
    lean_dec_ref(v_x_5715_);
    return v_res_5716_;
}
pub unsafe fn l___private_Std_Sync_Channel_0__Std_CloseableChannel_Consumer_ctorElim___redArg(
    mut v_t_5717_: *mut LeanObject,
    mut v_k_5718_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_t_5717_) == 0 {
        let mut v_promise_5719_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_5720_: *mut LeanObject = core::ptr::null_mut();
        v_promise_5719_ = lean_ctor_get(v_t_5717_, 0);
        lean_inc(v_promise_5719_);
        lean_dec_ref_known(v_t_5717_, 1);
        v___x_5720_ = lean_apply_1(v_k_5718_, v_promise_5719_);
        return v___x_5720_;
    } else {
        let mut v_finished_5721_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_5722_: *mut LeanObject = core::ptr::null_mut();
        v_finished_5721_ = lean_ctor_get(v_t_5717_, 0);
        lean_inc_ref(v_finished_5721_);
        lean_dec_ref_known(v_t_5717_, 1);
        v___x_5722_ = lean_apply_1(v_k_5718_, v_finished_5721_);
        return v___x_5722_;
    }
}
pub unsafe fn l___private_Std_Sync_Channel_0__Std_CloseableChannel_Consumer_ctorElim(
    mut v_00_u03b1_5723_: *mut LeanObject,
    mut v_motive_5724_: *mut LeanObject,
    mut v_ctorIdx_5725_: *mut LeanObject,
    mut v_t_5726_: *mut LeanObject,
    mut v_h_5727_: *mut LeanObject,
    mut v_k_5728_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5729_: *mut LeanObject = core::ptr::null_mut();
    v___x_5729_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Consumer_ctorElim___redArg(
        v_t_5726_, v_k_5728_,
    );
    return v___x_5729_;
}
pub unsafe fn l___private_Std_Sync_Channel_0__Std_CloseableChannel_Consumer_ctorElim___boxed(
    mut v_00_u03b1_5730_: *mut LeanObject,
    mut v_motive_5731_: *mut LeanObject,
    mut v_ctorIdx_5732_: *mut LeanObject,
    mut v_t_5733_: *mut LeanObject,
    mut v_h_5734_: *mut LeanObject,
    mut v_k_5735_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5736_: *mut LeanObject = core::ptr::null_mut();
    v_res_5736_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Consumer_ctorElim(
        v_00_u03b1_5730_,
        v_motive_5731_,
        v_ctorIdx_5732_,
        v_t_5733_,
        v_h_5734_,
        v_k_5735_,
    );
    lean_dec(v_ctorIdx_5732_);
    return v_res_5736_;
}
pub unsafe fn l___private_Std_Sync_Channel_0__Std_CloseableChannel_Consumer_normal_elim___redArg(
    mut v_t_5737_: *mut LeanObject,
    mut v_normal_5738_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5739_: *mut LeanObject = core::ptr::null_mut();
    v___x_5739_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Consumer_ctorElim___redArg(
        v_t_5737_,
        v_normal_5738_,
    );
    return v___x_5739_;
}
pub unsafe fn l___private_Std_Sync_Channel_0__Std_CloseableChannel_Consumer_normal_elim(
    mut v_00_u03b1_5740_: *mut LeanObject,
    mut v_motive_5741_: *mut LeanObject,
    mut v_t_5742_: *mut LeanObject,
    mut v_h_5743_: *mut LeanObject,
    mut v_normal_5744_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5745_: *mut LeanObject = core::ptr::null_mut();
    v___x_5745_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Consumer_ctorElim___redArg(
        v_t_5742_,
        v_normal_5744_,
    );
    return v___x_5745_;
}
pub unsafe fn l___private_Std_Sync_Channel_0__Std_CloseableChannel_Consumer_select_elim___redArg(
    mut v_t_5746_: *mut LeanObject,
    mut v_select_5747_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5748_: *mut LeanObject = core::ptr::null_mut();
    v___x_5748_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Consumer_ctorElim___redArg(
        v_t_5746_,
        v_select_5747_,
    );
    return v___x_5748_;
}
pub unsafe fn l___private_Std_Sync_Channel_0__Std_CloseableChannel_Consumer_select_elim(
    mut v_00_u03b1_5749_: *mut LeanObject,
    mut v_motive_5750_: *mut LeanObject,
    mut v_t_5751_: *mut LeanObject,
    mut v_h_5752_: *mut LeanObject,
    mut v_select_5753_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5754_: *mut LeanObject = core::ptr::null_mut();
    v___x_5754_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Consumer_ctorElim___redArg(
        v_t_5751_,
        v_select_5753_,
    );
    return v___x_5754_;
}
pub unsafe fn l_Std_Async_Waiter_race___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Consumer_resolve_spec__0___redArg(
    mut v_x_5755_: *mut LeanObject,
    mut v_w_5756_: *mut LeanObject,
    mut v_lose_5757_: *mut LeanObject,
) -> u8 {
    let mut v_finished_5759_: *mut LeanObject = core::ptr::null_mut();
    let mut v_promise_5760_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5761_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5763_: u8 = 0;
    let mut v___x_5764_: u8 = 0;
    let mut v___x_5765_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5766_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5767_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5768_: u8 = 0;
    let mut v___x_5769_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5770_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5771_: u8 = 0;
    let mut v___x_5772_: u8 = 0;
    let mut v___x_5773_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_finished_5759_ = lean_ctor_get(v_w_5756_, 0);
                v_promise_5760_ = lean_ctor_get(v_w_5756_, 1);
                v___x_5761_ = lean_st_ref_take(v_finished_5759_);
                v___x_5771_ = (lean_unbox(v___x_5761_) as u8);
                lean_dec(v___x_5761_);
                if v___x_5771_ == 0 {
                    v___x_5772_ = 1;
                    v___y_5763_ = v___x_5772_;
                    state = 1;
                    continue;
                } else {
                    v___x_5773_ = 0;
                    v___y_5763_ = v___x_5773_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_5764_ = 1;
                v___x_5765_ = lean_box((v___x_5764_) as usize);
                v___x_5766_ = lean_st_ref_set(v_finished_5759_, v___x_5765_);
                if v___y_5763_ == 0 {
                    lean_dec(v_x_5755_);
                    v___x_5767_ = lean_apply_1(v_lose_5757_, lean_box(0));
                    v___x_5768_ = (lean_unbox(v___x_5767_) as u8);
                    return v___x_5768_;
                } else {
                    lean_dec_ref(v_lose_5757_);
                    v___x_5769_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v___x_5769_, 0, v_x_5755_);
                    v___x_5770_ = lean_io_promise_resolve(v___x_5769_, v_promise_5760_);
                    return v___y_5763_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Async_Waiter_race___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Consumer_resolve_spec__0___redArg___boxed(
    mut v_x_5774_: *mut LeanObject,
    mut v_w_5775_: *mut LeanObject,
    mut v_lose_5776_: *mut LeanObject,
    mut v___y_5777_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5778_: u8 = 0;
    let mut v_r_5779_: *mut LeanObject = core::ptr::null_mut();
    v_res_5778_ = l_Std_Async_Waiter_race___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Consumer_resolve_spec__0___redArg(v_x_5774_, v_w_5775_, v_lose_5776_);
    lean_dec_ref(v_w_5775_);
    v_r_5779_ = lean_box((v_res_5778_) as usize);
    return v_r_5779_;
}
pub unsafe fn l_Std_Async_Waiter_race___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Consumer_resolve_spec__0(
    mut v_00_u03b1_5780_: *mut LeanObject,
    mut v_x_5781_: *mut LeanObject,
    mut v_w_5782_: *mut LeanObject,
    mut v_lose_5783_: *mut LeanObject,
) -> u8 {
    let mut v___x_5785_: u8 = 0;
    v___x_5785_ = l_Std_Async_Waiter_race___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Consumer_resolve_spec__0___redArg(v_x_5781_, v_w_5782_, v_lose_5783_);
    return v___x_5785_;
}
pub unsafe fn l_Std_Async_Waiter_race___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Consumer_resolve_spec__0___boxed(
    mut v_00_u03b1_5786_: *mut LeanObject,
    mut v_x_5787_: *mut LeanObject,
    mut v_w_5788_: *mut LeanObject,
    mut v_lose_5789_: *mut LeanObject,
    mut v___y_5790_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5791_: u8 = 0;
    let mut v_r_5792_: *mut LeanObject = core::ptr::null_mut();
    v_res_5791_ = l_Std_Async_Waiter_race___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Consumer_resolve_spec__0(v_00_u03b1_5786_, v_x_5787_, v_w_5788_, v_lose_5789_);
    lean_dec_ref(v_w_5788_);
    v_r_5792_ = lean_box((v_res_5791_) as usize);
    return v_r_5792_;
}
pub unsafe fn l___private_Std_Sync_Channel_0__Std_CloseableChannel_Consumer_resolve___redArg___lam__0(
    mut v___x_5793_: u8,
) -> u8 {
    return v___x_5793_;
}
pub unsafe fn l___private_Std_Sync_Channel_0__Std_CloseableChannel_Consumer_resolve___redArg___lam__0___boxed(
    mut v___x_5795_: *mut LeanObject,
    mut v___y_5796_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_400__boxed_5797_: u8 = 0;
    let mut v_res_5798_: u8 = 0;
    let mut v_r_5799_: *mut LeanObject = core::ptr::null_mut();
    v___x_400__boxed_5797_ = (lean_unbox(v___x_5795_) as u8);
    v_res_5798_ =
        l___private_Std_Sync_Channel_0__Std_CloseableChannel_Consumer_resolve___redArg___lam__0(
            v___x_400__boxed_5797_,
        );
    v_r_5799_ = lean_box((v_res_5798_) as usize);
    return v_r_5799_;
}
pub unsafe fn l___private_Std_Sync_Channel_0__Std_CloseableChannel_Consumer_resolve___redArg(
    mut v_c_5803_: *mut LeanObject,
    mut v_x_5804_: *mut LeanObject,
) -> u8 {
    if lean_obj_tag(v_c_5803_) == 0 {
        let mut v_promise_5806_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_5807_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_5808_: u8 = 0;
        v_promise_5806_ = lean_ctor_get(v_c_5803_, 0);
        v___x_5807_ = lean_io_promise_resolve(v_x_5804_, v_promise_5806_);
        v___x_5808_ = 1;
        return v___x_5808_;
    } else {
        let mut v_finished_5809_: *mut LeanObject = core::ptr::null_mut();
        let mut v_lose_5810_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_5811_: u8 = 0;
        v_finished_5809_ = lean_ctor_get(v_c_5803_, 0);
        v_lose_5810_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Consumer_resolve___redArg___closed__0;
        v___x_5811_ = l_Std_Async_Waiter_race___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Consumer_resolve_spec__0___redArg(v_x_5804_, v_finished_5809_, v_lose_5810_);
        return v___x_5811_;
    }
}
pub unsafe fn l___private_Std_Sync_Channel_0__Std_CloseableChannel_Consumer_resolve___redArg___boxed(
    mut v_c_5812_: *mut LeanObject,
    mut v_x_5813_: *mut LeanObject,
    mut v_a_5814_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5815_: u8 = 0;
    let mut v_r_5816_: *mut LeanObject = core::ptr::null_mut();
    v_res_5815_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Consumer_resolve___redArg(
        v_c_5812_, v_x_5813_,
    );
    lean_dec_ref(v_c_5812_);
    v_r_5816_ = lean_box((v_res_5815_) as usize);
    return v_r_5816_;
}
pub unsafe fn l___private_Std_Sync_Channel_0__Std_CloseableChannel_Consumer_resolve(
    mut v_00_u03b1_5817_: *mut LeanObject,
    mut v_c_5818_: *mut LeanObject,
    mut v_x_5819_: *mut LeanObject,
) -> u8 {
    let mut v___x_5821_: u8 = 0;
    v___x_5821_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Consumer_resolve___redArg(
        v_c_5818_, v_x_5819_,
    );
    return v___x_5821_;
}
pub unsafe fn l___private_Std_Sync_Channel_0__Std_CloseableChannel_Consumer_resolve___boxed(
    mut v_00_u03b1_5822_: *mut LeanObject,
    mut v_c_5823_: *mut LeanObject,
    mut v_x_5824_: *mut LeanObject,
    mut v_a_5825_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5826_: u8 = 0;
    let mut v_r_5827_: *mut LeanObject = core::ptr::null_mut();
    v_res_5826_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Consumer_resolve(
        v_00_u03b1_5822_,
        v_c_5823_,
        v_x_5824_,
    );
    lean_dec_ref(v_c_5823_);
    v_r_5827_ = lean_box((v_res_5826_) as usize);
    return v_r_5827_;
}
pub unsafe fn _init_l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_new___redArg___closed__0()
-> *mut LeanObject {
    let mut v___x_5828_: *mut LeanObject = core::ptr::null_mut();
    v___x_5828_ = l_Std_Queue_empty(lean_box(0));
    return v___x_5828_;
}
pub unsafe fn _init_l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_new___redArg___closed__1()
-> *mut LeanObject {
    let mut v___x_5829_: u8 = 0;
    let mut v___x_5830_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5831_: *mut LeanObject = core::ptr::null_mut();
    v___x_5829_ = 0;
    v___x_5830_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_new___redArg___closed__0), core::ptr::addr_of_mut!(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_new___redArg___closed__0_once), _init_l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_new___redArg___closed__0);
    v___x_5831_ = lean_alloc_ctor(0, 2, (1) as u32);
    lean_ctor_set(v___x_5831_, 0, v___x_5830_);
    lean_ctor_set(v___x_5831_, 1, v___x_5830_);
    lean_ctor_set_uint8(
        v___x_5831_,
        (core::mem::size_of::<*mut LeanObject>() * 2) as u32,
        v___x_5829_,
    );
    return v___x_5831_;
}
pub unsafe fn l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_new___redArg()
-> *mut LeanObject {
    let mut v___x_5833_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5834_: *mut LeanObject = core::ptr::null_mut();
    v___x_5833_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_new___redArg___closed__1), core::ptr::addr_of_mut!(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_new___redArg___closed__1_once), _init_l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_new___redArg___closed__1);
    v___x_5834_ = l_Std_Mutex_new___redArg(v___x_5833_);
    return v___x_5834_;
}
pub unsafe fn l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_new___redArg___boxed(
    mut v_a_5835_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5836_: *mut LeanObject = core::ptr::null_mut();
    v_res_5836_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_new___redArg();
    return v_res_5836_;
}
pub unsafe fn l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_new(
    mut v_00_u03b1_5837_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5839_: *mut LeanObject = core::ptr::null_mut();
    v___x_5839_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_new___redArg();
    return v___x_5839_;
}
pub unsafe fn l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_new___boxed(
    mut v_00_u03b1_5840_: *mut LeanObject,
    mut v_a_5841_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5842_: *mut LeanObject = core::ptr::null_mut();
    v_res_5842_ =
        l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_new(v_00_u03b1_5840_);
    return v_res_5842_;
}
pub unsafe fn l_Std_Mutex_atomically___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_trySend_spec__1___redArg(
    mut v_mutex_5843_: *mut LeanObject,
    mut v_k_5844_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_ref_5846_: *mut LeanObject = core::ptr::null_mut();
    let mut v_mutex_5847_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5848_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5849_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5850_: *mut LeanObject = core::ptr::null_mut();
    v_ref_5846_ = lean_ctor_get(v_mutex_5843_, 0);
    lean_inc(v_ref_5846_);
    v_mutex_5847_ = lean_ctor_get(v_mutex_5843_, 1);
    lean_inc(v_mutex_5847_);
    lean_dec_ref(v_mutex_5843_);
    v___x_5848_ = lean_io_basemutex_lock(v_mutex_5847_);
    v___x_5849_ = lean_apply_2(v_k_5844_, v_ref_5846_, lean_box(0));
    v___x_5850_ = lean_io_basemutex_unlock(v_mutex_5847_);
    lean_dec(v_mutex_5847_);
    return v___x_5849_;
}
pub unsafe fn l_Std_Mutex_atomically___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_trySend_spec__1___redArg___boxed(
    mut v_mutex_5851_: *mut LeanObject,
    mut v_k_5852_: *mut LeanObject,
    mut v___y_5853_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5854_: *mut LeanObject = core::ptr::null_mut();
    v_res_5854_ = l_Std_Mutex_atomically___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_trySend_spec__1___redArg(v_mutex_5851_, v_k_5852_);
    return v_res_5854_;
}
pub unsafe fn l_Std_Mutex_atomically___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_trySend_spec__1(
    mut v_00_u03b1_5855_: *mut LeanObject,
    mut v_00_u03b2_5856_: *mut LeanObject,
    mut v_mutex_5857_: *mut LeanObject,
    mut v_k_5858_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5860_: *mut LeanObject = core::ptr::null_mut();
    v___x_5860_ = l_Std_Mutex_atomically___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_trySend_spec__1___redArg(v_mutex_5857_, v_k_5858_);
    return v___x_5860_;
}
pub unsafe fn l_Std_Mutex_atomically___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_trySend_spec__1___boxed(
    mut v_00_u03b1_5861_: *mut LeanObject,
    mut v_00_u03b2_5862_: *mut LeanObject,
    mut v_mutex_5863_: *mut LeanObject,
    mut v_k_5864_: *mut LeanObject,
    mut v___y_5865_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5866_: *mut LeanObject = core::ptr::null_mut();
    v_res_5866_ = l_Std_Mutex_atomically___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_trySend_spec__1(v_00_u03b1_5861_, v_00_u03b2_5862_, v_mutex_5863_, v_k_5864_);
    return v_res_5866_;
}
pub unsafe fn l___private_Init_While_0__whileM_erased___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_trySend_spec__0___redArg(
    mut v_v_5867_: *mut LeanObject,
    mut v___y_5868_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5870_: *mut LeanObject = core::ptr::null_mut();
    let mut v_values_5871_: *mut LeanObject = core::ptr::null_mut();
    let mut v_consumers_5872_: *mut LeanObject = core::ptr::null_mut();
    let mut v_closed_5873_: u8 = 0;
    let mut v___x_5875_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5876_: u8 = 0;
    let mut v___x_5877_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5878_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_5879_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5881_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5882_: u8 = 0;
    let mut v_fst_5883_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_5884_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5886_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5887_: u8 = 0;
    let mut v___x_5889_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5890_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5892_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5893_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5894_: u8 = 0;
    let mut v___x_5895_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5897_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5898_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5899_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5900_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5870_ = lean_st_ref_get(v___y_5868_);
                v_values_5871_ = lean_ctor_get(v___x_5870_, 0);
                v_consumers_5872_ = lean_ctor_get(v___x_5870_, 1);
                v_closed_5873_ = lean_ctor_get_uint8(
                    v___x_5870_,
                    (core::mem::size_of::<*mut LeanObject>() * 2) as u32,
                );
                v_isSharedCheck_5900_ = (!lean_is_exclusive(v___x_5870_)) as u8;
                if v_isSharedCheck_5900_ == 0 {
                    v___x_5875_ = v___x_5870_;
                    v_isShared_5876_ = v_isSharedCheck_5900_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_consumers_5872_);
                    lean_inc(v_values_5871_);
                    lean_dec(v___x_5870_);
                    v___x_5875_ = lean_box(0);
                    v_isShared_5876_ = v_isSharedCheck_5900_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_5877_ = lean_box(0);
                lean_inc_ref(v_consumers_5872_);
                v___x_5878_ = l_Std_Queue_dequeue_x3f___redArg(v_consumers_5872_);
                if lean_obj_tag(v___x_5878_) == 1 {
                    lean_dec_ref(v_consumers_5872_);
                    v_val_5879_ = lean_ctor_get(v___x_5878_, 0);
                    v_isSharedCheck_5894_ = (!lean_is_exclusive(v___x_5878_)) as u8;
                    if v_isSharedCheck_5894_ == 0 {
                        v___x_5881_ = v___x_5878_;
                        v_isShared_5882_ = v_isSharedCheck_5894_;
                        state = 2;
                        continue;
                    } else {
                        lean_inc(v_val_5879_);
                        lean_dec(v___x_5878_);
                        v___x_5881_ = lean_box(0);
                        v_isShared_5882_ = v_isSharedCheck_5894_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_dec(v___x_5878_);
                    v___x_5895_ = l_Std_Queue_enqueue___redArg(v_v_5867_, v_values_5871_);
                    if v_isShared_5876_ == 0 {
                        lean_ctor_set(v___x_5875_, 0, v___x_5895_);
                        v___x_5897_ = v___x_5875_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_5899_ = lean_alloc_ctor(0, 2, (1) as u32);
                        lean_ctor_set(v_reuseFailAlloc_5899_, 0, v___x_5895_);
                        lean_ctor_set(v_reuseFailAlloc_5899_, 1, v_consumers_5872_);
                        lean_ctor_set_uint8(
                            v_reuseFailAlloc_5899_,
                            (core::mem::size_of::<*mut LeanObject>() * 2) as u32,
                            v_closed_5873_,
                        );
                        v___x_5897_ = v_reuseFailAlloc_5899_;
                        state = 5;
                        continue;
                    }
                }
            }
            2 => {
                v_fst_5883_ = lean_ctor_get(v_val_5879_, 0);
                lean_inc(v_fst_5883_);
                v_snd_5884_ = lean_ctor_get(v_val_5879_, 1);
                lean_inc(v_snd_5884_);
                lean_dec(v_val_5879_);
                lean_inc(v_v_5867_);
                if v_isShared_5882_ == 0 {
                    lean_ctor_set(v___x_5881_, 0, v_v_5867_);
                    v___x_5886_ = v___x_5881_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_5893_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5893_, 0, v_v_5867_);
                    v___x_5886_ = v_reuseFailAlloc_5893_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_5887_ =
                    l___private_Std_Sync_Channel_0__Std_CloseableChannel_Consumer_resolve___redArg(
                        v_fst_5883_,
                        v___x_5886_,
                    );
                lean_dec(v_fst_5883_);
                if v_isShared_5876_ == 0 {
                    lean_ctor_set(v___x_5875_, 1, v_snd_5884_);
                    v___x_5889_ = v___x_5875_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_5892_ = lean_alloc_ctor(0, 2, (1) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5892_, 0, v_values_5871_);
                    lean_ctor_set(v_reuseFailAlloc_5892_, 1, v_snd_5884_);
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_5892_,
                        (core::mem::size_of::<*mut LeanObject>() * 2) as u32,
                        v_closed_5873_,
                    );
                    v___x_5889_ = v_reuseFailAlloc_5892_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_5890_ = lean_st_ref_set(v___y_5868_, v___x_5889_);
                if v___x_5887_ == 0 {
                    state = 0;
                    continue;
                } else {
                    lean_dec(v_v_5867_);
                    return v___x_5877_;
                }
            }
            5 => {
                v___x_5898_ = lean_st_ref_set(v___y_5868_, v___x_5897_);
                return v___x_5877_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_While_0__whileM_erased___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_trySend_spec__0___redArg___boxed(
    mut v_v_5901_: *mut LeanObject,
    mut v___y_5902_: *mut LeanObject,
    mut v___y_5903_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5904_: *mut LeanObject = core::ptr::null_mut();
    v_res_5904_ = l___private_Init_While_0__whileM_erased___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_trySend_spec__0___redArg(v_v_5901_, v___y_5902_);
    lean_dec(v___y_5902_);
    return v_res_5904_;
}
pub unsafe fn l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_trySend___redArg___lam__0(
    mut v_v_5905_: *mut LeanObject,
    mut v___y_5906_: *mut LeanObject,
) -> u8 {
    let mut v___x_5908_: *mut LeanObject = core::ptr::null_mut();
    let mut v_closed_5909_: u8 = 0;
    v___x_5908_ = lean_st_ref_get(v___y_5906_);
    v_closed_5909_ = lean_ctor_get_uint8(
        v___x_5908_,
        (core::mem::size_of::<*mut LeanObject>() * 2) as u32,
    );
    lean_dec(v___x_5908_);
    if v_closed_5909_ == 0 {
        let mut v___x_5910_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_5911_: u8 = 0;
        v___x_5910_ = l___private_Init_While_0__whileM_erased___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_trySend_spec__0___redArg(v_v_5905_, v___y_5906_);
        v___x_5911_ = 1;
        return v___x_5911_;
    } else {
        let mut v___x_5912_: u8 = 0;
        lean_dec(v_v_5905_);
        v___x_5912_ = 0;
        return v___x_5912_;
    }
}
pub unsafe fn l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_trySend___redArg___lam__0___boxed(
    mut v_v_5913_: *mut LeanObject,
    mut v___y_5914_: *mut LeanObject,
    mut v___y_5915_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5916_: u8 = 0;
    let mut v_r_5917_: *mut LeanObject = core::ptr::null_mut();
    v_res_5916_ =
        l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_trySend___redArg___lam__0(
            v_v_5913_,
            v___y_5914_,
        );
    lean_dec(v___y_5914_);
    v_r_5917_ = lean_box((v_res_5916_) as usize);
    return v_r_5917_;
}
pub unsafe fn l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_trySend___redArg(
    mut v_ch_5918_: *mut LeanObject,
    mut v_v_5919_: *mut LeanObject,
) -> u8 {
    let mut v___f_5921_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5922_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5923_: u8 = 0;
    v___f_5921_ = lean_alloc_closure(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_trySend___redArg___lam__0___boxed as *mut core::ffi::c_void, 3, 1);
    lean_closure_set(v___f_5921_, 0, v_v_5919_);
    v___x_5922_ = l_Std_Mutex_atomically___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_trySend_spec__1___redArg(v_ch_5918_, v___f_5921_);
    v___x_5923_ = (lean_unbox(v___x_5922_) as u8);
    lean_dec(v___x_5922_);
    return v___x_5923_;
}
pub unsafe fn l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_trySend___redArg___boxed(
    mut v_ch_5924_: *mut LeanObject,
    mut v_v_5925_: *mut LeanObject,
    mut v_a_5926_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5927_: u8 = 0;
    let mut v_r_5928_: *mut LeanObject = core::ptr::null_mut();
    v_res_5927_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_trySend___redArg(
        v_ch_5924_, v_v_5925_,
    );
    v_r_5928_ = lean_box((v_res_5927_) as usize);
    return v_r_5928_;
}
pub unsafe fn l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_trySend(
    mut v_00_u03b1_5929_: *mut LeanObject,
    mut v_ch_5930_: *mut LeanObject,
    mut v_v_5931_: *mut LeanObject,
) -> u8 {
    let mut v___x_5933_: u8 = 0;
    v___x_5933_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_trySend___redArg(
        v_ch_5930_, v_v_5931_,
    );
    return v___x_5933_;
}
pub unsafe fn l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_trySend___boxed(
    mut v_00_u03b1_5934_: *mut LeanObject,
    mut v_ch_5935_: *mut LeanObject,
    mut v_v_5936_: *mut LeanObject,
    mut v_a_5937_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5938_: u8 = 0;
    let mut v_r_5939_: *mut LeanObject = core::ptr::null_mut();
    v_res_5938_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_trySend(
        v_00_u03b1_5934_,
        v_ch_5935_,
        v_v_5936_,
    );
    v_r_5939_ = lean_box((v_res_5938_) as usize);
    return v_r_5939_;
}
pub unsafe fn l___private_Init_While_0__whileM_erased___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_trySend_spec__0(
    mut v_00_u03b1_5940_: *mut LeanObject,
    mut v_v_5941_: *mut LeanObject,
    mut v_inst_5942_: *mut LeanObject,
    mut v_a_5943_: *mut LeanObject,
    mut v___y_5944_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5946_: *mut LeanObject = core::ptr::null_mut();
    v___x_5946_ = l___private_Init_While_0__whileM_erased___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_trySend_spec__0___redArg(v_v_5941_, v___y_5944_);
    return v___x_5946_;
}
pub unsafe fn l___private_Init_While_0__whileM_erased___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_trySend_spec__0___boxed(
    mut v_00_u03b1_5947_: *mut LeanObject,
    mut v_v_5948_: *mut LeanObject,
    mut v_inst_5949_: *mut LeanObject,
    mut v_a_5950_: *mut LeanObject,
    mut v___y_5951_: *mut LeanObject,
    mut v___y_5952_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5953_: *mut LeanObject = core::ptr::null_mut();
    v_res_5953_ = l___private_Init_While_0__whileM_erased___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_trySend_spec__0(v_00_u03b1_5947_, v_v_5948_, v_inst_5949_, v_a_5950_, v___y_5951_);
    lean_dec(v___y_5951_);
    return v_res_5953_;
}
pub unsafe fn _init_l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_send___redArg___closed__1()
-> *mut LeanObject {
    let mut v___x_5957_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5958_: *mut LeanObject = core::ptr::null_mut();
    v___x_5957_ =
        l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_send___redArg___closed__0;
    v___x_5958_ = lean_task_pure(v___x_5957_);
    return v___x_5958_;
}
pub unsafe fn _init_l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_send___redArg___closed__3()
-> *mut LeanObject {
    let mut v___x_5961_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5962_: *mut LeanObject = core::ptr::null_mut();
    v___x_5961_ =
        l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_send___redArg___closed__2;
    v___x_5962_ = lean_task_pure(v___x_5961_);
    return v___x_5962_;
}
pub unsafe fn l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_send___redArg(
    mut v_ch_5963_: *mut LeanObject,
    mut v_v_5964_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5966_: u8 = 0;
    v___x_5966_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_trySend___redArg(
        v_ch_5963_, v_v_5964_,
    );
    if v___x_5966_ == 0 {
        let mut v___x_5967_: *mut LeanObject = core::ptr::null_mut();
        v___x_5967_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_send___redArg___closed__1), core::ptr::addr_of_mut!(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_send___redArg___closed__1_once), _init_l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_send___redArg___closed__1);
        return v___x_5967_;
    } else {
        let mut v___x_5968_: *mut LeanObject = core::ptr::null_mut();
        v___x_5968_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_send___redArg___closed__3), core::ptr::addr_of_mut!(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_send___redArg___closed__3_once), _init_l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_send___redArg___closed__3);
        return v___x_5968_;
    }
}
pub unsafe fn l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_send___redArg___boxed(
    mut v_ch_5969_: *mut LeanObject,
    mut v_v_5970_: *mut LeanObject,
    mut v_a_5971_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5972_: *mut LeanObject = core::ptr::null_mut();
    v_res_5972_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_send___redArg(
        v_ch_5969_, v_v_5970_,
    );
    return v_res_5972_;
}
pub unsafe fn l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_send(
    mut v_00_u03b1_5973_: *mut LeanObject,
    mut v_ch_5974_: *mut LeanObject,
    mut v_v_5975_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5977_: *mut LeanObject = core::ptr::null_mut();
    v___x_5977_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_send___redArg(
        v_ch_5974_, v_v_5975_,
    );
    return v___x_5977_;
}
pub unsafe fn l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_send___boxed(
    mut v_00_u03b1_5978_: *mut LeanObject,
    mut v_ch_5979_: *mut LeanObject,
    mut v_v_5980_: *mut LeanObject,
    mut v_a_5981_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5982_: *mut LeanObject = core::ptr::null_mut();
    v_res_5982_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_send(
        v_00_u03b1_5978_,
        v_ch_5979_,
        v_v_5980_,
    );
    return v_res_5982_;
}
pub unsafe fn l_Std_Mutex_atomically___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_close_spec__1___redArg(
    mut v_mutex_5983_: *mut LeanObject,
    mut v_k_5984_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_ref_5986_: *mut LeanObject = core::ptr::null_mut();
    let mut v_mutex_5987_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5988_: *mut LeanObject = core::ptr::null_mut();
    let mut v_r_5989_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5990_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5992_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5993_: u8 = 0;
    let mut v___x_5994_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5996_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5997_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5998_: u8 = 0;
    let mut v_a_5999_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6001_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6002_: u8 = 0;
    let mut v___x_6003_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6005_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6006_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6007_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ref_5986_ = lean_ctor_get(v_mutex_5983_, 0);
                lean_inc(v_ref_5986_);
                v_mutex_5987_ = lean_ctor_get(v_mutex_5983_, 1);
                lean_inc(v_mutex_5987_);
                lean_dec_ref(v_mutex_5983_);
                v___x_5988_ = lean_io_basemutex_lock(v_mutex_5987_);
                v_r_5989_ = lean_apply_2(v_k_5984_, v_ref_5986_, lean_box(0));
                if lean_obj_tag(v_r_5989_) == 0 {
                    v_a_5990_ = lean_ctor_get(v_r_5989_, 0);
                    v_isSharedCheck_5998_ = (!lean_is_exclusive(v_r_5989_)) as u8;
                    if v_isSharedCheck_5998_ == 0 {
                        v___x_5992_ = v_r_5989_;
                        v_isShared_5993_ = v_isSharedCheck_5998_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_5990_);
                        lean_dec(v_r_5989_);
                        v___x_5992_ = lean_box(0);
                        v_isShared_5993_ = v_isSharedCheck_5998_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_5999_ = lean_ctor_get(v_r_5989_, 0);
                    v_isSharedCheck_6007_ = (!lean_is_exclusive(v_r_5989_)) as u8;
                    if v_isSharedCheck_6007_ == 0 {
                        v___x_6001_ = v_r_5989_;
                        v_isShared_6002_ = v_isSharedCheck_6007_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_5999_);
                        lean_dec(v_r_5989_);
                        v___x_6001_ = lean_box(0);
                        v_isShared_6002_ = v_isSharedCheck_6007_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v___x_5994_ = lean_io_basemutex_unlock(v_mutex_5987_);
                lean_dec(v_mutex_5987_);
                if v_isShared_5993_ == 0 {
                    v___x_5996_ = v___x_5992_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_5997_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5997_, 0, v_a_5990_);
                    v___x_5996_ = v_reuseFailAlloc_5997_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_5996_;
            }
            3 => {
                v___x_6003_ = lean_io_basemutex_unlock(v_mutex_5987_);
                lean_dec(v_mutex_5987_);
                if v_isShared_6002_ == 0 {
                    v___x_6005_ = v___x_6001_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_6006_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6006_, 0, v_a_5999_);
                    v___x_6005_ = v_reuseFailAlloc_6006_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_6005_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Mutex_atomically___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_close_spec__1___redArg___boxed(
    mut v_mutex_6008_: *mut LeanObject,
    mut v_k_6009_: *mut LeanObject,
    mut v___y_6010_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6011_: *mut LeanObject = core::ptr::null_mut();
    v_res_6011_ = l_Std_Mutex_atomically___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_close_spec__1___redArg(v_mutex_6008_, v_k_6009_);
    return v_res_6011_;
}
pub unsafe fn l_Std_Mutex_atomically___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_close_spec__1(
    mut v_00_u03b1_6012_: *mut LeanObject,
    mut v_00_u03b2_6013_: *mut LeanObject,
    mut v_mutex_6014_: *mut LeanObject,
    mut v_k_6015_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6017_: *mut LeanObject = core::ptr::null_mut();
    v___x_6017_ = l_Std_Mutex_atomically___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_close_spec__1___redArg(v_mutex_6014_, v_k_6015_);
    return v___x_6017_;
}
pub unsafe fn l_Std_Mutex_atomically___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_close_spec__1___boxed(
    mut v_00_u03b1_6018_: *mut LeanObject,
    mut v_00_u03b2_6019_: *mut LeanObject,
    mut v_mutex_6020_: *mut LeanObject,
    mut v_k_6021_: *mut LeanObject,
    mut v___y_6022_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6023_: *mut LeanObject = core::ptr::null_mut();
    v_res_6023_ = l_Std_Mutex_atomically___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_close_spec__1(v_00_u03b1_6018_, v_00_u03b2_6019_, v_mutex_6020_, v_k_6021_);
    return v_res_6023_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_close_spec__0___redArg(
    mut v_as_6024_: *mut LeanObject,
    mut v_sz_6025_: usize,
    mut v_i_6026_: usize,
    mut v_b_6027_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6029_: u8 = 0;
    let mut v___x_6030_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6031_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6032_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6033_: u8 = 0;
    let mut v___x_6034_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6035_: usize = 0;
    let mut v___x_6036_: usize = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_6029_ = lean_usize_dec_lt(v_i_6026_, v_sz_6025_);
                if v___x_6029_ == 0 {
                    v___x_6030_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_6030_, 0, v_b_6027_);
                    return v___x_6030_;
                } else {
                    v_a_6031_ = lean_array_uget_borrowed(v_as_6024_, v_i_6026_);
                    v___x_6032_ = lean_box(0);
                    v___x_6033_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Consumer_resolve___redArg(v_a_6031_, v___x_6032_);
                    v___x_6034_ = lean_box(0);
                    v___x_6035_ = 1usize;
                    v___x_6036_ = lean_usize_add(v_i_6026_, v___x_6035_);
                    v_i_6026_ = v___x_6036_;
                    v_b_6027_ = v___x_6034_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_close_spec__0___redArg___boxed(
    mut v_as_6038_: *mut LeanObject,
    mut v_sz_6039_: *mut LeanObject,
    mut v_i_6040_: *mut LeanObject,
    mut v_b_6041_: *mut LeanObject,
    mut v___y_6042_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sz_boxed_6043_: usize = 0;
    let mut v_i_boxed_6044_: usize = 0;
    let mut v_res_6045_: *mut LeanObject = core::ptr::null_mut();
    v_sz_boxed_6043_ = lean_unbox_usize(v_sz_6039_);
    lean_dec(v_sz_6039_);
    v_i_boxed_6044_ = lean_unbox_usize(v_i_6040_);
    lean_dec(v_i_6040_);
    v_res_6045_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_close_spec__0___redArg(v_as_6038_, v_sz_boxed_6043_, v_i_boxed_6044_, v_b_6041_);
    lean_dec_ref(v_as_6038_);
    return v_res_6045_;
}
pub unsafe fn _init_l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_close___redArg___lam__0___closed__0()
-> *mut LeanObject {
    let mut v___x_6046_: *mut LeanObject = core::ptr::null_mut();
    v___x_6046_ = l_Std_Queue_empty(lean_box(0));
    return v___x_6046_;
}
pub unsafe fn l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_close___redArg___lam__0(
    mut v___y_6047_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6049_: *mut LeanObject = core::ptr::null_mut();
    let mut v_closed_6050_: u8 = 0;
    let mut v_values_6051_: *mut LeanObject = core::ptr::null_mut();
    let mut v_consumers_6052_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6054_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6055_: u8 = 0;
    let mut v___x_6056_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6057_: *mut LeanObject = core::ptr::null_mut();
    let mut v_sz_6058_: usize = 0;
    let mut v___x_6059_: usize = 0;
    let mut v___x_6060_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6062_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6063_: u8 = 0;
    let mut v___x_6064_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6065_: u8 = 0;
    let mut v___x_6067_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6068_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6070_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6071_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6072_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6073_: u8 = 0;
    let mut v_unused_6074_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6075_: u8 = 0;
    let mut v___x_6076_: u8 = 0;
    let mut v___x_6077_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6078_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_6049_ = lean_st_ref_get(v___y_6047_);
                v_closed_6050_ = lean_ctor_get_uint8(
                    v___x_6049_,
                    (core::mem::size_of::<*mut LeanObject>() * 2) as u32,
                );
                if v_closed_6050_ == 0 {
                    v_values_6051_ = lean_ctor_get(v___x_6049_, 0);
                    v_consumers_6052_ = lean_ctor_get(v___x_6049_, 1);
                    v_isSharedCheck_6075_ = (!lean_is_exclusive(v___x_6049_)) as u8;
                    if v_isSharedCheck_6075_ == 0 {
                        v___x_6054_ = v___x_6049_;
                        v_isShared_6055_ = v_isSharedCheck_6075_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_consumers_6052_);
                        lean_inc(v_values_6051_);
                        lean_dec(v___x_6049_);
                        v___x_6054_ = lean_box(0);
                        v_isShared_6055_ = v_isSharedCheck_6075_;
                        state = 1;
                        continue;
                    }
                } else {
                    lean_dec(v___x_6049_);
                    v___x_6076_ = 1;
                    v___x_6077_ = lean_box((v___x_6076_) as usize);
                    v___x_6078_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v___x_6078_, 0, v___x_6077_);
                    return v___x_6078_;
                }
            }
            1 => {
                v___x_6056_ = l_Std_Queue_toArray___redArg(v_consumers_6052_);
                v___x_6057_ = lean_box(0);
                v_sz_6058_ = lean_array_size(v___x_6056_);
                v___x_6059_ = 0usize;
                v___x_6060_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_close_spec__0___redArg(v___x_6056_, v_sz_6058_, v___x_6059_, v___x_6057_);
                lean_dec_ref(v___x_6056_);
                if lean_obj_tag(v___x_6060_) == 0 {
                    v_isSharedCheck_6073_ = (!lean_is_exclusive(v___x_6060_)) as u8;
                    if v_isSharedCheck_6073_ == 0 {
                        v_unused_6074_ = lean_ctor_get(v___x_6060_, 0);
                        lean_dec(v_unused_6074_);
                        v___x_6062_ = v___x_6060_;
                        v_isShared_6063_ = v_isSharedCheck_6073_;
                        state = 2;
                        continue;
                    } else {
                        lean_dec(v___x_6060_);
                        v___x_6062_ = lean_box(0);
                        v_isShared_6063_ = v_isSharedCheck_6073_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_6054_);
                    lean_dec_ref(v_values_6051_);
                    return v___x_6060_;
                }
            }
            2 => {
                v___x_6064_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_close___redArg___lam__0___closed__0), core::ptr::addr_of_mut!(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_close___redArg___lam__0___closed__0_once), _init_l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_close___redArg___lam__0___closed__0);
                v___x_6065_ = 1;
                if v_isShared_6055_ == 0 {
                    lean_ctor_set(v___x_6054_, 1, v___x_6064_);
                    v___x_6067_ = v___x_6054_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_6072_ = lean_alloc_ctor(0, 2, (1) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6072_, 0, v_values_6051_);
                    lean_ctor_set(v_reuseFailAlloc_6072_, 1, v___x_6064_);
                    v___x_6067_ = v_reuseFailAlloc_6072_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                lean_ctor_set_uint8(
                    v___x_6067_,
                    (core::mem::size_of::<*mut LeanObject>() * 2) as u32,
                    v___x_6065_,
                );
                v___x_6068_ = lean_st_ref_set(v___y_6047_, v___x_6067_);
                if v_isShared_6063_ == 0 {
                    lean_ctor_set(v___x_6062_, 0, v___x_6057_);
                    v___x_6070_ = v___x_6062_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_6071_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6071_, 0, v___x_6057_);
                    v___x_6070_ = v_reuseFailAlloc_6071_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_6070_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_close___redArg___lam__0___boxed(
    mut v___y_6079_: *mut LeanObject,
    mut v___y_6080_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6081_: *mut LeanObject = core::ptr::null_mut();
    v_res_6081_ =
        l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_close___redArg___lam__0(
            v___y_6079_,
        );
    lean_dec(v___y_6079_);
    return v_res_6081_;
}
pub unsafe fn l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_close___redArg(
    mut v_ch_6083_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_6085_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6086_: *mut LeanObject = core::ptr::null_mut();
    v___f_6085_ =
        l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_close___redArg___closed__0;
    v___x_6086_ = l_Std_Mutex_atomically___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_close_spec__1___redArg(v_ch_6083_, v___f_6085_);
    return v___x_6086_;
}
pub unsafe fn l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_close___redArg___boxed(
    mut v_ch_6087_: *mut LeanObject,
    mut v_a_6088_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6089_: *mut LeanObject = core::ptr::null_mut();
    v_res_6089_ =
        l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_close___redArg(v_ch_6087_);
    return v_res_6089_;
}
pub unsafe fn l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_close(
    mut v_00_u03b1_6090_: *mut LeanObject,
    mut v_ch_6091_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6093_: *mut LeanObject = core::ptr::null_mut();
    v___x_6093_ =
        l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_close___redArg(v_ch_6091_);
    return v___x_6093_;
}
pub unsafe fn l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_close___boxed(
    mut v_00_u03b1_6094_: *mut LeanObject,
    mut v_ch_6095_: *mut LeanObject,
    mut v_a_6096_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6097_: *mut LeanObject = core::ptr::null_mut();
    v_res_6097_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_close(
        v_00_u03b1_6094_,
        v_ch_6095_,
    );
    return v_res_6097_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_close_spec__0(
    mut v_00_u03b1_6098_: *mut LeanObject,
    mut v_as_6099_: *mut LeanObject,
    mut v_sz_6100_: usize,
    mut v_i_6101_: usize,
    mut v_b_6102_: *mut LeanObject,
    mut v___y_6103_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6105_: *mut LeanObject = core::ptr::null_mut();
    v___x_6105_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_close_spec__0___redArg(v_as_6099_, v_sz_6100_, v_i_6101_, v_b_6102_);
    return v___x_6105_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_close_spec__0___boxed(
    mut v_00_u03b1_6106_: *mut LeanObject,
    mut v_as_6107_: *mut LeanObject,
    mut v_sz_6108_: *mut LeanObject,
    mut v_i_6109_: *mut LeanObject,
    mut v_b_6110_: *mut LeanObject,
    mut v___y_6111_: *mut LeanObject,
    mut v___y_6112_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sz_boxed_6113_: usize = 0;
    let mut v_i_boxed_6114_: usize = 0;
    let mut v_res_6115_: *mut LeanObject = core::ptr::null_mut();
    v_sz_boxed_6113_ = lean_unbox_usize(v_sz_6108_);
    lean_dec(v_sz_6108_);
    v_i_boxed_6114_ = lean_unbox_usize(v_i_6109_);
    lean_dec(v_i_6109_);
    v_res_6115_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_close_spec__0(v_00_u03b1_6106_, v_as_6107_, v_sz_boxed_6113_, v_i_boxed_6114_, v_b_6110_, v___y_6111_);
    lean_dec(v___y_6111_);
    lean_dec_ref(v_as_6107_);
    return v_res_6115_;
}
pub unsafe fn l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_isClosed___redArg___lam__0(
    mut v___y_6116_: *mut LeanObject,
) -> u8 {
    let mut v___x_6118_: *mut LeanObject = core::ptr::null_mut();
    let mut v_closed_6119_: u8 = 0;
    v___x_6118_ = lean_st_ref_get(v___y_6116_);
    v_closed_6119_ = lean_ctor_get_uint8(
        v___x_6118_,
        (core::mem::size_of::<*mut LeanObject>() * 2) as u32,
    );
    lean_dec(v___x_6118_);
    return v_closed_6119_;
}
pub unsafe fn l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_isClosed___redArg___lam__0___boxed(
    mut v___y_6120_: *mut LeanObject,
    mut v___y_6121_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6122_: u8 = 0;
    let mut v_r_6123_: *mut LeanObject = core::ptr::null_mut();
    v_res_6122_ =
        l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_isClosed___redArg___lam__0(
            v___y_6120_,
        );
    lean_dec(v___y_6120_);
    v_r_6123_ = lean_box((v_res_6122_) as usize);
    return v_r_6123_;
}
pub unsafe fn l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_isClosed___redArg(
    mut v_ch_6125_: *mut LeanObject,
) -> u8 {
    let mut v___f_6127_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6128_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6129_: u8 = 0;
    v___f_6127_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_isClosed___redArg___closed__0;
    v___x_6128_ = l_Std_Mutex_atomically___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_trySend_spec__1___redArg(v_ch_6125_, v___f_6127_);
    v___x_6129_ = (lean_unbox(v___x_6128_) as u8);
    lean_dec(v___x_6128_);
    return v___x_6129_;
}
pub unsafe fn l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_isClosed___redArg___boxed(
    mut v_ch_6130_: *mut LeanObject,
    mut v_a_6131_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6132_: u8 = 0;
    let mut v_r_6133_: *mut LeanObject = core::ptr::null_mut();
    v_res_6132_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_isClosed___redArg(
        v_ch_6130_,
    );
    v_r_6133_ = lean_box((v_res_6132_) as usize);
    return v_r_6133_;
}
pub unsafe fn l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_isClosed(
    mut v_00_u03b1_6134_: *mut LeanObject,
    mut v_ch_6135_: *mut LeanObject,
) -> u8 {
    let mut v___x_6137_: u8 = 0;
    v___x_6137_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_isClosed___redArg(
        v_ch_6135_,
    );
    return v___x_6137_;
}
pub unsafe fn l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_isClosed___boxed(
    mut v_00_u03b1_6138_: *mut LeanObject,
    mut v_ch_6139_: *mut LeanObject,
    mut v_a_6140_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6141_: u8 = 0;
    let mut v_r_6142_: *mut LeanObject = core::ptr::null_mut();
    v_res_6141_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_isClosed(
        v_00_u03b1_6138_,
        v_ch_6139_,
    );
    v_r_6142_ = lean_box((v_res_6141_) as usize);
    return v_r_6142_;
}
pub unsafe fn l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_tryRecv_x27___redArg___lam__0(
    mut v_toApplicative_6143_: *mut LeanObject,
    mut v_fst_6144_: *mut LeanObject,
    mut v_a_6145_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toPure_6146_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6147_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6148_: *mut LeanObject = core::ptr::null_mut();
    v_toPure_6146_ = lean_ctor_get(v_toApplicative_6143_, 1);
    lean_inc(v_toPure_6146_);
    lean_dec_ref(v_toApplicative_6143_);
    v___x_6147_ = lean_alloc_ctor(1, 1, (0) as u32);
    lean_ctor_set(v___x_6147_, 0, v_fst_6144_);
    v___x_6148_ = lean_apply_2(v_toPure_6146_, lean_box(0), v___x_6147_);
    return v___x_6148_;
}
pub unsafe fn l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_tryRecv_x27___redArg___lam__1(
    mut v_toApplicative_6149_: *mut LeanObject,
    mut v_a_6150_: *mut LeanObject,
    mut v_inst_6151_: *mut LeanObject,
    mut v_toBind_6152_: *mut LeanObject,
    mut v_a_6153_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_values_6154_: *mut LeanObject = core::ptr::null_mut();
    let mut v_consumers_6155_: *mut LeanObject = core::ptr::null_mut();
    let mut v_closed_6156_: u8 = 0;
    let mut v___x_6158_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6159_: u8 = 0;
    let mut v___x_6160_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_6161_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_6162_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_6163_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_6164_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6166_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6167_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6168_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6169_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6170_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toPure_6171_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6172_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6173_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6174_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_values_6154_ = lean_ctor_get(v_a_6153_, 0);
                v_consumers_6155_ = lean_ctor_get(v_a_6153_, 1);
                v_closed_6156_ = lean_ctor_get_uint8(
                    v_a_6153_,
                    (core::mem::size_of::<*mut LeanObject>() * 2) as u32,
                );
                v_isSharedCheck_6174_ = (!lean_is_exclusive(v_a_6153_)) as u8;
                if v_isSharedCheck_6174_ == 0 {
                    v___x_6158_ = v_a_6153_;
                    v_isShared_6159_ = v_isSharedCheck_6174_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_consumers_6155_);
                    lean_inc(v_values_6154_);
                    lean_dec(v_a_6153_);
                    v___x_6158_ = lean_box(0);
                    v_isShared_6159_ = v_isSharedCheck_6174_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_6160_ = l_Std_Queue_dequeue_x3f___redArg(v_values_6154_);
                if lean_obj_tag(v___x_6160_) == 1 {
                    v_val_6161_ = lean_ctor_get(v___x_6160_, 0);
                    lean_inc(v_val_6161_);
                    lean_dec_ref_known(v___x_6160_, 1);
                    v_fst_6162_ = lean_ctor_get(v_val_6161_, 0);
                    lean_inc(v_fst_6162_);
                    v_snd_6163_ = lean_ctor_get(v_val_6161_, 1);
                    lean_inc(v_snd_6163_);
                    lean_dec(v_val_6161_);
                    v___f_6164_ = lean_alloc_closure(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_tryRecv_x27___redArg___lam__0 as *mut core::ffi::c_void, 3, 2);
                    lean_closure_set(v___f_6164_, 0, v_toApplicative_6149_);
                    lean_closure_set(v___f_6164_, 1, v_fst_6162_);
                    if v_isShared_6159_ == 0 {
                        lean_ctor_set(v___x_6158_, 0, v_snd_6163_);
                        v___x_6166_ = v___x_6158_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_6170_ = lean_alloc_ctor(0, 2, (1) as u32);
                        lean_ctor_set(v_reuseFailAlloc_6170_, 0, v_snd_6163_);
                        lean_ctor_set(v_reuseFailAlloc_6170_, 1, v_consumers_6155_);
                        lean_ctor_set_uint8(
                            v_reuseFailAlloc_6170_,
                            (core::mem::size_of::<*mut LeanObject>() * 2) as u32,
                            v_closed_6156_,
                        );
                        v___x_6166_ = v_reuseFailAlloc_6170_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_dec(v___x_6160_);
                    lean_del_object(v___x_6158_);
                    lean_dec_ref(v_consumers_6155_);
                    lean_dec(v_toBind_6152_);
                    lean_dec(v_inst_6151_);
                    v_toPure_6171_ = lean_ctor_get(v_toApplicative_6149_, 1);
                    lean_inc(v_toPure_6171_);
                    lean_dec_ref(v_toApplicative_6149_);
                    v___x_6172_ = lean_box(0);
                    v___x_6173_ = lean_apply_2(v_toPure_6171_, lean_box(0), v___x_6172_);
                    return v___x_6173_;
                }
            }
            2 => {
                lean_inc(v_a_6150_);
                v___x_6167_ =
                    lean_alloc_closure(l_ST_Prim_Ref_set___boxed as *mut core::ffi::c_void, 5, 4);
                lean_closure_set(v___x_6167_, 0, lean_box(0));
                lean_closure_set(v___x_6167_, 1, lean_box(0));
                lean_closure_set(v___x_6167_, 2, v_a_6150_);
                lean_closure_set(v___x_6167_, 3, v___x_6166_);
                v___x_6168_ = lean_apply_2(v_inst_6151_, lean_box(0), v___x_6167_);
                v___x_6169_ = lean_apply_4(
                    v_toBind_6152_,
                    lean_box(0),
                    lean_box(0),
                    v___x_6168_,
                    v___f_6164_,
                );
                return v___x_6169_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_tryRecv_x27___redArg___lam__1___boxed(
    mut v_toApplicative_6175_: *mut LeanObject,
    mut v_a_6176_: *mut LeanObject,
    mut v_inst_6177_: *mut LeanObject,
    mut v_toBind_6178_: *mut LeanObject,
    mut v_a_6179_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6180_: *mut LeanObject = core::ptr::null_mut();
    v_res_6180_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_tryRecv_x27___redArg___lam__1(v_toApplicative_6175_, v_a_6176_, v_inst_6177_, v_toBind_6178_, v_a_6179_);
    lean_dec(v_a_6176_);
    return v_res_6180_;
}
pub unsafe fn l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_tryRecv_x27___redArg(
    mut v_inst_6181_: *mut LeanObject,
    mut v_inst_6182_: *mut LeanObject,
    mut v_a_6183_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toApplicative_6184_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toBind_6185_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_6186_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6187_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6188_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6189_: *mut LeanObject = core::ptr::null_mut();
    v_toApplicative_6184_ = lean_ctor_get(v_inst_6181_, 0);
    lean_inc_ref(v_toApplicative_6184_);
    v_toBind_6185_ = lean_ctor_get(v_inst_6181_, 1);
    lean_inc_n(v_toBind_6185_, 2);
    lean_dec_ref(v_inst_6181_);
    lean_inc(v_inst_6182_);
    lean_inc_n(v_a_6183_, 2);
    v___f_6186_ = lean_alloc_closure(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_tryRecv_x27___redArg___lam__1___boxed as *mut core::ffi::c_void, 5, 4);
    lean_closure_set(v___f_6186_, 0, v_toApplicative_6184_);
    lean_closure_set(v___f_6186_, 1, v_a_6183_);
    lean_closure_set(v___f_6186_, 2, v_inst_6182_);
    lean_closure_set(v___f_6186_, 3, v_toBind_6185_);
    v___x_6187_ = lean_alloc_closure(l_ST_Prim_Ref_get___boxed as *mut core::ffi::c_void, 4, 3);
    lean_closure_set(v___x_6187_, 0, lean_box(0));
    lean_closure_set(v___x_6187_, 1, lean_box(0));
    lean_closure_set(v___x_6187_, 2, v_a_6183_);
    v___x_6188_ = lean_apply_2(v_inst_6182_, lean_box(0), v___x_6187_);
    v___x_6189_ = lean_apply_4(
        v_toBind_6185_,
        lean_box(0),
        lean_box(0),
        v___x_6188_,
        v___f_6186_,
    );
    return v___x_6189_;
}
pub unsafe fn l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_tryRecv_x27___redArg___boxed(
    mut v_inst_6190_: *mut LeanObject,
    mut v_inst_6191_: *mut LeanObject,
    mut v_a_6192_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6193_: *mut LeanObject = core::ptr::null_mut();
    v_res_6193_ =
        l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_tryRecv_x27___redArg(
            v_inst_6190_,
            v_inst_6191_,
            v_a_6192_,
        );
    lean_dec(v_a_6192_);
    return v_res_6193_;
}
pub unsafe fn l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_tryRecv_x27(
    mut v_m_6194_: *mut LeanObject,
    mut v_00_u03b1_6195_: *mut LeanObject,
    mut v_inst_6196_: *mut LeanObject,
    mut v_inst_6197_: *mut LeanObject,
    mut v_a_6198_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6199_: *mut LeanObject = core::ptr::null_mut();
    v___x_6199_ =
        l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_tryRecv_x27___redArg(
            v_inst_6196_,
            v_inst_6197_,
            v_a_6198_,
        );
    return v___x_6199_;
}
pub unsafe fn l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_tryRecv_x27___boxed(
    mut v_m_6200_: *mut LeanObject,
    mut v_00_u03b1_6201_: *mut LeanObject,
    mut v_inst_6202_: *mut LeanObject,
    mut v_inst_6203_: *mut LeanObject,
    mut v_a_6204_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6205_: *mut LeanObject = core::ptr::null_mut();
    v_res_6205_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_tryRecv_x27(
        v_m_6200_,
        v_00_u03b1_6201_,
        v_inst_6202_,
        v_inst_6203_,
        v_a_6204_,
    );
    lean_dec(v_a_6204_);
    return v_res_6205_;
}
pub unsafe fn l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_tryRecv_spec__0___redArg(
    mut v_a_6206_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6208_: *mut LeanObject = core::ptr::null_mut();
    let mut v_values_6209_: *mut LeanObject = core::ptr::null_mut();
    let mut v_consumers_6210_: *mut LeanObject = core::ptr::null_mut();
    let mut v_closed_6211_: u8 = 0;
    let mut v___x_6213_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6214_: u8 = 0;
    let mut v___x_6215_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_6216_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6218_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6219_: u8 = 0;
    let mut v_fst_6220_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_6221_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6223_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6224_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6226_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6227_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6228_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6229_: u8 = 0;
    let mut v___x_6230_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6231_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_6208_ = lean_st_ref_get(v_a_6206_);
                v_values_6209_ = lean_ctor_get(v___x_6208_, 0);
                v_consumers_6210_ = lean_ctor_get(v___x_6208_, 1);
                v_closed_6211_ = lean_ctor_get_uint8(
                    v___x_6208_,
                    (core::mem::size_of::<*mut LeanObject>() * 2) as u32,
                );
                v_isSharedCheck_6231_ = (!lean_is_exclusive(v___x_6208_)) as u8;
                if v_isSharedCheck_6231_ == 0 {
                    v___x_6213_ = v___x_6208_;
                    v_isShared_6214_ = v_isSharedCheck_6231_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_consumers_6210_);
                    lean_inc(v_values_6209_);
                    lean_dec(v___x_6208_);
                    v___x_6213_ = lean_box(0);
                    v_isShared_6214_ = v_isSharedCheck_6231_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_6215_ = l_Std_Queue_dequeue_x3f___redArg(v_values_6209_);
                if lean_obj_tag(v___x_6215_) == 1 {
                    v_val_6216_ = lean_ctor_get(v___x_6215_, 0);
                    v_isSharedCheck_6229_ = (!lean_is_exclusive(v___x_6215_)) as u8;
                    if v_isSharedCheck_6229_ == 0 {
                        v___x_6218_ = v___x_6215_;
                        v_isShared_6219_ = v_isSharedCheck_6229_;
                        state = 2;
                        continue;
                    } else {
                        lean_inc(v_val_6216_);
                        lean_dec(v___x_6215_);
                        v___x_6218_ = lean_box(0);
                        v_isShared_6219_ = v_isSharedCheck_6229_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_dec(v___x_6215_);
                    lean_del_object(v___x_6213_);
                    lean_dec_ref(v_consumers_6210_);
                    v___x_6230_ = lean_box(0);
                    return v___x_6230_;
                }
            }
            2 => {
                v_fst_6220_ = lean_ctor_get(v_val_6216_, 0);
                lean_inc(v_fst_6220_);
                v_snd_6221_ = lean_ctor_get(v_val_6216_, 1);
                lean_inc(v_snd_6221_);
                lean_dec(v_val_6216_);
                if v_isShared_6214_ == 0 {
                    lean_ctor_set(v___x_6213_, 0, v_snd_6221_);
                    v___x_6223_ = v___x_6213_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_6228_ = lean_alloc_ctor(0, 2, (1) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6228_, 0, v_snd_6221_);
                    lean_ctor_set(v_reuseFailAlloc_6228_, 1, v_consumers_6210_);
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_6228_,
                        (core::mem::size_of::<*mut LeanObject>() * 2) as u32,
                        v_closed_6211_,
                    );
                    v___x_6223_ = v_reuseFailAlloc_6228_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_6224_ = lean_st_ref_set(v_a_6206_, v___x_6223_);
                if v_isShared_6219_ == 0 {
                    lean_ctor_set(v___x_6218_, 0, v_fst_6220_);
                    v___x_6226_ = v___x_6218_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_6227_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6227_, 0, v_fst_6220_);
                    v___x_6226_ = v_reuseFailAlloc_6227_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_6226_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_tryRecv_spec__0___redArg___boxed(
    mut v_a_6232_: *mut LeanObject,
    mut v___y_6233_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6234_: *mut LeanObject = core::ptr::null_mut();
    v_res_6234_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_tryRecv_spec__0___redArg(v_a_6232_);
    lean_dec(v_a_6232_);
    return v_res_6234_;
}
pub unsafe fn l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_tryRecv_spec__0(
    mut v_00_u03b1_6235_: *mut LeanObject,
    mut v_a_6236_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6238_: *mut LeanObject = core::ptr::null_mut();
    v___x_6238_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_tryRecv_spec__0___redArg(v_a_6236_);
    return v___x_6238_;
}
pub unsafe fn l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_tryRecv_spec__0___boxed(
    mut v_00_u03b1_6239_: *mut LeanObject,
    mut v_a_6240_: *mut LeanObject,
    mut v___y_6241_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6242_: *mut LeanObject = core::ptr::null_mut();
    v_res_6242_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_tryRecv_spec__0(v_00_u03b1_6239_, v_a_6240_);
    lean_dec(v_a_6240_);
    return v_res_6242_;
}
pub unsafe fn l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_tryRecv___redArg(
    mut v_ch_6244_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_6246_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6247_: *mut LeanObject = core::ptr::null_mut();
    v___f_6246_ =
        l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_tryRecv___redArg___closed__0;
    v___x_6247_ = l_Std_Mutex_atomically___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_trySend_spec__1___redArg(v_ch_6244_, v___f_6246_);
    return v___x_6247_;
}
pub unsafe fn l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_tryRecv___redArg___boxed(
    mut v_ch_6248_: *mut LeanObject,
    mut v_a_6249_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6250_: *mut LeanObject = core::ptr::null_mut();
    v_res_6250_ =
        l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_tryRecv___redArg(v_ch_6248_);
    return v_res_6250_;
}
pub unsafe fn l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_tryRecv(
    mut v_00_u03b1_6251_: *mut LeanObject,
    mut v_ch_6252_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6254_: *mut LeanObject = core::ptr::null_mut();
    v___x_6254_ =
        l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_tryRecv___redArg(v_ch_6252_);
    return v___x_6254_;
}
pub unsafe fn l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_tryRecv___boxed(
    mut v_00_u03b1_6255_: *mut LeanObject,
    mut v_ch_6256_: *mut LeanObject,
    mut v_a_6257_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6258_: *mut LeanObject = core::ptr::null_mut();
    v_res_6258_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_tryRecv(
        v_00_u03b1_6255_,
        v_ch_6256_,
    );
    return v_res_6258_;
}
pub unsafe fn l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recv___redArg___lam__0(
    mut v_x_6259_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_6259_) == 0 {
        let mut v___x_6260_: *mut LeanObject = core::ptr::null_mut();
        v___x_6260_ = lean_box(0);
        return v___x_6260_;
    } else {
        let mut v_val_6261_: *mut LeanObject = core::ptr::null_mut();
        v_val_6261_ = lean_ctor_get(v_x_6259_, 0);
        lean_inc(v_val_6261_);
        return v_val_6261_;
    }
}
pub unsafe fn l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recv___redArg___lam__0___boxed(
    mut v_x_6262_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6263_: *mut LeanObject = core::ptr::null_mut();
    v_res_6263_ =
        l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recv___redArg___lam__0(
            v_x_6262_,
        );
    lean_dec(v_x_6262_);
    return v_res_6263_;
}
pub unsafe fn _init_l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recv___redArg___lam__1___closed__0()
-> *mut LeanObject {
    let mut v___x_6264_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6265_: *mut LeanObject = core::ptr::null_mut();
    v___x_6264_ = lean_box(0);
    v___x_6265_ = lean_task_pure(v___x_6264_);
    return v___x_6265_;
}
pub unsafe fn l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recv___redArg___lam__1(
    mut v___f_6266_: *mut LeanObject,
    mut v___y_6267_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6269_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6270_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6271_: *mut LeanObject = core::ptr::null_mut();
    let mut v_closed_6272_: u8 = 0;
    let mut v___x_6273_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6274_: *mut LeanObject = core::ptr::null_mut();
    let mut v_values_6275_: *mut LeanObject = core::ptr::null_mut();
    let mut v_consumers_6276_: *mut LeanObject = core::ptr::null_mut();
    let mut v_closed_6277_: u8 = 0;
    let mut v___x_6279_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6280_: u8 = 0;
    let mut v___x_6281_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6282_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6284_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6285_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6286_: u8 = 0;
    let mut v___x_6287_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6288_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6289_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6290_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6291_: u8 = 0;
    let mut v___x_6292_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_6269_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_tryRecv_spec__0___redArg(v___y_6267_);
                if lean_obj_tag(v___x_6269_) == 1 {
                    lean_dec_ref(v___f_6266_);
                    v___x_6270_ = lean_task_pure(v___x_6269_);
                    return v___x_6270_;
                } else {
                    lean_dec(v___x_6269_);
                    v___x_6271_ = lean_st_ref_get(v___y_6267_);
                    v_closed_6272_ = lean_ctor_get_uint8(
                        v___x_6271_,
                        (core::mem::size_of::<*mut LeanObject>() * 2) as u32,
                    );
                    lean_dec(v___x_6271_);
                    if v_closed_6272_ == 0 {
                        v___x_6273_ = lean_io_promise_new();
                        v___x_6274_ = lean_st_ref_take(v___y_6267_);
                        v_values_6275_ = lean_ctor_get(v___x_6274_, 0);
                        v_consumers_6276_ = lean_ctor_get(v___x_6274_, 1);
                        v_closed_6277_ = lean_ctor_get_uint8(
                            v___x_6274_,
                            (core::mem::size_of::<*mut LeanObject>() * 2) as u32,
                        );
                        v_isSharedCheck_6291_ = (!lean_is_exclusive(v___x_6274_)) as u8;
                        if v_isSharedCheck_6291_ == 0 {
                            v___x_6279_ = v___x_6274_;
                            v_isShared_6280_ = v_isSharedCheck_6291_;
                            state = 1;
                            continue;
                        } else {
                            lean_inc(v_consumers_6276_);
                            lean_inc(v_values_6275_);
                            lean_dec(v___x_6274_);
                            v___x_6279_ = lean_box(0);
                            v_isShared_6280_ = v_isSharedCheck_6291_;
                            state = 1;
                            continue;
                        }
                    } else {
                        lean_dec_ref(v___f_6266_);
                        v___x_6292_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recv___redArg___lam__1___closed__0), core::ptr::addr_of_mut!(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recv___redArg___lam__1___closed__0_once), _init_l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recv___redArg___lam__1___closed__0);
                        return v___x_6292_;
                    }
                }
            }
            1 => {
                lean_inc(v___x_6273_);
                v___x_6281_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_6281_, 0, v___x_6273_);
                v___x_6282_ = l_Std_Queue_enqueue___redArg(v___x_6281_, v_consumers_6276_);
                if v_isShared_6280_ == 0 {
                    lean_ctor_set(v___x_6279_, 1, v___x_6282_);
                    v___x_6284_ = v___x_6279_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_6290_ = lean_alloc_ctor(0, 2, (1) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6290_, 0, v_values_6275_);
                    lean_ctor_set(v_reuseFailAlloc_6290_, 1, v___x_6282_);
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_6290_,
                        (core::mem::size_of::<*mut LeanObject>() * 2) as u32,
                        v_closed_6277_,
                    );
                    v___x_6284_ = v_reuseFailAlloc_6290_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_6285_ = lean_st_ref_set(v___y_6267_, v___x_6284_);
                v___x_6286_ = 1;
                v___x_6287_ = lean_io_promise_result_opt(v___x_6273_);
                lean_dec(v___x_6273_);
                v___x_6288_ = lean_unsigned_to_nat(0);
                v___x_6289_ = lean_task_map(v___f_6266_, v___x_6287_, v___x_6288_, v___x_6286_);
                return v___x_6289_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recv___redArg___lam__1___boxed(
    mut v___f_6293_: *mut LeanObject,
    mut v___y_6294_: *mut LeanObject,
    mut v___y_6295_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6296_: *mut LeanObject = core::ptr::null_mut();
    v_res_6296_ =
        l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recv___redArg___lam__1(
            v___f_6293_,
            v___y_6294_,
        );
    lean_dec(v___y_6294_);
    return v_res_6296_;
}
pub unsafe fn l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recv___redArg(
    mut v_ch_6300_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_6302_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6303_: *mut LeanObject = core::ptr::null_mut();
    v___f_6302_ =
        l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recv___redArg___closed__1;
    v___x_6303_ = l_Std_Mutex_atomically___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_trySend_spec__1___redArg(v_ch_6300_, v___f_6302_);
    return v___x_6303_;
}
pub unsafe fn l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recv___redArg___boxed(
    mut v_ch_6304_: *mut LeanObject,
    mut v_a_6305_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6306_: *mut LeanObject = core::ptr::null_mut();
    v_res_6306_ =
        l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recv___redArg(v_ch_6304_);
    return v_res_6306_;
}
pub unsafe fn l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recv(
    mut v_00_u03b1_6307_: *mut LeanObject,
    mut v_ch_6308_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6310_: *mut LeanObject = core::ptr::null_mut();
    v___x_6310_ =
        l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recv___redArg(v_ch_6308_);
    return v___x_6310_;
}
pub unsafe fn l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recv___boxed(
    mut v_00_u03b1_6311_: *mut LeanObject,
    mut v_ch_6312_: *mut LeanObject,
    mut v_a_6313_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6314_: *mut LeanObject = core::ptr::null_mut();
    v_res_6314_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recv(
        v_00_u03b1_6311_,
        v_ch_6312_,
    );
    return v_res_6314_;
}
pub unsafe fn l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvReady_x27___redArg___lam__0(
    mut v_toApplicative_6315_: *mut LeanObject,
    mut v_a_6316_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___y_6318_: u8 = 0;
    let mut v_toPure_6319_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6320_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6321_: *mut LeanObject = core::ptr::null_mut();
    let mut v_values_6322_: *mut LeanObject = core::ptr::null_mut();
    let mut v_closed_6323_: u8 = 0;
    let mut v___x_6324_: u8 = 0;
    let mut v___x_6325_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_values_6322_ = lean_ctor_get(v_a_6316_, 0);
                v_closed_6323_ = lean_ctor_get_uint8(
                    v_a_6316_,
                    (core::mem::size_of::<*mut LeanObject>() * 2) as u32,
                );
                v___x_6324_ = l_Std_Queue_isEmpty___redArg(v_values_6322_);
                if v___x_6324_ == 0 {
                    v___x_6325_ = 1;
                    v___y_6318_ = v___x_6325_;
                    state = 1;
                    continue;
                } else {
                    v___y_6318_ = v_closed_6323_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_toPure_6319_ = lean_ctor_get(v_toApplicative_6315_, 1);
                lean_inc(v_toPure_6319_);
                lean_dec_ref(v_toApplicative_6315_);
                v___x_6320_ = lean_box((v___y_6318_) as usize);
                v___x_6321_ = lean_apply_2(v_toPure_6319_, lean_box(0), v___x_6320_);
                return v___x_6321_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvReady_x27___redArg___lam__0___boxed(
    mut v_toApplicative_6326_: *mut LeanObject,
    mut v_a_6327_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6328_: *mut LeanObject = core::ptr::null_mut();
    v_res_6328_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvReady_x27___redArg___lam__0(v_toApplicative_6326_, v_a_6327_);
    lean_dec_ref(v_a_6327_);
    return v_res_6328_;
}
pub unsafe fn l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvReady_x27___redArg(
    mut v_inst_6329_: *mut LeanObject,
    mut v_inst_6330_: *mut LeanObject,
    mut v_a_6331_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toApplicative_6332_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toBind_6333_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_6334_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6335_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6336_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6337_: *mut LeanObject = core::ptr::null_mut();
    v_toApplicative_6332_ = lean_ctor_get(v_inst_6329_, 0);
    lean_inc_ref(v_toApplicative_6332_);
    v_toBind_6333_ = lean_ctor_get(v_inst_6329_, 1);
    lean_inc(v_toBind_6333_);
    lean_dec_ref(v_inst_6329_);
    v___f_6334_ = lean_alloc_closure(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvReady_x27___redArg___lam__0___boxed as *mut core::ffi::c_void, 2, 1);
    lean_closure_set(v___f_6334_, 0, v_toApplicative_6332_);
    lean_inc(v_a_6331_);
    v___x_6335_ = lean_alloc_closure(l_ST_Prim_Ref_get___boxed as *mut core::ffi::c_void, 4, 3);
    lean_closure_set(v___x_6335_, 0, lean_box(0));
    lean_closure_set(v___x_6335_, 1, lean_box(0));
    lean_closure_set(v___x_6335_, 2, v_a_6331_);
    v___x_6336_ = lean_apply_2(v_inst_6330_, lean_box(0), v___x_6335_);
    v___x_6337_ = lean_apply_4(
        v_toBind_6333_,
        lean_box(0),
        lean_box(0),
        v___x_6336_,
        v___f_6334_,
    );
    return v___x_6337_;
}
pub unsafe fn l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvReady_x27___redArg___boxed(
    mut v_inst_6338_: *mut LeanObject,
    mut v_inst_6339_: *mut LeanObject,
    mut v_a_6340_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6341_: *mut LeanObject = core::ptr::null_mut();
    v_res_6341_ =
        l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvReady_x27___redArg(
            v_inst_6338_,
            v_inst_6339_,
            v_a_6340_,
        );
    lean_dec(v_a_6340_);
    return v_res_6341_;
}
pub unsafe fn l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvReady_x27(
    mut v_m_6342_: *mut LeanObject,
    mut v_00_u03b1_6343_: *mut LeanObject,
    mut v_inst_6344_: *mut LeanObject,
    mut v_inst_6345_: *mut LeanObject,
    mut v_a_6346_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toApplicative_6347_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toBind_6348_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_6349_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6350_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6351_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6352_: *mut LeanObject = core::ptr::null_mut();
    v_toApplicative_6347_ = lean_ctor_get(v_inst_6344_, 0);
    lean_inc_ref(v_toApplicative_6347_);
    v_toBind_6348_ = lean_ctor_get(v_inst_6344_, 1);
    lean_inc(v_toBind_6348_);
    lean_dec_ref(v_inst_6344_);
    v___f_6349_ = lean_alloc_closure(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvReady_x27___redArg___lam__0___boxed as *mut core::ffi::c_void, 2, 1);
    lean_closure_set(v___f_6349_, 0, v_toApplicative_6347_);
    lean_inc(v_a_6346_);
    v___x_6350_ = lean_alloc_closure(l_ST_Prim_Ref_get___boxed as *mut core::ffi::c_void, 4, 3);
    lean_closure_set(v___x_6350_, 0, lean_box(0));
    lean_closure_set(v___x_6350_, 1, lean_box(0));
    lean_closure_set(v___x_6350_, 2, v_a_6346_);
    v___x_6351_ = lean_apply_2(v_inst_6345_, lean_box(0), v___x_6350_);
    v___x_6352_ = lean_apply_4(
        v_toBind_6348_,
        lean_box(0),
        lean_box(0),
        v___x_6351_,
        v___f_6349_,
    );
    return v___x_6352_;
}
pub unsafe fn l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvReady_x27___boxed(
    mut v_m_6353_: *mut LeanObject,
    mut v_00_u03b1_6354_: *mut LeanObject,
    mut v_inst_6355_: *mut LeanObject,
    mut v_inst_6356_: *mut LeanObject,
    mut v_a_6357_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6358_: *mut LeanObject = core::ptr::null_mut();
    v_res_6358_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvReady_x27(
        v_m_6353_,
        v_00_u03b1_6354_,
        v_inst_6355_,
        v_inst_6356_,
        v_a_6357_,
    );
    lean_dec(v_a_6357_);
    return v_res_6358_;
}
pub unsafe fn l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__0___redArg___lam__0(
    mut v_fst_6359_: *mut LeanObject,
    mut v_x_6360_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_6362_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6364_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6365_: u8 = 0;
    let mut v___x_6367_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6368_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6369_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6370_: u8 = 0;
    let mut v___x_6372_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6373_: u8 = 0;
    let mut v___x_6374_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6376_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6377_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6378_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6379_: u8 = 0;
    let mut v_unused_6380_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_6360_) == 0 {
                    lean_dec(v_fst_6359_);
                    v_a_6362_ = lean_ctor_get(v_x_6360_, 0);
                    v_isSharedCheck_6370_ = (!lean_is_exclusive(v_x_6360_)) as u8;
                    if v_isSharedCheck_6370_ == 0 {
                        v___x_6364_ = v_x_6360_;
                        v_isShared_6365_ = v_isSharedCheck_6370_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_6362_);
                        lean_dec(v_x_6360_);
                        v___x_6364_ = lean_box(0);
                        v_isShared_6365_ = v_isSharedCheck_6370_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_isSharedCheck_6379_ = (!lean_is_exclusive(v_x_6360_)) as u8;
                    if v_isSharedCheck_6379_ == 0 {
                        v_unused_6380_ = lean_ctor_get(v_x_6360_, 0);
                        lean_dec(v_unused_6380_);
                        v___x_6372_ = v_x_6360_;
                        v_isShared_6373_ = v_isSharedCheck_6379_;
                        state = 3;
                        continue;
                    } else {
                        lean_dec(v_x_6360_);
                        v___x_6372_ = lean_box(0);
                        v_isShared_6373_ = v_isSharedCheck_6379_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_6365_ == 0 {
                    v___x_6367_ = v___x_6364_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_6369_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6369_, 0, v_a_6362_);
                    v___x_6367_ = v_reuseFailAlloc_6369_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_6368_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_6368_, 0, v___x_6367_);
                return v___x_6368_;
            }
            3 => {
                v___x_6374_ = lean_alloc_ctor(1, 1, (0) as u32);
                lean_ctor_set(v___x_6374_, 0, v_fst_6359_);
                if v_isShared_6373_ == 0 {
                    lean_ctor_set(v___x_6372_, 0, v___x_6374_);
                    v___x_6376_ = v___x_6372_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_6378_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6378_, 0, v___x_6374_);
                    v___x_6376_ = v_reuseFailAlloc_6378_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_6377_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_6377_, 0, v___x_6376_);
                return v___x_6377_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__0___redArg___lam__0___boxed(
    mut v_fst_6381_: *mut LeanObject,
    mut v_x_6382_: *mut LeanObject,
    mut v___y_6383_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6384_: *mut LeanObject = core::ptr::null_mut();
    v_res_6384_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__0___redArg___lam__0(v_fst_6381_, v_x_6382_);
    return v_res_6384_;
}
pub unsafe fn l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__0___redArg___lam__1(
    mut v_a_6389_: *mut LeanObject,
    mut v_x_6390_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_6392_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6394_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6395_: u8 = 0;
    let mut v___x_6397_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6398_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6399_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6400_: u8 = 0;
    let mut v_a_6401_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6403_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6404_: u8 = 0;
    let mut v_values_6405_: *mut LeanObject = core::ptr::null_mut();
    let mut v_consumers_6406_: *mut LeanObject = core::ptr::null_mut();
    let mut v_closed_6407_: u8 = 0;
    let mut v___x_6409_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6410_: u8 = 0;
    let mut v___x_6411_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_6412_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6414_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6415_: u8 = 0;
    let mut v_fst_6416_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_6417_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6419_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6420_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_6421_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6423_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6425_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6426_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6427_: u8 = 0;
    let mut v___x_6428_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6429_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6430_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6431_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6432_: u8 = 0;
    let mut v___x_6433_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6434_: u8 = 0;
    let mut v_isSharedCheck_6435_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_6390_) == 0 {
                    v_a_6392_ = lean_ctor_get(v_x_6390_, 0);
                    v_isSharedCheck_6400_ = (!lean_is_exclusive(v_x_6390_)) as u8;
                    if v_isSharedCheck_6400_ == 0 {
                        v___x_6394_ = v_x_6390_;
                        v_isShared_6395_ = v_isSharedCheck_6400_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_6392_);
                        lean_dec(v_x_6390_);
                        v___x_6394_ = lean_box(0);
                        v_isShared_6395_ = v_isSharedCheck_6400_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_6401_ = lean_ctor_get(v_x_6390_, 0);
                    v_isSharedCheck_6435_ = (!lean_is_exclusive(v_x_6390_)) as u8;
                    if v_isSharedCheck_6435_ == 0 {
                        v___x_6403_ = v_x_6390_;
                        v_isShared_6404_ = v_isSharedCheck_6435_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_6401_);
                        lean_dec(v_x_6390_);
                        v___x_6403_ = lean_box(0);
                        v_isShared_6404_ = v_isSharedCheck_6435_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_6395_ == 0 {
                    v___x_6397_ = v___x_6394_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_6399_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6399_, 0, v_a_6392_);
                    v___x_6397_ = v_reuseFailAlloc_6399_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_6398_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_6398_, 0, v___x_6397_);
                return v___x_6398_;
            }
            3 => {
                v_values_6405_ = lean_ctor_get(v_a_6401_, 0);
                v_consumers_6406_ = lean_ctor_get(v_a_6401_, 1);
                v_closed_6407_ = lean_ctor_get_uint8(
                    v_a_6401_,
                    (core::mem::size_of::<*mut LeanObject>() * 2) as u32,
                );
                v_isSharedCheck_6434_ = (!lean_is_exclusive(v_a_6401_)) as u8;
                if v_isSharedCheck_6434_ == 0 {
                    v___x_6409_ = v_a_6401_;
                    v_isShared_6410_ = v_isSharedCheck_6434_;
                    state = 4;
                    continue;
                } else {
                    lean_inc(v_consumers_6406_);
                    lean_inc(v_values_6405_);
                    lean_dec(v_a_6401_);
                    v___x_6409_ = lean_box(0);
                    v_isShared_6410_ = v_isSharedCheck_6434_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_6411_ = l_Std_Queue_dequeue_x3f___redArg(v_values_6405_);
                if lean_obj_tag(v___x_6411_) == 1 {
                    v_val_6412_ = lean_ctor_get(v___x_6411_, 0);
                    v_isSharedCheck_6432_ = (!lean_is_exclusive(v___x_6411_)) as u8;
                    if v_isSharedCheck_6432_ == 0 {
                        v___x_6414_ = v___x_6411_;
                        v_isShared_6415_ = v_isSharedCheck_6432_;
                        state = 5;
                        continue;
                    } else {
                        lean_inc(v_val_6412_);
                        lean_dec(v___x_6411_);
                        v___x_6414_ = lean_box(0);
                        v_isShared_6415_ = v_isSharedCheck_6432_;
                        state = 5;
                        continue;
                    }
                } else {
                    lean_dec(v___x_6411_);
                    lean_del_object(v___x_6409_);
                    lean_dec_ref(v_consumers_6406_);
                    lean_del_object(v___x_6403_);
                    v___x_6433_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__0___redArg___lam__1___closed__1;
                    return v___x_6433_;
                }
            }
            5 => {
                v_fst_6416_ = lean_ctor_get(v_val_6412_, 0);
                lean_inc(v_fst_6416_);
                v_snd_6417_ = lean_ctor_get(v_val_6412_, 1);
                lean_inc(v_snd_6417_);
                lean_dec(v_val_6412_);
                if v_isShared_6410_ == 0 {
                    lean_ctor_set(v___x_6409_, 0, v_snd_6417_);
                    v___x_6419_ = v___x_6409_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_6431_ = lean_alloc_ctor(0, 2, (1) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6431_, 0, v_snd_6417_);
                    lean_ctor_set(v_reuseFailAlloc_6431_, 1, v_consumers_6406_);
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_6431_,
                        (core::mem::size_of::<*mut LeanObject>() * 2) as u32,
                        v_closed_6407_,
                    );
                    v___x_6419_ = v_reuseFailAlloc_6431_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                v___x_6420_ = lean_st_ref_set(v_a_6389_, v___x_6419_);
                v___f_6421_ = lean_alloc_closure(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__0___redArg___lam__0___boxed as *mut core::ffi::c_void, 3, 1);
                lean_closure_set(v___f_6421_, 0, v_fst_6416_);
                if v_isShared_6404_ == 0 {
                    lean_ctor_set(v___x_6403_, 0, v___x_6420_);
                    v___x_6423_ = v___x_6403_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_6430_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6430_, 0, v___x_6420_);
                    v___x_6423_ = v_reuseFailAlloc_6430_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                if v_isShared_6415_ == 0 {
                    lean_ctor_set_tag(v___x_6414_, 0);
                    lean_ctor_set(v___x_6414_, 0, v___x_6423_);
                    v___x_6425_ = v___x_6414_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_6429_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6429_, 0, v___x_6423_);
                    v___x_6425_ = v_reuseFailAlloc_6429_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                v___x_6426_ = lean_unsigned_to_nat(0);
                v___x_6427_ = 0;
                v___x_6428_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(
                    lean_box(0),
                    lean_box(0),
                    v___x_6426_,
                    v___x_6427_,
                    v___x_6425_,
                    v___f_6421_,
                );
                return v___x_6428_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__0___redArg___lam__1___boxed(
    mut v_a_6436_: *mut LeanObject,
    mut v_x_6437_: *mut LeanObject,
    mut v___y_6438_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6439_: *mut LeanObject = core::ptr::null_mut();
    v_res_6439_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__0___redArg___lam__1(v_a_6436_, v_x_6437_);
    lean_dec(v_a_6436_);
    return v_res_6439_;
}
pub unsafe fn l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__0___redArg(
    mut v_a_6440_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6442_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_6443_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6444_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6445_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6446_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6447_: u8 = 0;
    let mut v___x_6448_: *mut LeanObject = core::ptr::null_mut();
    v___x_6442_ = lean_st_ref_get(v_a_6440_);
    lean_inc(v_a_6440_);
    v___f_6443_ = lean_alloc_closure(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__0___redArg___lam__1___boxed as *mut core::ffi::c_void, 3, 1);
    lean_closure_set(v___f_6443_, 0, v_a_6440_);
    v___x_6444_ = lean_alloc_ctor(1, 1, (0) as u32);
    lean_ctor_set(v___x_6444_, 0, v___x_6442_);
    v___x_6445_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_6445_, 0, v___x_6444_);
    v___x_6446_ = lean_unsigned_to_nat(0);
    v___x_6447_ = 0;
    v___x_6448_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(
        lean_box(0),
        lean_box(0),
        v___x_6446_,
        v___x_6447_,
        v___x_6445_,
        v___f_6443_,
    );
    return v___x_6448_;
}
pub unsafe fn l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__0___redArg___boxed(
    mut v_a_6449_: *mut LeanObject,
    mut v___y_6450_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6451_: *mut LeanObject = core::ptr::null_mut();
    v_res_6451_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__0___redArg(v_a_6449_);
    lean_dec(v_a_6449_);
    return v_res_6451_;
}
pub unsafe fn l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__0(
    mut v_00_u03b1_6452_: *mut LeanObject,
    mut v_a_6453_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6455_: *mut LeanObject = core::ptr::null_mut();
    v___x_6455_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__0___redArg(v_a_6453_);
    return v___x_6455_;
}
pub unsafe fn l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__0___boxed(
    mut v_00_u03b1_6456_: *mut LeanObject,
    mut v_a_6457_: *mut LeanObject,
    mut v___y_6458_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6459_: *mut LeanObject = core::ptr::null_mut();
    v_res_6459_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__0(v_00_u03b1_6456_, v_a_6457_);
    lean_dec(v_a_6457_);
    return v_res_6459_;
}
pub unsafe fn l_Std_Async_Waiter_race___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__1___redArg___lam__0(
    mut v_promise_6460_: *mut LeanObject,
    mut v_x_6461_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_6463_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6465_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6466_: u8 = 0;
    let mut v___x_6468_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6469_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6470_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6471_: u8 = 0;
    let mut v___x_6472_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6473_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6474_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_6461_) == 0 {
                    v_a_6463_ = lean_ctor_get(v_x_6461_, 0);
                    v_isSharedCheck_6471_ = (!lean_is_exclusive(v_x_6461_)) as u8;
                    if v_isSharedCheck_6471_ == 0 {
                        v___x_6465_ = v_x_6461_;
                        v_isShared_6466_ = v_isSharedCheck_6471_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_6463_);
                        lean_dec(v_x_6461_);
                        v___x_6465_ = lean_box(0);
                        v_isShared_6466_ = v_isSharedCheck_6471_;
                        state = 1;
                        continue;
                    }
                } else {
                    v___x_6472_ = lean_io_promise_resolve(v_x_6461_, v_promise_6460_);
                    v___x_6473_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v___x_6473_, 0, v___x_6472_);
                    v___x_6474_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_6474_, 0, v___x_6473_);
                    return v___x_6474_;
                }
            }
            1 => {
                if v_isShared_6466_ == 0 {
                    v___x_6468_ = v___x_6465_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_6470_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6470_, 0, v_a_6463_);
                    v___x_6468_ = v_reuseFailAlloc_6470_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_6469_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_6469_, 0, v___x_6468_);
                return v___x_6469_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Async_Waiter_race___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__1___redArg___lam__0___boxed(
    mut v_promise_6475_: *mut LeanObject,
    mut v_x_6476_: *mut LeanObject,
    mut v___y_6477_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6478_: *mut LeanObject = core::ptr::null_mut();
    v_res_6478_ = l_Std_Async_Waiter_race___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__1___redArg___lam__0(v_promise_6475_, v_x_6476_);
    lean_dec(v_promise_6475_);
    return v_res_6478_;
}
pub unsafe fn l_Std_Async_Waiter_race___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__1___redArg___lam__1(
    mut v_lose_6479_: *mut LeanObject,
    mut v___y_6480_: *mut LeanObject,
    mut v___f_6481_: *mut LeanObject,
    mut v_x_6482_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_6484_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6486_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6487_: u8 = 0;
    let mut v___x_6489_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6490_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6491_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6492_: u8 = 0;
    let mut v_a_6493_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6494_: u8 = 0;
    let mut v___x_6495_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6496_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6497_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6498_: u8 = 0;
    let mut v___x_6499_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_6482_) == 0 {
                    lean_dec_ref(v___f_6481_);
                    lean_dec_ref(v_lose_6479_);
                    v_a_6484_ = lean_ctor_get(v_x_6482_, 0);
                    v_isSharedCheck_6492_ = (!lean_is_exclusive(v_x_6482_)) as u8;
                    if v_isSharedCheck_6492_ == 0 {
                        v___x_6486_ = v_x_6482_;
                        v_isShared_6487_ = v_isSharedCheck_6492_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_6484_);
                        lean_dec(v_x_6482_);
                        v___x_6486_ = lean_box(0);
                        v_isShared_6487_ = v_isSharedCheck_6492_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_6493_ = lean_ctor_get(v_x_6482_, 0);
                    lean_inc(v_a_6493_);
                    lean_dec_ref_known(v_x_6482_, 1);
                    v___x_6494_ = (lean_unbox(v_a_6493_) as u8);
                    lean_dec(v_a_6493_);
                    if v___x_6494_ == 0 {
                        lean_dec_ref(v___f_6481_);
                        lean_inc(v___y_6480_);
                        v___x_6495_ = lean_apply_2(v_lose_6479_, v___y_6480_, lean_box(0));
                        return v___x_6495_;
                    } else {
                        lean_dec_ref(v_lose_6479_);
                        v___x_6496_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__0___redArg(v___y_6480_);
                        v___x_6497_ = lean_unsigned_to_nat(0);
                        v___x_6498_ = 0;
                        v___x_6499_ =
                            l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(
                                lean_box(0),
                                lean_box(0),
                                v___x_6497_,
                                v___x_6498_,
                                v___x_6496_,
                                v___f_6481_,
                            );
                        return v___x_6499_;
                    }
                }
            }
            1 => {
                if v_isShared_6487_ == 0 {
                    v___x_6489_ = v___x_6486_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_6491_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6491_, 0, v_a_6484_);
                    v___x_6489_ = v_reuseFailAlloc_6491_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_6490_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_6490_, 0, v___x_6489_);
                return v___x_6490_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Async_Waiter_race___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__1___redArg___lam__1___boxed(
    mut v_lose_6500_: *mut LeanObject,
    mut v___y_6501_: *mut LeanObject,
    mut v___f_6502_: *mut LeanObject,
    mut v_x_6503_: *mut LeanObject,
    mut v___y_6504_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6505_: *mut LeanObject = core::ptr::null_mut();
    v_res_6505_ = l_Std_Async_Waiter_race___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__1___redArg___lam__1(v_lose_6500_, v___y_6501_, v___f_6502_, v_x_6503_);
    lean_dec(v___y_6501_);
    return v_res_6505_;
}
pub unsafe fn l_Std_Async_Waiter_race___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__1___redArg(
    mut v_w_6506_: *mut LeanObject,
    mut v_lose_6507_: *mut LeanObject,
    mut v___y_6508_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_finished_6510_: *mut LeanObject = core::ptr::null_mut();
    let mut v_promise_6511_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6512_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_6513_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_6514_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6516_: u8 = 0;
    let mut v___x_6517_: u8 = 0;
    let mut v___x_6518_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6519_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6520_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6521_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6522_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6523_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6524_: u8 = 0;
    let mut v___x_6525_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6526_: u8 = 0;
    let mut v___x_6527_: u8 = 0;
    let mut v___x_6528_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_finished_6510_ = lean_ctor_get(v_w_6506_, 0);
                lean_inc(v_finished_6510_);
                v_promise_6511_ = lean_ctor_get(v_w_6506_, 1);
                lean_inc(v_promise_6511_);
                lean_dec_ref(v_w_6506_);
                v___x_6512_ = lean_st_ref_take(v_finished_6510_);
                v___f_6513_ = lean_alloc_closure(l_Std_Async_Waiter_race___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__1___redArg___lam__0___boxed as *mut core::ffi::c_void, 3, 1);
                lean_closure_set(v___f_6513_, 0, v_promise_6511_);
                lean_inc(v___y_6508_);
                v___f_6514_ = lean_alloc_closure(l_Std_Async_Waiter_race___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__1___redArg___lam__1___boxed as *mut core::ffi::c_void, 5, 3);
                lean_closure_set(v___f_6514_, 0, v_lose_6507_);
                lean_closure_set(v___f_6514_, 1, v___y_6508_);
                lean_closure_set(v___f_6514_, 2, v___f_6513_);
                v___x_6526_ = (lean_unbox(v___x_6512_) as u8);
                lean_dec(v___x_6512_);
                if v___x_6526_ == 0 {
                    v___x_6527_ = 1;
                    v___y_6516_ = v___x_6527_;
                    state = 1;
                    continue;
                } else {
                    v___x_6528_ = 0;
                    v___y_6516_ = v___x_6528_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_6517_ = 1;
                v___x_6518_ = lean_box((v___x_6517_) as usize);
                v___x_6519_ = lean_st_ref_set(v_finished_6510_, v___x_6518_);
                lean_dec(v_finished_6510_);
                v___x_6520_ = lean_box((v___y_6516_) as usize);
                v___x_6521_ = lean_alloc_ctor(1, 1, (0) as u32);
                lean_ctor_set(v___x_6521_, 0, v___x_6520_);
                v___x_6522_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_6522_, 0, v___x_6521_);
                v___x_6523_ = lean_unsigned_to_nat(0);
                v___x_6524_ = 0;
                v___x_6525_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(
                    lean_box(0),
                    lean_box(0),
                    v___x_6523_,
                    v___x_6524_,
                    v___x_6522_,
                    v___f_6514_,
                );
                return v___x_6525_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Async_Waiter_race___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__1___redArg___boxed(
    mut v_w_6529_: *mut LeanObject,
    mut v_lose_6530_: *mut LeanObject,
    mut v___y_6531_: *mut LeanObject,
    mut v___y_6532_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6533_: *mut LeanObject = core::ptr::null_mut();
    v_res_6533_ = l_Std_Async_Waiter_race___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__1___redArg(v_w_6529_, v_lose_6530_, v___y_6531_);
    lean_dec(v___y_6531_);
    return v_res_6533_;
}
pub unsafe fn l_Std_Async_Waiter_race___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__1(
    mut v_00_u03b1_6534_: *mut LeanObject,
    mut v_w_6535_: *mut LeanObject,
    mut v_lose_6536_: *mut LeanObject,
    mut v___y_6537_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6539_: *mut LeanObject = core::ptr::null_mut();
    v___x_6539_ = l_Std_Async_Waiter_race___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__1___redArg(v_w_6535_, v_lose_6536_, v___y_6537_);
    return v___x_6539_;
}
pub unsafe fn l_Std_Async_Waiter_race___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__1___boxed(
    mut v_00_u03b1_6540_: *mut LeanObject,
    mut v_w_6541_: *mut LeanObject,
    mut v_lose_6542_: *mut LeanObject,
    mut v___y_6543_: *mut LeanObject,
    mut v___y_6544_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6545_: *mut LeanObject = core::ptr::null_mut();
    v_res_6545_ = l_Std_Async_Waiter_race___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__1(v_00_u03b1_6540_, v_w_6541_, v_lose_6542_, v___y_6543_);
    lean_dec(v___y_6543_);
    return v_res_6545_;
}
pub unsafe fn l_Std_Mutex_atomically___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__2___redArg___lam__0(
    mut v_mutex_6546_: *mut LeanObject,
    mut v_x_6547_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6549_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6550_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6551_: *mut LeanObject = core::ptr::null_mut();
    v___x_6549_ = lean_io_basemutex_unlock(v_mutex_6546_);
    v___x_6550_ = lean_alloc_ctor(1, 1, (0) as u32);
    lean_ctor_set(v___x_6550_, 0, v___x_6549_);
    v___x_6551_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_6551_, 0, v___x_6550_);
    return v___x_6551_;
}
pub unsafe fn l_Std_Mutex_atomically___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__2___redArg___lam__0___boxed(
    mut v_mutex_6552_: *mut LeanObject,
    mut v_x_6553_: *mut LeanObject,
    mut v___y_6554_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6555_: *mut LeanObject = core::ptr::null_mut();
    v_res_6555_ = l_Std_Mutex_atomically___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__2___redArg___lam__0(v_mutex_6552_, v_x_6553_);
    lean_dec(v_x_6553_);
    lean_dec(v_mutex_6552_);
    return v_res_6555_;
}
pub unsafe fn l_Std_Mutex_atomically___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__2___redArg___lam__1(
    mut v_k_6556_: *mut LeanObject,
    mut v_ref_6557_: *mut LeanObject,
    mut v_x_6558_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_6560_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6562_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6563_: u8 = 0;
    let mut v___x_6565_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6566_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6567_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6568_: u8 = 0;
    let mut v___x_6569_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_6558_) == 0 {
                    lean_dec(v_ref_6557_);
                    lean_dec_ref(v_k_6556_);
                    v_a_6560_ = lean_ctor_get(v_x_6558_, 0);
                    v_isSharedCheck_6568_ = (!lean_is_exclusive(v_x_6558_)) as u8;
                    if v_isSharedCheck_6568_ == 0 {
                        v___x_6562_ = v_x_6558_;
                        v_isShared_6563_ = v_isSharedCheck_6568_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_6560_);
                        lean_dec(v_x_6558_);
                        v___x_6562_ = lean_box(0);
                        v_isShared_6563_ = v_isSharedCheck_6568_;
                        state = 1;
                        continue;
                    }
                } else {
                    lean_dec_ref_known(v_x_6558_, 1);
                    v___x_6569_ = lean_apply_2(v_k_6556_, v_ref_6557_, lean_box(0));
                    return v___x_6569_;
                }
            }
            1 => {
                if v_isShared_6563_ == 0 {
                    v___x_6565_ = v___x_6562_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_6567_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6567_, 0, v_a_6560_);
                    v___x_6565_ = v_reuseFailAlloc_6567_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_6566_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_6566_, 0, v___x_6565_);
                return v___x_6566_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Mutex_atomically___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__2___redArg___lam__1___boxed(
    mut v_k_6570_: *mut LeanObject,
    mut v_ref_6571_: *mut LeanObject,
    mut v_x_6572_: *mut LeanObject,
    mut v___y_6573_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6574_: *mut LeanObject = core::ptr::null_mut();
    v_res_6574_ = l_Std_Mutex_atomically___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__2___redArg___lam__1(v_k_6570_, v_ref_6571_, v_x_6572_);
    return v_res_6574_;
}
pub unsafe fn l_Std_Mutex_atomically___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__2___redArg___lam__2(
    mut v_mutex_6575_: *mut LeanObject,
    mut v___f_6576_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6578_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6579_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6580_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6581_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6582_: u8 = 0;
    let mut v___x_6583_: *mut LeanObject = core::ptr::null_mut();
    v___x_6578_ = lean_io_basemutex_lock(v_mutex_6575_);
    v___x_6579_ = lean_alloc_ctor(1, 1, (0) as u32);
    lean_ctor_set(v___x_6579_, 0, v___x_6578_);
    v___x_6580_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_6580_, 0, v___x_6579_);
    v___x_6581_ = lean_unsigned_to_nat(0);
    v___x_6582_ = 0;
    v___x_6583_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(
        lean_box(0),
        lean_box(0),
        v___x_6581_,
        v___x_6582_,
        v___x_6580_,
        v___f_6576_,
    );
    return v___x_6583_;
}
pub unsafe fn l_Std_Mutex_atomically___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__2___redArg___lam__2___boxed(
    mut v_mutex_6584_: *mut LeanObject,
    mut v___f_6585_: *mut LeanObject,
    mut v___y_6586_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6587_: *mut LeanObject = core::ptr::null_mut();
    v_res_6587_ = l_Std_Mutex_atomically___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__2___redArg___lam__2(v_mutex_6584_, v___f_6585_);
    lean_dec(v_mutex_6584_);
    return v_res_6587_;
}
pub unsafe fn l_Std_Mutex_atomically___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__2___redArg___lam__3(
    mut v___y_6588_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_6589_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6591_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6592_: u8 = 0;
    let mut v___x_6594_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6595_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6596_: u8 = 0;
    let mut v_a_6597_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6599_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6600_: u8 = 0;
    let mut v_fst_6601_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6603_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6604_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6605_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v___y_6588_) == 0 {
                    v_a_6589_ = lean_ctor_get(v___y_6588_, 0);
                    v_isSharedCheck_6596_ = (!lean_is_exclusive(v___y_6588_)) as u8;
                    if v_isSharedCheck_6596_ == 0 {
                        v___x_6591_ = v___y_6588_;
                        v_isShared_6592_ = v_isSharedCheck_6596_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_6589_);
                        lean_dec(v___y_6588_);
                        v___x_6591_ = lean_box(0);
                        v_isShared_6592_ = v_isSharedCheck_6596_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_6597_ = lean_ctor_get(v___y_6588_, 0);
                    v_isSharedCheck_6605_ = (!lean_is_exclusive(v___y_6588_)) as u8;
                    if v_isSharedCheck_6605_ == 0 {
                        v___x_6599_ = v___y_6588_;
                        v_isShared_6600_ = v_isSharedCheck_6605_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_6597_);
                        lean_dec(v___y_6588_);
                        v___x_6599_ = lean_box(0);
                        v_isShared_6600_ = v_isSharedCheck_6605_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_6592_ == 0 {
                    v___x_6594_ = v___x_6591_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_6595_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6595_, 0, v_a_6589_);
                    v___x_6594_ = v_reuseFailAlloc_6595_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_6594_;
            }
            3 => {
                v_fst_6601_ = lean_ctor_get(v_a_6597_, 0);
                lean_inc(v_fst_6601_);
                lean_dec(v_a_6597_);
                if v_isShared_6600_ == 0 {
                    lean_ctor_set(v___x_6599_, 0, v_fst_6601_);
                    v___x_6603_ = v___x_6599_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_6604_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6604_, 0, v_fst_6601_);
                    v___x_6603_ = v_reuseFailAlloc_6604_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_6603_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Mutex_atomically___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__2___redArg(
    mut v_mutex_6607_: *mut LeanObject,
    mut v_k_6608_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_ref_6610_: *mut LeanObject = core::ptr::null_mut();
    let mut v_mutex_6611_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_6612_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_6613_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_6614_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6615_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6616_: u8 = 0;
    let mut v___x_6617_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6619_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6620_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6621_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6622_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6624_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6625_: u8 = 0;
    let mut v___x_6627_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6628_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6629_: u8 = 0;
    let mut v_a_6630_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6632_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6633_: u8 = 0;
    let mut v_fst_6634_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6636_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6637_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6638_: u8 = 0;
    let mut v_a_6639_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6641_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6642_: u8 = 0;
    let mut v___f_6643_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6644_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6646_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6647_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6648_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ref_6610_ = lean_ctor_get(v_mutex_6607_, 0);
                lean_inc(v_ref_6610_);
                v_mutex_6611_ = lean_ctor_get(v_mutex_6607_, 1);
                lean_inc_n(v_mutex_6611_, 2);
                lean_dec_ref(v_mutex_6607_);
                v___f_6612_ = lean_alloc_closure(l_Std_Mutex_atomically___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__2___redArg___lam__0___boxed as *mut core::ffi::c_void, 3, 1);
                lean_closure_set(v___f_6612_, 0, v_mutex_6611_);
                v___f_6613_ = lean_alloc_closure(l_Std_Mutex_atomically___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__2___redArg___lam__1___boxed as *mut core::ffi::c_void, 4, 2);
                lean_closure_set(v___f_6613_, 0, v_k_6608_);
                lean_closure_set(v___f_6613_, 1, v_ref_6610_);
                v___f_6614_ = lean_alloc_closure(l_Std_Mutex_atomically___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__2___redArg___lam__2___boxed as *mut core::ffi::c_void, 3, 2);
                lean_closure_set(v___f_6614_, 0, v_mutex_6611_);
                lean_closure_set(v___f_6614_, 1, v___f_6613_);
                v___x_6615_ = lean_unsigned_to_nat(0);
                v___x_6616_ = 0;
                v___x_6617_ = l_Std_Async_EAsync_tryFinally_x27___redArg(
                    v___f_6614_,
                    v___f_6612_,
                    v___x_6615_,
                    v___x_6616_,
                );
                if lean_obj_tag(v___x_6617_) == 0 {
                    v_a_6621_ = lean_ctor_get(v___x_6617_, 0);
                    lean_inc(v_a_6621_);
                    lean_dec_ref_known(v___x_6617_, 1);
                    if lean_obj_tag(v_a_6621_) == 0 {
                        v_a_6622_ = lean_ctor_get(v_a_6621_, 0);
                        v_isSharedCheck_6629_ = (!lean_is_exclusive(v_a_6621_)) as u8;
                        if v_isSharedCheck_6629_ == 0 {
                            v___x_6624_ = v_a_6621_;
                            v_isShared_6625_ = v_isSharedCheck_6629_;
                            state = 2;
                            continue;
                        } else {
                            lean_inc(v_a_6622_);
                            lean_dec(v_a_6621_);
                            v___x_6624_ = lean_box(0);
                            v_isShared_6625_ = v_isSharedCheck_6629_;
                            state = 2;
                            continue;
                        }
                    } else {
                        v_a_6630_ = lean_ctor_get(v_a_6621_, 0);
                        v_isSharedCheck_6638_ = (!lean_is_exclusive(v_a_6621_)) as u8;
                        if v_isSharedCheck_6638_ == 0 {
                            v___x_6632_ = v_a_6621_;
                            v_isShared_6633_ = v_isSharedCheck_6638_;
                            state = 4;
                            continue;
                        } else {
                            lean_inc(v_a_6630_);
                            lean_dec(v_a_6621_);
                            v___x_6632_ = lean_box(0);
                            v_isShared_6633_ = v_isSharedCheck_6638_;
                            state = 4;
                            continue;
                        }
                    }
                } else {
                    v_a_6639_ = lean_ctor_get(v___x_6617_, 0);
                    v_isSharedCheck_6648_ = (!lean_is_exclusive(v___x_6617_)) as u8;
                    if v_isSharedCheck_6648_ == 0 {
                        v___x_6641_ = v___x_6617_;
                        v_isShared_6642_ = v_isSharedCheck_6648_;
                        state = 6;
                        continue;
                    } else {
                        lean_inc(v_a_6639_);
                        lean_dec(v___x_6617_);
                        v___x_6641_ = lean_box(0);
                        v_isShared_6642_ = v_isSharedCheck_6648_;
                        state = 6;
                        continue;
                    }
                }
            }
            1 => {
                v___x_6620_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_6620_, 0, v___y_6619_);
                return v___x_6620_;
            }
            2 => {
                if v_isShared_6625_ == 0 {
                    v___x_6627_ = v___x_6624_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_6628_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6628_, 0, v_a_6622_);
                    v___x_6627_ = v_reuseFailAlloc_6628_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___y_6619_ = v___x_6627_;
                state = 1;
                continue;
            }
            4 => {
                v_fst_6634_ = lean_ctor_get(v_a_6630_, 0);
                lean_inc(v_fst_6634_);
                lean_dec(v_a_6630_);
                if v_isShared_6633_ == 0 {
                    lean_ctor_set(v___x_6632_, 0, v_fst_6634_);
                    v___x_6636_ = v___x_6632_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_6637_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6637_, 0, v_fst_6634_);
                    v___x_6636_ = v_reuseFailAlloc_6637_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v___y_6619_ = v___x_6636_;
                state = 1;
                continue;
            }
            6 => {
                v___f_6643_ = l_Std_Mutex_atomically___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__2___redArg___closed__0;
                v___x_6644_ = lean_task_map(v___f_6643_, v_a_6639_, v___x_6615_, v___x_6616_);
                if v_isShared_6642_ == 0 {
                    lean_ctor_set(v___x_6641_, 0, v___x_6644_);
                    v___x_6646_ = v___x_6641_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_6647_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6647_, 0, v___x_6644_);
                    v___x_6646_ = v_reuseFailAlloc_6647_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_6646_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Mutex_atomically___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__2___redArg___boxed(
    mut v_mutex_6649_: *mut LeanObject,
    mut v_k_6650_: *mut LeanObject,
    mut v___y_6651_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6652_: *mut LeanObject = core::ptr::null_mut();
    v_res_6652_ = l_Std_Mutex_atomically___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__2___redArg(v_mutex_6649_, v_k_6650_);
    return v_res_6652_;
}
pub unsafe fn l_Std_Mutex_atomically___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__2(
    mut v_00_u03b1_6653_: *mut LeanObject,
    mut v_00_u03b2_6654_: *mut LeanObject,
    mut v_mutex_6655_: *mut LeanObject,
    mut v_k_6656_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6658_: *mut LeanObject = core::ptr::null_mut();
    v___x_6658_ = l_Std_Mutex_atomically___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__2___redArg(v_mutex_6655_, v_k_6656_);
    return v___x_6658_;
}
pub unsafe fn l_Std_Mutex_atomically___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__2___boxed(
    mut v_00_u03b1_6659_: *mut LeanObject,
    mut v_00_u03b2_6660_: *mut LeanObject,
    mut v_mutex_6661_: *mut LeanObject,
    mut v_k_6662_: *mut LeanObject,
    mut v___y_6663_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6664_: *mut LeanObject = core::ptr::null_mut();
    v_res_6664_ = l_Std_Mutex_atomically___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__2(v_00_u03b1_6659_, v_00_u03b2_6660_, v_mutex_6661_, v_k_6662_);
    return v_res_6664_;
}
pub unsafe fn l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector___redArg___lam__0(
    mut v_x_6665_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_6667_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6669_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6670_: u8 = 0;
    let mut v___x_6672_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6673_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6674_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6675_: u8 = 0;
    let mut v_a_6676_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6678_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6679_: u8 = 0;
    let mut v___x_6680_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6682_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6683_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6684_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6685_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_6665_) == 0 {
                    v_a_6667_ = lean_ctor_get(v_x_6665_, 0);
                    v_isSharedCheck_6675_ = (!lean_is_exclusive(v_x_6665_)) as u8;
                    if v_isSharedCheck_6675_ == 0 {
                        v___x_6669_ = v_x_6665_;
                        v_isShared_6670_ = v_isSharedCheck_6675_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_6667_);
                        lean_dec(v_x_6665_);
                        v___x_6669_ = lean_box(0);
                        v_isShared_6670_ = v_isSharedCheck_6675_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_6676_ = lean_ctor_get(v_x_6665_, 0);
                    v_isSharedCheck_6685_ = (!lean_is_exclusive(v_x_6665_)) as u8;
                    if v_isSharedCheck_6685_ == 0 {
                        v___x_6678_ = v_x_6665_;
                        v_isShared_6679_ = v_isSharedCheck_6685_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_6676_);
                        lean_dec(v_x_6665_);
                        v___x_6678_ = lean_box(0);
                        v_isShared_6679_ = v_isSharedCheck_6685_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_6670_ == 0 {
                    v___x_6672_ = v___x_6669_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_6674_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6674_, 0, v_a_6667_);
                    v___x_6672_ = v_reuseFailAlloc_6674_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_6673_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_6673_, 0, v___x_6672_);
                return v___x_6673_;
            }
            3 => {
                v___x_6680_ = lean_alloc_ctor(1, 1, (0) as u32);
                lean_ctor_set(v___x_6680_, 0, v_a_6676_);
                if v_isShared_6679_ == 0 {
                    lean_ctor_set(v___x_6678_, 0, v___x_6680_);
                    v___x_6682_ = v___x_6678_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_6684_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6684_, 0, v___x_6680_);
                    v___x_6682_ = v_reuseFailAlloc_6684_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_6683_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_6683_, 0, v___x_6682_);
                return v___x_6683_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector___redArg___lam__0___boxed(
    mut v_x_6686_: *mut LeanObject,
    mut v___y_6687_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6688_: *mut LeanObject = core::ptr::null_mut();
    v_res_6688_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector___redArg___lam__0(v_x_6686_);
    return v_res_6688_;
}
pub unsafe fn l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector___redArg___lam__1(
    mut v_x_6689_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___y_6692_: u8 = 0;
    let mut v___x_6693_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6694_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6695_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6696_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6698_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6699_: u8 = 0;
    let mut v___x_6701_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6702_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6703_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6704_: u8 = 0;
    let mut v_a_6705_: *mut LeanObject = core::ptr::null_mut();
    let mut v_values_6706_: *mut LeanObject = core::ptr::null_mut();
    let mut v_closed_6707_: u8 = 0;
    let mut v___x_6708_: u8 = 0;
    let mut v___x_6709_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_6689_) == 0 {
                    v_a_6696_ = lean_ctor_get(v_x_6689_, 0);
                    v_isSharedCheck_6704_ = (!lean_is_exclusive(v_x_6689_)) as u8;
                    if v_isSharedCheck_6704_ == 0 {
                        v___x_6698_ = v_x_6689_;
                        v_isShared_6699_ = v_isSharedCheck_6704_;
                        state = 2;
                        continue;
                    } else {
                        lean_inc(v_a_6696_);
                        lean_dec(v_x_6689_);
                        v___x_6698_ = lean_box(0);
                        v_isShared_6699_ = v_isSharedCheck_6704_;
                        state = 2;
                        continue;
                    }
                } else {
                    v_a_6705_ = lean_ctor_get(v_x_6689_, 0);
                    lean_inc(v_a_6705_);
                    lean_dec_ref_known(v_x_6689_, 1);
                    v_values_6706_ = lean_ctor_get(v_a_6705_, 0);
                    lean_inc_ref(v_values_6706_);
                    v_closed_6707_ = lean_ctor_get_uint8(
                        v_a_6705_,
                        (core::mem::size_of::<*mut LeanObject>() * 2) as u32,
                    );
                    lean_dec(v_a_6705_);
                    v___x_6708_ = l_Std_Queue_isEmpty___redArg(v_values_6706_);
                    lean_dec_ref(v_values_6706_);
                    if v___x_6708_ == 0 {
                        v___x_6709_ = 1;
                        v___y_6692_ = v___x_6709_;
                        state = 1;
                        continue;
                    } else {
                        v___y_6692_ = v_closed_6707_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_6693_ = lean_box((v___y_6692_) as usize);
                v___x_6694_ = lean_alloc_ctor(1, 1, (0) as u32);
                lean_ctor_set(v___x_6694_, 0, v___x_6693_);
                v___x_6695_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_6695_, 0, v___x_6694_);
                return v___x_6695_;
            }
            2 => {
                if v_isShared_6699_ == 0 {
                    v___x_6701_ = v___x_6698_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_6703_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6703_, 0, v_a_6696_);
                    v___x_6701_ = v_reuseFailAlloc_6703_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_6702_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_6702_, 0, v___x_6701_);
                return v___x_6702_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector___redArg___lam__1___boxed(
    mut v_x_6710_: *mut LeanObject,
    mut v___y_6711_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6712_: *mut LeanObject = core::ptr::null_mut();
    v_res_6712_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector___redArg___lam__1(v_x_6710_);
    return v_res_6712_;
}
pub unsafe fn l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector___redArg___lam__2(
    mut v___x_6713_: *mut LeanObject,
    mut v___y_6714_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6716_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6717_: *mut LeanObject = core::ptr::null_mut();
    v___x_6716_ = lean_alloc_ctor(1, 1, (0) as u32);
    lean_ctor_set(v___x_6716_, 0, v___x_6713_);
    v___x_6717_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_6717_, 0, v___x_6716_);
    return v___x_6717_;
}
pub unsafe fn l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector___redArg___lam__2___boxed(
    mut v___x_6718_: *mut LeanObject,
    mut v___y_6719_: *mut LeanObject,
    mut v___y_6720_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6721_: *mut LeanObject = core::ptr::null_mut();
    v_res_6721_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector___redArg___lam__2(v___x_6718_, v___y_6719_);
    lean_dec(v___y_6719_);
    return v_res_6721_;
}
pub unsafe fn l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector___redArg___lam__3(
    mut v___y_6728_: *mut LeanObject,
    mut v_waiter_6729_: *mut LeanObject,
    mut v_x_6730_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_6732_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6734_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6735_: u8 = 0;
    let mut v___x_6737_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6738_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6739_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6740_: u8 = 0;
    let mut v_a_6741_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6742_: u8 = 0;
    let mut v___x_6743_: *mut LeanObject = core::ptr::null_mut();
    let mut v_values_6744_: *mut LeanObject = core::ptr::null_mut();
    let mut v_consumers_6745_: *mut LeanObject = core::ptr::null_mut();
    let mut v_closed_6746_: u8 = 0;
    let mut v___x_6748_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6749_: u8 = 0;
    let mut v___x_6750_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6751_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6753_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6754_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6755_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6756_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6757_: u8 = 0;
    let mut v_lose_6758_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6759_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_6730_) == 0 {
                    lean_dec_ref(v_waiter_6729_);
                    v_a_6732_ = lean_ctor_get(v_x_6730_, 0);
                    v_isSharedCheck_6740_ = (!lean_is_exclusive(v_x_6730_)) as u8;
                    if v_isSharedCheck_6740_ == 0 {
                        v___x_6734_ = v_x_6730_;
                        v_isShared_6735_ = v_isSharedCheck_6740_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_6732_);
                        lean_dec(v_x_6730_);
                        v___x_6734_ = lean_box(0);
                        v_isShared_6735_ = v_isSharedCheck_6740_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_6741_ = lean_ctor_get(v_x_6730_, 0);
                    lean_inc(v_a_6741_);
                    lean_dec_ref_known(v_x_6730_, 1);
                    v___x_6742_ = (lean_unbox(v_a_6741_) as u8);
                    lean_dec(v_a_6741_);
                    if v___x_6742_ == 0 {
                        v___x_6743_ = lean_st_ref_take(v___y_6728_);
                        v_values_6744_ = lean_ctor_get(v___x_6743_, 0);
                        v_consumers_6745_ = lean_ctor_get(v___x_6743_, 1);
                        v_closed_6746_ = lean_ctor_get_uint8(
                            v___x_6743_,
                            (core::mem::size_of::<*mut LeanObject>() * 2) as u32,
                        );
                        v_isSharedCheck_6757_ = (!lean_is_exclusive(v___x_6743_)) as u8;
                        if v_isSharedCheck_6757_ == 0 {
                            v___x_6748_ = v___x_6743_;
                            v_isShared_6749_ = v_isSharedCheck_6757_;
                            state = 3;
                            continue;
                        } else {
                            lean_inc(v_consumers_6745_);
                            lean_inc(v_values_6744_);
                            lean_dec(v___x_6743_);
                            v___x_6748_ = lean_box(0);
                            v_isShared_6749_ = v_isSharedCheck_6757_;
                            state = 3;
                            continue;
                        }
                    } else {
                        v_lose_6758_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector___redArg___lam__3___closed__2;
                        v___x_6759_ = l_Std_Async_Waiter_race___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__1___redArg(v_waiter_6729_, v_lose_6758_, v___y_6728_);
                        return v___x_6759_;
                    }
                }
            }
            1 => {
                if v_isShared_6735_ == 0 {
                    v___x_6737_ = v___x_6734_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_6739_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6739_, 0, v_a_6732_);
                    v___x_6737_ = v_reuseFailAlloc_6739_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_6738_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_6738_, 0, v___x_6737_);
                return v___x_6738_;
            }
            3 => {
                v___x_6750_ = lean_alloc_ctor(1, 1, (0) as u32);
                lean_ctor_set(v___x_6750_, 0, v_waiter_6729_);
                v___x_6751_ = l_Std_Queue_enqueue___redArg(v___x_6750_, v_consumers_6745_);
                if v_isShared_6749_ == 0 {
                    lean_ctor_set(v___x_6748_, 1, v___x_6751_);
                    v___x_6753_ = v___x_6748_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_6756_ = lean_alloc_ctor(0, 2, (1) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6756_, 0, v_values_6744_);
                    lean_ctor_set(v_reuseFailAlloc_6756_, 1, v___x_6751_);
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_6756_,
                        (core::mem::size_of::<*mut LeanObject>() * 2) as u32,
                        v_closed_6746_,
                    );
                    v___x_6753_ = v_reuseFailAlloc_6756_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_6754_ = lean_st_ref_set(v___y_6728_, v___x_6753_);
                v___x_6755_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector___redArg___lam__3___closed__1;
                return v___x_6755_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector___redArg___lam__3___boxed(
    mut v___y_6760_: *mut LeanObject,
    mut v_waiter_6761_: *mut LeanObject,
    mut v_x_6762_: *mut LeanObject,
    mut v___y_6763_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6764_: *mut LeanObject = core::ptr::null_mut();
    v_res_6764_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector___redArg___lam__3(v___y_6760_, v_waiter_6761_, v_x_6762_);
    lean_dec(v___y_6760_);
    return v_res_6764_;
}
pub unsafe fn l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector___redArg___lam__4(
    mut v___f_6765_: *mut LeanObject,
    mut v_waiter_6766_: *mut LeanObject,
    mut v___y_6767_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6769_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6770_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6771_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6772_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6773_: u8 = 0;
    let mut v___x_6774_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_6775_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6776_: *mut LeanObject = core::ptr::null_mut();
    v___x_6769_ = lean_st_ref_get(v___y_6767_);
    v___x_6770_ = lean_alloc_ctor(1, 1, (0) as u32);
    lean_ctor_set(v___x_6770_, 0, v___x_6769_);
    v___x_6771_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_6771_, 0, v___x_6770_);
    v___x_6772_ = lean_unsigned_to_nat(0);
    v___x_6773_ = 0;
    v___x_6774_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(
        lean_box(0),
        lean_box(0),
        v___x_6772_,
        v___x_6773_,
        v___x_6771_,
        v___f_6765_,
    );
    lean_inc(v___y_6767_);
    v___f_6775_ = lean_alloc_closure(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector___redArg___lam__3___boxed as *mut core::ffi::c_void, 4, 2);
    lean_closure_set(v___f_6775_, 0, v___y_6767_);
    lean_closure_set(v___f_6775_, 1, v_waiter_6766_);
    v___x_6776_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(
        lean_box(0),
        lean_box(0),
        v___x_6772_,
        v___x_6773_,
        v___x_6774_,
        v___f_6775_,
    );
    return v___x_6776_;
}
pub unsafe fn l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector___redArg___lam__4___boxed(
    mut v___f_6777_: *mut LeanObject,
    mut v_waiter_6778_: *mut LeanObject,
    mut v___y_6779_: *mut LeanObject,
    mut v___y_6780_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6781_: *mut LeanObject = core::ptr::null_mut();
    v_res_6781_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector___redArg___lam__4(v___f_6777_, v_waiter_6778_, v___y_6779_);
    lean_dec(v___y_6779_);
    return v_res_6781_;
}
pub unsafe fn l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector___redArg___lam__5(
    mut v___f_6782_: *mut LeanObject,
    mut v_ch_6783_: *mut LeanObject,
    mut v_waiter_6784_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_6786_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6787_: *mut LeanObject = core::ptr::null_mut();
    v___f_6786_ = lean_alloc_closure(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector___redArg___lam__4___boxed as *mut core::ffi::c_void, 4, 2);
    lean_closure_set(v___f_6786_, 0, v___f_6782_);
    lean_closure_set(v___f_6786_, 1, v_waiter_6784_);
    v___x_6787_ = l_Std_Mutex_atomically___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__2___redArg(v_ch_6783_, v___f_6786_);
    return v___x_6787_;
}
pub unsafe fn l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector___redArg___lam__5___boxed(
    mut v___f_6788_: *mut LeanObject,
    mut v_ch_6789_: *mut LeanObject,
    mut v_waiter_6790_: *mut LeanObject,
    mut v___y_6791_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6792_: *mut LeanObject = core::ptr::null_mut();
    v_res_6792_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector___redArg___lam__5(v___f_6788_, v_ch_6789_, v_waiter_6790_);
    return v_res_6792_;
}
pub unsafe fn l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector___redArg___lam__7(
    mut v___y_6797_: *mut LeanObject,
    mut v___f_6798_: *mut LeanObject,
    mut v_x_6799_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_6801_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6803_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6804_: u8 = 0;
    let mut v___x_6806_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6807_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6808_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6809_: u8 = 0;
    let mut v_a_6810_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6811_: u8 = 0;
    let mut v___x_6812_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6813_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6814_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6815_: u8 = 0;
    let mut v___x_6816_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_6799_) == 0 {
                    lean_dec_ref(v___f_6798_);
                    v_a_6801_ = lean_ctor_get(v_x_6799_, 0);
                    v_isSharedCheck_6809_ = (!lean_is_exclusive(v_x_6799_)) as u8;
                    if v_isSharedCheck_6809_ == 0 {
                        v___x_6803_ = v_x_6799_;
                        v_isShared_6804_ = v_isSharedCheck_6809_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_6801_);
                        lean_dec(v_x_6799_);
                        v___x_6803_ = lean_box(0);
                        v_isShared_6804_ = v_isSharedCheck_6809_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_6810_ = lean_ctor_get(v_x_6799_, 0);
                    lean_inc(v_a_6810_);
                    lean_dec_ref_known(v_x_6799_, 1);
                    v___x_6811_ = (lean_unbox(v_a_6810_) as u8);
                    lean_dec(v_a_6810_);
                    if v___x_6811_ == 0 {
                        lean_dec_ref(v___f_6798_);
                        v___x_6812_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector___redArg___lam__7___closed__1;
                        return v___x_6812_;
                    } else {
                        v___x_6813_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__0___redArg(v___y_6797_);
                        v___x_6814_ = lean_unsigned_to_nat(0);
                        v___x_6815_ = 0;
                        v___x_6816_ =
                            l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(
                                lean_box(0),
                                lean_box(0),
                                v___x_6814_,
                                v___x_6815_,
                                v___x_6813_,
                                v___f_6798_,
                            );
                        return v___x_6816_;
                    }
                }
            }
            1 => {
                if v_isShared_6804_ == 0 {
                    v___x_6806_ = v___x_6803_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_6808_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6808_, 0, v_a_6801_);
                    v___x_6806_ = v_reuseFailAlloc_6808_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_6807_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_6807_, 0, v___x_6806_);
                return v___x_6807_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector___redArg___lam__7___boxed(
    mut v___y_6817_: *mut LeanObject,
    mut v___f_6818_: *mut LeanObject,
    mut v_x_6819_: *mut LeanObject,
    mut v___y_6820_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6821_: *mut LeanObject = core::ptr::null_mut();
    v_res_6821_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector___redArg___lam__7(v___y_6817_, v___f_6818_, v_x_6819_);
    lean_dec(v___y_6817_);
    return v_res_6821_;
}
pub unsafe fn l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector___redArg___lam__6(
    mut v___f_6822_: *mut LeanObject,
    mut v___f_6823_: *mut LeanObject,
    mut v___y_6824_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6826_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6827_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6828_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6829_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6830_: u8 = 0;
    let mut v___x_6831_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_6832_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6833_: *mut LeanObject = core::ptr::null_mut();
    v___x_6826_ = lean_st_ref_get(v___y_6824_);
    v___x_6827_ = lean_alloc_ctor(1, 1, (0) as u32);
    lean_ctor_set(v___x_6827_, 0, v___x_6826_);
    v___x_6828_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_6828_, 0, v___x_6827_);
    v___x_6829_ = lean_unsigned_to_nat(0);
    v___x_6830_ = 0;
    v___x_6831_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(
        lean_box(0),
        lean_box(0),
        v___x_6829_,
        v___x_6830_,
        v___x_6828_,
        v___f_6822_,
    );
    lean_inc(v___y_6824_);
    v___f_6832_ = lean_alloc_closure(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector___redArg___lam__7___boxed as *mut core::ffi::c_void, 4, 2);
    lean_closure_set(v___f_6832_, 0, v___y_6824_);
    lean_closure_set(v___f_6832_, 1, v___f_6823_);
    v___x_6833_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(
        lean_box(0),
        lean_box(0),
        v___x_6829_,
        v___x_6830_,
        v___x_6831_,
        v___f_6832_,
    );
    return v___x_6833_;
}
pub unsafe fn l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector___redArg___lam__6___boxed(
    mut v___f_6834_: *mut LeanObject,
    mut v___f_6835_: *mut LeanObject,
    mut v___y_6836_: *mut LeanObject,
    mut v___y_6837_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6838_: *mut LeanObject = core::ptr::null_mut();
    v_res_6838_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector___redArg___lam__6(v___f_6834_, v___f_6835_, v___y_6836_);
    lean_dec(v___y_6836_);
    return v_res_6838_;
}
pub unsafe fn l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector___redArg___lam__8(
    mut v_values_6839_: *mut LeanObject,
    mut v_closed_6840_: u8,
    mut v___y_6841_: *mut LeanObject,
    mut v_x_6842_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_6844_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6846_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6847_: u8 = 0;
    let mut v___x_6849_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6850_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6851_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6852_: u8 = 0;
    let mut v_a_6853_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6855_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6856_: u8 = 0;
    let mut v___x_6857_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6858_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6860_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6861_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6862_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6863_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_6842_) == 0 {
                    lean_dec_ref(v_values_6839_);
                    v_a_6844_ = lean_ctor_get(v_x_6842_, 0);
                    v_isSharedCheck_6852_ = (!lean_is_exclusive(v_x_6842_)) as u8;
                    if v_isSharedCheck_6852_ == 0 {
                        v___x_6846_ = v_x_6842_;
                        v_isShared_6847_ = v_isSharedCheck_6852_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_6844_);
                        lean_dec(v_x_6842_);
                        v___x_6846_ = lean_box(0);
                        v_isShared_6847_ = v_isSharedCheck_6852_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_6853_ = lean_ctor_get(v_x_6842_, 0);
                    v_isSharedCheck_6863_ = (!lean_is_exclusive(v_x_6842_)) as u8;
                    if v_isSharedCheck_6863_ == 0 {
                        v___x_6855_ = v_x_6842_;
                        v_isShared_6856_ = v_isSharedCheck_6863_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_6853_);
                        lean_dec(v_x_6842_);
                        v___x_6855_ = lean_box(0);
                        v_isShared_6856_ = v_isSharedCheck_6863_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_6847_ == 0 {
                    v___x_6849_ = v___x_6846_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_6851_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6851_, 0, v_a_6844_);
                    v___x_6849_ = v_reuseFailAlloc_6851_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_6850_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_6850_, 0, v___x_6849_);
                return v___x_6850_;
            }
            3 => {
                v___x_6857_ = lean_alloc_ctor(0, 2, (1) as u32);
                lean_ctor_set(v___x_6857_, 0, v_values_6839_);
                lean_ctor_set(v___x_6857_, 1, v_a_6853_);
                lean_ctor_set_uint8(
                    v___x_6857_,
                    (core::mem::size_of::<*mut LeanObject>() * 2) as u32,
                    v_closed_6840_,
                );
                v___x_6858_ = lean_st_ref_set(v___y_6841_, v___x_6857_);
                if v_isShared_6856_ == 0 {
                    lean_ctor_set(v___x_6855_, 0, v___x_6858_);
                    v___x_6860_ = v___x_6855_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_6862_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6862_, 0, v___x_6858_);
                    v___x_6860_ = v_reuseFailAlloc_6862_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_6861_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_6861_, 0, v___x_6860_);
                return v___x_6861_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector___redArg___lam__8___boxed(
    mut v_values_6864_: *mut LeanObject,
    mut v_closed_6865_: *mut LeanObject,
    mut v___y_6866_: *mut LeanObject,
    mut v_x_6867_: *mut LeanObject,
    mut v___y_6868_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_closed_boxed_6869_: u8 = 0;
    let mut v_res_6870_: *mut LeanObject = core::ptr::null_mut();
    v_closed_boxed_6869_ = (lean_unbox(v_closed_6865_) as u8);
    v_res_6870_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector___redArg___lam__8(v_values_6864_, v_closed_boxed_6869_, v___y_6866_, v_x_6867_);
    lean_dec(v___y_6866_);
    return v_res_6870_;
}
pub unsafe fn l_Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__3___redArg___lam__0(
    mut v_x_6871_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6873_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6874_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6876_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6877_: u8 = 0;
    let mut v___x_6878_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6880_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6881_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6882_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6883_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_6871_) == 0 {
                    v___x_6873_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_6873_, 0, v_x_6871_);
                    return v___x_6873_;
                } else {
                    v_a_6874_ = lean_ctor_get(v_x_6871_, 0);
                    v_isSharedCheck_6883_ = (!lean_is_exclusive(v_x_6871_)) as u8;
                    if v_isSharedCheck_6883_ == 0 {
                        v___x_6876_ = v_x_6871_;
                        v_isShared_6877_ = v_isSharedCheck_6883_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_6874_);
                        lean_dec(v_x_6871_);
                        v___x_6876_ = lean_box(0);
                        v_isShared_6877_ = v_isSharedCheck_6883_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_6878_ = l_List_reverse___redArg(v_a_6874_);
                if v_isShared_6877_ == 0 {
                    lean_ctor_set(v___x_6876_, 0, v___x_6878_);
                    v___x_6880_ = v___x_6876_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_6882_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6882_, 0, v___x_6878_);
                    v___x_6880_ = v_reuseFailAlloc_6882_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_6881_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_6881_, 0, v___x_6880_);
                return v___x_6881_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__3___redArg___lam__0___boxed(
    mut v_x_6884_: *mut LeanObject,
    mut v___y_6885_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6886_: *mut LeanObject = core::ptr::null_mut();
    v_res_6886_ = l_Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__3___redArg___lam__0(v_x_6884_);
    return v_res_6886_;
}
pub unsafe fn l_Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__3___redArg___lam__2(
    mut v_a_6887_: *mut LeanObject,
    mut v___x_6888_: *mut LeanObject,
    mut v_x_6889_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_6891_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6893_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6894_: u8 = 0;
    let mut v___x_6896_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6897_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6898_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6899_: u8 = 0;
    let mut v_a_6900_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6902_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6903_: u8 = 0;
    let mut v___x_6904_: u8 = 0;
    let mut v___x_6905_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6907_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6908_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6909_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6910_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6911_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6913_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6914_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6915_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6916_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_6889_) == 0 {
                    lean_dec(v___x_6888_);
                    lean_dec(v_a_6887_);
                    v_a_6891_ = lean_ctor_get(v_x_6889_, 0);
                    v_isSharedCheck_6899_ = (!lean_is_exclusive(v_x_6889_)) as u8;
                    if v_isSharedCheck_6899_ == 0 {
                        v___x_6893_ = v_x_6889_;
                        v_isShared_6894_ = v_isSharedCheck_6899_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_6891_);
                        lean_dec(v_x_6889_);
                        v___x_6893_ = lean_box(0);
                        v_isShared_6894_ = v_isSharedCheck_6899_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_6900_ = lean_ctor_get(v_x_6889_, 0);
                    v_isSharedCheck_6916_ = (!lean_is_exclusive(v_x_6889_)) as u8;
                    if v_isSharedCheck_6916_ == 0 {
                        v___x_6902_ = v_x_6889_;
                        v_isShared_6903_ = v_isSharedCheck_6916_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_6900_);
                        lean_dec(v_x_6889_);
                        v___x_6902_ = lean_box(0);
                        v_isShared_6903_ = v_isSharedCheck_6916_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_6894_ == 0 {
                    v___x_6896_ = v___x_6893_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_6898_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6898_, 0, v_a_6891_);
                    v___x_6896_ = v_reuseFailAlloc_6898_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_6897_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_6897_, 0, v___x_6896_);
                return v___x_6897_;
            }
            3 => {
                v___x_6904_ = l_List_isEmpty___redArg(v_a_6887_);
                if v___x_6904_ == 0 {
                    lean_dec(v___x_6888_);
                    v___x_6905_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v___x_6905_, 0, v_a_6900_);
                    lean_ctor_set(v___x_6905_, 1, v_a_6887_);
                    if v_isShared_6903_ == 0 {
                        lean_ctor_set(v___x_6902_, 0, v___x_6905_);
                        v___x_6907_ = v___x_6902_;
                        state = 4;
                        continue;
                    } else {
                        v_reuseFailAlloc_6909_ = lean_alloc_ctor(1, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_6909_, 0, v___x_6905_);
                        v___x_6907_ = v_reuseFailAlloc_6909_;
                        state = 4;
                        continue;
                    }
                } else {
                    lean_dec(v_a_6887_);
                    v___x_6910_ = l_List_reverse___redArg(v_a_6900_);
                    v___x_6911_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v___x_6911_, 0, v___x_6888_);
                    lean_ctor_set(v___x_6911_, 1, v___x_6910_);
                    if v_isShared_6903_ == 0 {
                        lean_ctor_set(v___x_6902_, 0, v___x_6911_);
                        v___x_6913_ = v___x_6902_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_6915_ = lean_alloc_ctor(1, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_6915_, 0, v___x_6911_);
                        v___x_6913_ = v_reuseFailAlloc_6915_;
                        state = 5;
                        continue;
                    }
                }
            }
            4 => {
                v___x_6908_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_6908_, 0, v___x_6907_);
                return v___x_6908_;
            }
            5 => {
                v___x_6914_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_6914_, 0, v___x_6913_);
                return v___x_6914_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__3___redArg___lam__2___boxed(
    mut v_a_6917_: *mut LeanObject,
    mut v___x_6918_: *mut LeanObject,
    mut v_x_6919_: *mut LeanObject,
    mut v___y_6920_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6921_: *mut LeanObject = core::ptr::null_mut();
    v_res_6921_ = l_Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__3___redArg___lam__2(v_a_6917_, v___x_6918_, v_x_6919_);
    return v_res_6921_;
}
pub unsafe fn l_List_filterAuxM___at___00Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__3_spec__3___redArg___lam__1(
    mut v_x_6922_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___y_6925_: u8 = 0;
    let mut v___x_6926_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6927_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6928_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6929_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6930_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6931_: u8 = 0;
    let mut v___x_6932_: u8 = 0;
    let mut v___x_6933_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_6922_) == 0 {
                    v___x_6929_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_6929_, 0, v_x_6922_);
                    return v___x_6929_;
                } else {
                    v_a_6930_ = lean_ctor_get(v_x_6922_, 0);
                    lean_inc(v_a_6930_);
                    lean_dec_ref_known(v_x_6922_, 1);
                    v___x_6931_ = (lean_unbox(v_a_6930_) as u8);
                    lean_dec(v_a_6930_);
                    if v___x_6931_ == 0 {
                        v___x_6932_ = 1;
                        v___y_6925_ = v___x_6932_;
                        state = 1;
                        continue;
                    } else {
                        v___x_6933_ = 0;
                        v___y_6925_ = v___x_6933_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_6926_ = lean_box((v___y_6925_) as usize);
                v___x_6927_ = lean_alloc_ctor(1, 1, (0) as u32);
                lean_ctor_set(v___x_6927_, 0, v___x_6926_);
                v___x_6928_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_6928_, 0, v___x_6927_);
                return v___x_6928_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_filterAuxM___at___00Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__3_spec__3___redArg___lam__1___boxed(
    mut v_x_6934_: *mut LeanObject,
    mut v___y_6935_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6936_: *mut LeanObject = core::ptr::null_mut();
    v_res_6936_ = l_List_filterAuxM___at___00Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__3_spec__3___redArg___lam__1(v_x_6934_);
    return v_res_6936_;
}
pub unsafe fn l_List_filterAuxM___at___00Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__3_spec__3___redArg___lam__0___boxed(
    mut v_tail_6937_: *mut LeanObject,
    mut v_x_6938_: *mut LeanObject,
    mut v_head_6939_: *mut LeanObject,
    mut v_x_6940_: *mut LeanObject,
    mut v___y_6941_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6942_: *mut LeanObject = core::ptr::null_mut();
    v_res_6942_ = l_List_filterAuxM___at___00Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__3_spec__3___redArg___lam__0(v_tail_6937_, v_x_6938_, v_head_6939_, v_x_6940_);
    return v_res_6942_;
}
pub unsafe fn l_List_filterAuxM___at___00Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__3_spec__3___redArg(
    mut v_x_6949_: *mut LeanObject,
    mut v_x_6950_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6952_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6953_: *mut LeanObject = core::ptr::null_mut();
    let mut v_head_6954_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_6955_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_6956_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_6958_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6959_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6960_: u8 = 0;
    let mut v___x_6961_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6962_: *mut LeanObject = core::ptr::null_mut();
    let mut v_finished_6963_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6965_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6966_: u8 = 0;
    let mut v_finished_6967_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6968_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_6969_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6971_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6972_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6973_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6974_: u8 = 0;
    let mut v___x_6975_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6976_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6977_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_6949_) == 0 {
                    v___x_6952_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v___x_6952_, 0, v_x_6950_);
                    v___x_6953_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_6953_, 0, v___x_6952_);
                    return v___x_6953_;
                } else {
                    v_head_6954_ = lean_ctor_get(v_x_6949_, 0);
                    lean_inc_n(v_head_6954_, 2);
                    v_tail_6955_ = lean_ctor_get(v_x_6949_, 1);
                    lean_inc(v_tail_6955_);
                    lean_dec_ref_known(v_x_6949_, 2);
                    v___f_6956_ = lean_alloc_closure(l_List_filterAuxM___at___00Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__3_spec__3___redArg___lam__0___boxed as *mut core::ffi::c_void, 5, 3);
                    lean_closure_set(v___f_6956_, 0, v_tail_6955_);
                    lean_closure_set(v___f_6956_, 1, v_x_6950_);
                    lean_closure_set(v___f_6956_, 2, v_head_6954_);
                    if lean_obj_tag(v_head_6954_) == 0 {
                        lean_dec_ref_known(v_head_6954_, 1);
                        v___x_6962_ = l_List_filterAuxM___at___00Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__3_spec__3___redArg___closed__1;
                        v_val_6958_ = v___x_6962_;
                        state = 1;
                        continue;
                    } else {
                        v_finished_6963_ = lean_ctor_get(v_head_6954_, 0);
                        v_isSharedCheck_6977_ = (!lean_is_exclusive(v_head_6954_)) as u8;
                        if v_isSharedCheck_6977_ == 0 {
                            v___x_6965_ = v_head_6954_;
                            v_isShared_6966_ = v_isSharedCheck_6977_;
                            state = 2;
                            continue;
                        } else {
                            lean_inc(v_finished_6963_);
                            lean_dec(v_head_6954_);
                            v___x_6965_ = lean_box(0);
                            v_isShared_6966_ = v_isSharedCheck_6977_;
                            state = 2;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v___x_6959_ = lean_unsigned_to_nat(0);
                v___x_6960_ = 0;
                v___x_6961_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(
                    lean_box(0),
                    lean_box(0),
                    v___x_6959_,
                    v___x_6960_,
                    v_val_6958_,
                    v___f_6956_,
                );
                return v___x_6961_;
            }
            2 => {
                v_finished_6967_ = lean_ctor_get(v_finished_6963_, 0);
                lean_inc(v_finished_6967_);
                lean_dec_ref(v_finished_6963_);
                v___x_6968_ = lean_st_ref_get(v_finished_6967_);
                lean_dec(v_finished_6967_);
                v___f_6969_ = l_List_filterAuxM___at___00Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__3_spec__3___redArg___closed__2;
                if v_isShared_6966_ == 0 {
                    lean_ctor_set(v___x_6965_, 0, v___x_6968_);
                    v___x_6971_ = v___x_6965_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_6976_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6976_, 0, v___x_6968_);
                    v___x_6971_ = v_reuseFailAlloc_6976_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_6972_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_6972_, 0, v___x_6971_);
                v___x_6973_ = lean_unsigned_to_nat(0);
                v___x_6974_ = 0;
                v___x_6975_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(
                    lean_box(0),
                    lean_box(0),
                    v___x_6973_,
                    v___x_6974_,
                    v___x_6972_,
                    v___f_6969_,
                );
                v_val_6958_ = v___x_6975_;
                state = 1;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_filterAuxM___at___00Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__3_spec__3___redArg___lam__0(
    mut v_tail_6978_: *mut LeanObject,
    mut v_x_6979_: *mut LeanObject,
    mut v_head_6980_: *mut LeanObject,
    mut v_x_6981_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_6983_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6985_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6986_: u8 = 0;
    let mut v___x_6988_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6989_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6990_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6991_: u8 = 0;
    let mut v_a_6992_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6993_: u8 = 0;
    let mut v___x_6994_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6995_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6996_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_6981_) == 0 {
                    lean_dec_ref(v_head_6980_);
                    lean_dec(v_x_6979_);
                    lean_dec(v_tail_6978_);
                    v_a_6983_ = lean_ctor_get(v_x_6981_, 0);
                    v_isSharedCheck_6991_ = (!lean_is_exclusive(v_x_6981_)) as u8;
                    if v_isSharedCheck_6991_ == 0 {
                        v___x_6985_ = v_x_6981_;
                        v_isShared_6986_ = v_isSharedCheck_6991_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_6983_);
                        lean_dec(v_x_6981_);
                        v___x_6985_ = lean_box(0);
                        v_isShared_6986_ = v_isSharedCheck_6991_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_6992_ = lean_ctor_get(v_x_6981_, 0);
                    lean_inc(v_a_6992_);
                    lean_dec_ref_known(v_x_6981_, 1);
                    v___x_6993_ = (lean_unbox(v_a_6992_) as u8);
                    lean_dec(v_a_6992_);
                    if v___x_6993_ == 0 {
                        lean_dec_ref(v_head_6980_);
                        v___x_6994_ = l_List_filterAuxM___at___00Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__3_spec__3___redArg(v_tail_6978_, v_x_6979_);
                        return v___x_6994_;
                    } else {
                        v___x_6995_ = lean_alloc_ctor(1, 2, (0) as u32);
                        lean_ctor_set(v___x_6995_, 0, v_head_6980_);
                        lean_ctor_set(v___x_6995_, 1, v_x_6979_);
                        v___x_6996_ = l_List_filterAuxM___at___00Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__3_spec__3___redArg(v_tail_6978_, v___x_6995_);
                        return v___x_6996_;
                    }
                }
            }
            1 => {
                if v_isShared_6986_ == 0 {
                    v___x_6988_ = v___x_6985_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_6990_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6990_, 0, v_a_6983_);
                    v___x_6988_ = v_reuseFailAlloc_6990_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_6989_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_6989_, 0, v___x_6988_);
                return v___x_6989_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_filterAuxM___at___00Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__3_spec__3___redArg___boxed(
    mut v_x_6997_: *mut LeanObject,
    mut v_x_6998_: *mut LeanObject,
    mut v___y_6999_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_7000_: *mut LeanObject = core::ptr::null_mut();
    v_res_7000_ = l_List_filterAuxM___at___00Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__3_spec__3___redArg(v_x_6997_, v_x_6998_);
    return v_res_7000_;
}
pub unsafe fn l_Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__3___redArg___lam__1(
    mut v_eList_7001_: *mut LeanObject,
    mut v___x_7002_: *mut LeanObject,
    mut v___f_7003_: *mut LeanObject,
    mut v_x_7004_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_7006_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7008_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_7009_: u8 = 0;
    let mut v___x_7011_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7012_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7013_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7014_: u8 = 0;
    let mut v_a_7015_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7016_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7017_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7018_: u8 = 0;
    let mut v___x_7019_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_7020_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7021_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_7004_) == 0 {
                    lean_dec_ref(v___f_7003_);
                    lean_dec(v___x_7002_);
                    lean_dec(v_eList_7001_);
                    v_a_7006_ = lean_ctor_get(v_x_7004_, 0);
                    v_isSharedCheck_7014_ = (!lean_is_exclusive(v_x_7004_)) as u8;
                    if v_isSharedCheck_7014_ == 0 {
                        v___x_7008_ = v_x_7004_;
                        v_isShared_7009_ = v_isSharedCheck_7014_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_7006_);
                        lean_dec(v_x_7004_);
                        v___x_7008_ = lean_box(0);
                        v_isShared_7009_ = v_isSharedCheck_7014_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_7015_ = lean_ctor_get(v_x_7004_, 0);
                    lean_inc(v_a_7015_);
                    lean_dec_ref_known(v_x_7004_, 1);
                    lean_inc(v___x_7002_);
                    v___x_7016_ = l_List_filterAuxM___at___00Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__3_spec__3___redArg(v_eList_7001_, v___x_7002_);
                    v___x_7017_ = lean_unsigned_to_nat(0);
                    v___x_7018_ = 0;
                    v___x_7019_ =
                        l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(
                            lean_box(0),
                            lean_box(0),
                            v___x_7017_,
                            v___x_7018_,
                            v___x_7016_,
                            v___f_7003_,
                        );
                    v___f_7020_ = lean_alloc_closure(l_Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__3___redArg___lam__2___boxed as *mut core::ffi::c_void, 4, 2);
                    lean_closure_set(v___f_7020_, 0, v_a_7015_);
                    lean_closure_set(v___f_7020_, 1, v___x_7002_);
                    v___x_7021_ =
                        l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(
                            lean_box(0),
                            lean_box(0),
                            v___x_7017_,
                            v___x_7018_,
                            v___x_7019_,
                            v___f_7020_,
                        );
                    return v___x_7021_;
                }
            }
            1 => {
                if v_isShared_7009_ == 0 {
                    v___x_7011_ = v___x_7008_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_7013_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_7013_, 0, v_a_7006_);
                    v___x_7011_ = v_reuseFailAlloc_7013_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_7012_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_7012_, 0, v___x_7011_);
                return v___x_7012_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__3___redArg___lam__1___boxed(
    mut v_eList_7022_: *mut LeanObject,
    mut v___x_7023_: *mut LeanObject,
    mut v___f_7024_: *mut LeanObject,
    mut v_x_7025_: *mut LeanObject,
    mut v___y_7026_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_7027_: *mut LeanObject = core::ptr::null_mut();
    v_res_7027_ = l_Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__3___redArg___lam__1(v_eList_7022_, v___x_7023_, v___f_7024_, v_x_7025_);
    return v_res_7027_;
}
pub unsafe fn l_Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__3___redArg(
    mut v_q_7029_: *mut LeanObject,
    mut v___y_7030_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_eList_7032_: *mut LeanObject = core::ptr::null_mut();
    let mut v_dList_7033_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7034_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7035_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_7036_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7037_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7038_: u8 = 0;
    let mut v___x_7039_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_7040_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7041_: *mut LeanObject = core::ptr::null_mut();
    v_eList_7032_ = lean_ctor_get(v_q_7029_, 0);
    lean_inc(v_eList_7032_);
    v_dList_7033_ = lean_ctor_get(v_q_7029_, 1);
    lean_inc(v_dList_7033_);
    lean_dec_ref(v_q_7029_);
    v___x_7034_ = lean_box(0);
    v___x_7035_ = l_List_filterAuxM___at___00Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__3_spec__3___redArg(v_dList_7033_, v___x_7034_);
    v___f_7036_ = l_Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__3___redArg___closed__0;
    v___x_7037_ = lean_unsigned_to_nat(0);
    v___x_7038_ = 0;
    v___x_7039_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(
        lean_box(0),
        lean_box(0),
        v___x_7037_,
        v___x_7038_,
        v___x_7035_,
        v___f_7036_,
    );
    v___f_7040_ = lean_alloc_closure(l_Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__3___redArg___lam__1___boxed as *mut core::ffi::c_void, 5, 3);
    lean_closure_set(v___f_7040_, 0, v_eList_7032_);
    lean_closure_set(v___f_7040_, 1, v___x_7034_);
    lean_closure_set(v___f_7040_, 2, v___f_7036_);
    v___x_7041_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(
        lean_box(0),
        lean_box(0),
        v___x_7037_,
        v___x_7038_,
        v___x_7039_,
        v___f_7040_,
    );
    return v___x_7041_;
}
pub unsafe fn l_Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__3___redArg___boxed(
    mut v_q_7042_: *mut LeanObject,
    mut v___y_7043_: *mut LeanObject,
    mut v___y_7044_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_7045_: *mut LeanObject = core::ptr::null_mut();
    v_res_7045_ = l_Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__3___redArg(v_q_7042_, v___y_7043_);
    lean_dec(v___y_7043_);
    return v_res_7045_;
}
pub unsafe fn l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector___redArg___lam__9(
    mut v___y_7046_: *mut LeanObject,
    mut v_x_7047_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_7049_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7051_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_7052_: u8 = 0;
    let mut v___x_7054_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7055_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7056_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7057_: u8 = 0;
    let mut v_a_7058_: *mut LeanObject = core::ptr::null_mut();
    let mut v_values_7059_: *mut LeanObject = core::ptr::null_mut();
    let mut v_consumers_7060_: *mut LeanObject = core::ptr::null_mut();
    let mut v_closed_7061_: u8 = 0;
    let mut v___x_7062_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7063_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_7064_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7065_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7066_: u8 = 0;
    let mut v___x_7067_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_7047_) == 0 {
                    v_a_7049_ = lean_ctor_get(v_x_7047_, 0);
                    v_isSharedCheck_7057_ = (!lean_is_exclusive(v_x_7047_)) as u8;
                    if v_isSharedCheck_7057_ == 0 {
                        v___x_7051_ = v_x_7047_;
                        v_isShared_7052_ = v_isSharedCheck_7057_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_7049_);
                        lean_dec(v_x_7047_);
                        v___x_7051_ = lean_box(0);
                        v_isShared_7052_ = v_isSharedCheck_7057_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_7058_ = lean_ctor_get(v_x_7047_, 0);
                    lean_inc(v_a_7058_);
                    lean_dec_ref_known(v_x_7047_, 1);
                    v_values_7059_ = lean_ctor_get(v_a_7058_, 0);
                    lean_inc_ref(v_values_7059_);
                    v_consumers_7060_ = lean_ctor_get(v_a_7058_, 1);
                    lean_inc_ref(v_consumers_7060_);
                    v_closed_7061_ = lean_ctor_get_uint8(
                        v_a_7058_,
                        (core::mem::size_of::<*mut LeanObject>() * 2) as u32,
                    );
                    lean_dec(v_a_7058_);
                    v___x_7062_ = l_Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__3___redArg(v_consumers_7060_, v___y_7046_);
                    v___x_7063_ = lean_box((v_closed_7061_) as usize);
                    lean_inc(v___y_7046_);
                    v___f_7064_ = lean_alloc_closure(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector___redArg___lam__8___boxed as *mut core::ffi::c_void, 5, 3);
                    lean_closure_set(v___f_7064_, 0, v_values_7059_);
                    lean_closure_set(v___f_7064_, 1, v___x_7063_);
                    lean_closure_set(v___f_7064_, 2, v___y_7046_);
                    v___x_7065_ = lean_unsigned_to_nat(0);
                    v___x_7066_ = 0;
                    v___x_7067_ =
                        l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(
                            lean_box(0),
                            lean_box(0),
                            v___x_7065_,
                            v___x_7066_,
                            v___x_7062_,
                            v___f_7064_,
                        );
                    return v___x_7067_;
                }
            }
            1 => {
                if v_isShared_7052_ == 0 {
                    v___x_7054_ = v___x_7051_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_7056_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_7056_, 0, v_a_7049_);
                    v___x_7054_ = v_reuseFailAlloc_7056_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_7055_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_7055_, 0, v___x_7054_);
                return v___x_7055_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector___redArg___lam__9___boxed(
    mut v___y_7068_: *mut LeanObject,
    mut v_x_7069_: *mut LeanObject,
    mut v___y_7070_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_7071_: *mut LeanObject = core::ptr::null_mut();
    v_res_7071_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector___redArg___lam__9(v___y_7068_, v_x_7069_);
    lean_dec(v___y_7068_);
    return v_res_7071_;
}
pub unsafe fn l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector___redArg___lam__10(
    mut v___y_7072_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_7074_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_7075_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7076_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7077_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7078_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7079_: u8 = 0;
    let mut v___x_7080_: *mut LeanObject = core::ptr::null_mut();
    v___x_7074_ = lean_st_ref_get(v___y_7072_);
    lean_inc(v___y_7072_);
    v___f_7075_ = lean_alloc_closure(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector___redArg___lam__9___boxed as *mut core::ffi::c_void, 3, 1);
    lean_closure_set(v___f_7075_, 0, v___y_7072_);
    v___x_7076_ = lean_alloc_ctor(1, 1, (0) as u32);
    lean_ctor_set(v___x_7076_, 0, v___x_7074_);
    v___x_7077_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_7077_, 0, v___x_7076_);
    v___x_7078_ = lean_unsigned_to_nat(0);
    v___x_7079_ = 0;
    v___x_7080_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(
        lean_box(0),
        lean_box(0),
        v___x_7078_,
        v___x_7079_,
        v___x_7077_,
        v___f_7075_,
    );
    return v___x_7080_;
}
pub unsafe fn l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector___redArg___lam__10___boxed(
    mut v___y_7081_: *mut LeanObject,
    mut v___y_7082_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_7083_: *mut LeanObject = core::ptr::null_mut();
    v_res_7083_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector___redArg___lam__10(v___y_7081_);
    lean_dec(v___y_7081_);
    return v_res_7083_;
}
pub unsafe fn l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector___redArg(
    mut v_ch_7090_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_7091_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_7092_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_7093_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_7094_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7095_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7096_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7097_: *mut LeanObject = core::ptr::null_mut();
    v___f_7091_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector___redArg___closed__1;
    lean_inc_ref_n(v_ch_7090_, 2);
    v___f_7092_ = lean_alloc_closure(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector___redArg___lam__5___boxed as *mut core::ffi::c_void, 4, 2);
    lean_closure_set(v___f_7092_, 0, v___f_7091_);
    lean_closure_set(v___f_7092_, 1, v_ch_7090_);
    v___f_7093_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector___redArg___closed__2;
    v___f_7094_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector___redArg___closed__3;
    v___x_7095_ = lean_alloc_closure(l_Std_Mutex_atomically___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__2___boxed as *mut core::ffi::c_void, 5, 4);
    lean_closure_set(v___x_7095_, 0, lean_box(0));
    lean_closure_set(v___x_7095_, 1, lean_box(0));
    lean_closure_set(v___x_7095_, 2, v_ch_7090_);
    lean_closure_set(v___x_7095_, 3, v___f_7093_);
    v___x_7096_ = lean_alloc_closure(l_Std_Mutex_atomically___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__2___boxed as *mut core::ffi::c_void, 5, 4);
    lean_closure_set(v___x_7096_, 0, lean_box(0));
    lean_closure_set(v___x_7096_, 1, lean_box(0));
    lean_closure_set(v___x_7096_, 2, v_ch_7090_);
    lean_closure_set(v___x_7096_, 3, v___f_7094_);
    v___x_7097_ = lean_alloc_ctor(0, 3, (0) as u32);
    lean_ctor_set(v___x_7097_, 0, v___x_7095_);
    lean_ctor_set(v___x_7097_, 1, v___f_7092_);
    lean_ctor_set(v___x_7097_, 2, v___x_7096_);
    return v___x_7097_;
}
pub unsafe fn l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector(
    mut v_00_u03b1_7098_: *mut LeanObject,
    mut v_ch_7099_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_7100_: *mut LeanObject = core::ptr::null_mut();
    v___x_7100_ =
        l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector___redArg(
            v_ch_7099_,
        );
    return v___x_7100_;
}
pub unsafe fn l_Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__3(
    mut v_00_u03b1_7101_: *mut LeanObject,
    mut v_q_7102_: *mut LeanObject,
    mut v___y_7103_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_7105_: *mut LeanObject = core::ptr::null_mut();
    v___x_7105_ = l_Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__3___redArg(v_q_7102_, v___y_7103_);
    return v___x_7105_;
}
pub unsafe fn l_Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__3___boxed(
    mut v_00_u03b1_7106_: *mut LeanObject,
    mut v_q_7107_: *mut LeanObject,
    mut v___y_7108_: *mut LeanObject,
    mut v___y_7109_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_7110_: *mut LeanObject = core::ptr::null_mut();
    v_res_7110_ = l_Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__3(v_00_u03b1_7106_, v_q_7107_, v___y_7108_);
    lean_dec(v___y_7108_);
    return v_res_7110_;
}
pub unsafe fn l_List_filterAuxM___at___00Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__3_spec__3(
    mut v_00_u03b1_7111_: *mut LeanObject,
    mut v_x_7112_: *mut LeanObject,
    mut v_x_7113_: *mut LeanObject,
    mut v___y_7114_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_7116_: *mut LeanObject = core::ptr::null_mut();
    v___x_7116_ = l_List_filterAuxM___at___00Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__3_spec__3___redArg(v_x_7112_, v_x_7113_);
    return v___x_7116_;
}
pub unsafe fn l_List_filterAuxM___at___00Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__3_spec__3___boxed(
    mut v_00_u03b1_7117_: *mut LeanObject,
    mut v_x_7118_: *mut LeanObject,
    mut v_x_7119_: *mut LeanObject,
    mut v___y_7120_: *mut LeanObject,
    mut v___y_7121_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_7122_: *mut LeanObject = core::ptr::null_mut();
    v_res_7122_ = l_List_filterAuxM___at___00Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__3_spec__3(v_00_u03b1_7117_, v_x_7118_, v_x_7119_, v___y_7120_);
    lean_dec(v___y_7120_);
    return v_res_7122_;
}
pub unsafe fn _init_l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_new___redArg___closed__0()
-> *mut LeanObject {
    let mut v___x_7123_: *mut LeanObject = core::ptr::null_mut();
    v___x_7123_ = l_Std_Queue_empty(lean_box(0));
    return v___x_7123_;
}
pub unsafe fn _init_l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_new___redArg___closed__1()
-> *mut LeanObject {
    let mut v___x_7124_: u8 = 0;
    let mut v___x_7125_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7126_: *mut LeanObject = core::ptr::null_mut();
    v___x_7124_ = 0;
    v___x_7125_ = lean_obj_once(
        core::ptr::addr_of_mut!(
            l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_new___redArg___closed__0
        ),
        core::ptr::addr_of_mut!(
            l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_new___redArg___closed__0_once
        ),
        _init_l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_new___redArg___closed__0,
    );
    v___x_7126_ = lean_alloc_ctor(0, 2, (1) as u32);
    lean_ctor_set(v___x_7126_, 0, v___x_7125_);
    lean_ctor_set(v___x_7126_, 1, v___x_7125_);
    lean_ctor_set_uint8(
        v___x_7126_,
        (core::mem::size_of::<*mut LeanObject>() * 2) as u32,
        v___x_7124_,
    );
    return v___x_7126_;
}
pub unsafe fn l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_new___redArg()
-> *mut LeanObject {
    let mut v___x_7128_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7129_: *mut LeanObject = core::ptr::null_mut();
    v___x_7128_ = lean_obj_once(
        core::ptr::addr_of_mut!(
            l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_new___redArg___closed__1
        ),
        core::ptr::addr_of_mut!(
            l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_new___redArg___closed__1_once
        ),
        _init_l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_new___redArg___closed__1,
    );
    v___x_7129_ = l_Std_Mutex_new___redArg(v___x_7128_);
    return v___x_7129_;
}
pub unsafe fn l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_new___redArg___boxed(
    mut v_a_7130_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_7131_: *mut LeanObject = core::ptr::null_mut();
    v_res_7131_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_new___redArg();
    return v_res_7131_;
}
pub unsafe fn l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_new(
    mut v_00_u03b1_7132_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_7134_: *mut LeanObject = core::ptr::null_mut();
    v___x_7134_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_new___redArg();
    return v___x_7134_;
}
pub unsafe fn l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_new___boxed(
    mut v_00_u03b1_7135_: *mut LeanObject,
    mut v_a_7136_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_7137_: *mut LeanObject = core::ptr::null_mut();
    v_res_7137_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_new(v_00_u03b1_7135_);
    return v_res_7137_;
}
pub unsafe fn l___private_Init_While_0__whileM_erased___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_trySend_x27_spec__0___redArg(
    mut v_v_7147_: *mut LeanObject,
    mut v___y_7148_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_7150_: *mut LeanObject = core::ptr::null_mut();
    let mut v_producers_7151_: *mut LeanObject = core::ptr::null_mut();
    let mut v_consumers_7152_: *mut LeanObject = core::ptr::null_mut();
    let mut v_closed_7153_: u8 = 0;
    let mut v___x_7155_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_7156_: u8 = 0;
    let mut v___x_7157_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_7158_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7160_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_7161_: u8 = 0;
    let mut v_fst_7162_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_7163_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7165_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7166_: u8 = 0;
    let mut v___x_7168_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7169_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7171_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7172_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7173_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7174_: u8 = 0;
    let mut v___x_7175_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7176_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_7150_ = lean_st_ref_get(v___y_7148_);
                v_producers_7151_ = lean_ctor_get(v___x_7150_, 0);
                v_consumers_7152_ = lean_ctor_get(v___x_7150_, 1);
                v_closed_7153_ = lean_ctor_get_uint8(
                    v___x_7150_,
                    (core::mem::size_of::<*mut LeanObject>() * 2) as u32,
                );
                v_isSharedCheck_7176_ = (!lean_is_exclusive(v___x_7150_)) as u8;
                if v_isSharedCheck_7176_ == 0 {
                    v___x_7155_ = v___x_7150_;
                    v_isShared_7156_ = v_isSharedCheck_7176_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_consumers_7152_);
                    lean_inc(v_producers_7151_);
                    lean_dec(v___x_7150_);
                    v___x_7155_ = lean_box(0);
                    v_isShared_7156_ = v_isSharedCheck_7176_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_7157_ = l_Std_Queue_dequeue_x3f___redArg(v_consumers_7152_);
                if lean_obj_tag(v___x_7157_) == 1 {
                    v_val_7158_ = lean_ctor_get(v___x_7157_, 0);
                    v_isSharedCheck_7174_ = (!lean_is_exclusive(v___x_7157_)) as u8;
                    if v_isSharedCheck_7174_ == 0 {
                        v___x_7160_ = v___x_7157_;
                        v_isShared_7161_ = v_isSharedCheck_7174_;
                        state = 2;
                        continue;
                    } else {
                        lean_inc(v_val_7158_);
                        lean_dec(v___x_7157_);
                        v___x_7160_ = lean_box(0);
                        v_isShared_7161_ = v_isSharedCheck_7174_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_dec(v___x_7157_);
                    lean_del_object(v___x_7155_);
                    lean_dec_ref(v_producers_7151_);
                    lean_dec(v_v_7147_);
                    v___x_7175_ = l___private_Init_While_0__whileM_erased___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_trySend_x27_spec__0___redArg___closed__2;
                    return v___x_7175_;
                }
            }
            2 => {
                v_fst_7162_ = lean_ctor_get(v_val_7158_, 0);
                lean_inc(v_fst_7162_);
                v_snd_7163_ = lean_ctor_get(v_val_7158_, 1);
                lean_inc(v_snd_7163_);
                lean_dec(v_val_7158_);
                lean_inc(v_v_7147_);
                if v_isShared_7161_ == 0 {
                    lean_ctor_set(v___x_7160_, 0, v_v_7147_);
                    v___x_7165_ = v___x_7160_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_7173_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_7173_, 0, v_v_7147_);
                    v___x_7165_ = v_reuseFailAlloc_7173_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_7166_ =
                    l___private_Std_Sync_Channel_0__Std_CloseableChannel_Consumer_resolve___redArg(
                        v_fst_7162_,
                        v___x_7165_,
                    );
                lean_dec(v_fst_7162_);
                if v_isShared_7156_ == 0 {
                    lean_ctor_set(v___x_7155_, 1, v_snd_7163_);
                    v___x_7168_ = v___x_7155_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_7172_ = lean_alloc_ctor(0, 2, (1) as u32);
                    lean_ctor_set(v_reuseFailAlloc_7172_, 0, v_producers_7151_);
                    lean_ctor_set(v_reuseFailAlloc_7172_, 1, v_snd_7163_);
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_7172_,
                        (core::mem::size_of::<*mut LeanObject>() * 2) as u32,
                        v_closed_7153_,
                    );
                    v___x_7168_ = v_reuseFailAlloc_7172_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_7169_ = lean_st_ref_set(v___y_7148_, v___x_7168_);
                if v___x_7166_ == 0 {
                    state = 0;
                    continue;
                } else {
                    lean_dec(v_v_7147_);
                    v___x_7171_ = l___private_Init_While_0__whileM_erased___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_trySend_x27_spec__0___redArg___closed__0;
                    return v___x_7171_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_While_0__whileM_erased___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_trySend_x27_spec__0___redArg___boxed(
    mut v_v_7177_: *mut LeanObject,
    mut v___y_7178_: *mut LeanObject,
    mut v___y_7179_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_7180_: *mut LeanObject = core::ptr::null_mut();
    v_res_7180_ = l___private_Init_While_0__whileM_erased___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_trySend_x27_spec__0___redArg(v_v_7177_, v___y_7178_);
    lean_dec(v___y_7178_);
    return v_res_7180_;
}
pub unsafe fn l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_trySend_x27___redArg(
    mut v_v_7181_: *mut LeanObject,
    mut v_a_7182_: *mut LeanObject,
) -> u8 {
    let mut v___x_7184_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_7185_: *mut LeanObject = core::ptr::null_mut();
    v___x_7184_ = l___private_Init_While_0__whileM_erased___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_trySend_x27_spec__0___redArg(v_v_7181_, v_a_7182_);
    v_fst_7185_ = lean_ctor_get(v___x_7184_, 0);
    lean_inc(v_fst_7185_);
    lean_dec_ref(v___x_7184_);
    if lean_obj_tag(v_fst_7185_) == 0 {
        let mut v___x_7186_: u8 = 0;
        v___x_7186_ = 1;
        return v___x_7186_;
    } else {
        let mut v_val_7187_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_7188_: u8 = 0;
        v_val_7187_ = lean_ctor_get(v_fst_7185_, 0);
        lean_inc(v_val_7187_);
        lean_dec_ref_known(v_fst_7185_, 1);
        v___x_7188_ = (lean_unbox(v_val_7187_) as u8);
        lean_dec(v_val_7187_);
        return v___x_7188_;
    }
}
pub unsafe fn l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_trySend_x27___redArg___boxed(
    mut v_v_7189_: *mut LeanObject,
    mut v_a_7190_: *mut LeanObject,
    mut v_a_7191_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_7192_: u8 = 0;
    let mut v_r_7193_: *mut LeanObject = core::ptr::null_mut();
    v_res_7192_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_trySend_x27___redArg(
        v_v_7189_, v_a_7190_,
    );
    lean_dec(v_a_7190_);
    v_r_7193_ = lean_box((v_res_7192_) as usize);
    return v_r_7193_;
}
pub unsafe fn l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_trySend_x27(
    mut v_00_u03b1_7194_: *mut LeanObject,
    mut v_v_7195_: *mut LeanObject,
    mut v_a_7196_: *mut LeanObject,
) -> u8 {
    let mut v___x_7198_: u8 = 0;
    v___x_7198_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_trySend_x27___redArg(
        v_v_7195_, v_a_7196_,
    );
    return v___x_7198_;
}
pub unsafe fn l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_trySend_x27___boxed(
    mut v_00_u03b1_7199_: *mut LeanObject,
    mut v_v_7200_: *mut LeanObject,
    mut v_a_7201_: *mut LeanObject,
    mut v_a_7202_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_7203_: u8 = 0;
    let mut v_r_7204_: *mut LeanObject = core::ptr::null_mut();
    v_res_7203_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_trySend_x27(
        v_00_u03b1_7199_,
        v_v_7200_,
        v_a_7201_,
    );
    lean_dec(v_a_7201_);
    v_r_7204_ = lean_box((v_res_7203_) as usize);
    return v_r_7204_;
}
pub unsafe fn l___private_Init_While_0__whileM_erased___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_trySend_x27_spec__0(
    mut v_00_u03b1_7205_: *mut LeanObject,
    mut v_v_7206_: *mut LeanObject,
    mut v_inst_7207_: *mut LeanObject,
    mut v_a_7208_: *mut LeanObject,
    mut v___y_7209_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_7211_: *mut LeanObject = core::ptr::null_mut();
    v___x_7211_ = l___private_Init_While_0__whileM_erased___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_trySend_x27_spec__0___redArg(v_v_7206_, v___y_7209_);
    return v___x_7211_;
}
pub unsafe fn l___private_Init_While_0__whileM_erased___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_trySend_x27_spec__0___boxed(
    mut v_00_u03b1_7212_: *mut LeanObject,
    mut v_v_7213_: *mut LeanObject,
    mut v_inst_7214_: *mut LeanObject,
    mut v_a_7215_: *mut LeanObject,
    mut v___y_7216_: *mut LeanObject,
    mut v___y_7217_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_7218_: *mut LeanObject = core::ptr::null_mut();
    v_res_7218_ = l___private_Init_While_0__whileM_erased___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_trySend_x27_spec__0(v_00_u03b1_7212_, v_v_7213_, v_inst_7214_, v_a_7215_, v___y_7216_);
    lean_dec(v___y_7216_);
    lean_dec_ref(v_a_7215_);
    return v_res_7218_;
}
pub unsafe fn l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_trySend___redArg___lam__0(
    mut v_v_7219_: *mut LeanObject,
    mut v___y_7220_: *mut LeanObject,
) -> u8 {
    let mut v___x_7222_: *mut LeanObject = core::ptr::null_mut();
    let mut v_closed_7223_: u8 = 0;
    v___x_7222_ = lean_st_ref_get(v___y_7220_);
    v_closed_7223_ = lean_ctor_get_uint8(
        v___x_7222_,
        (core::mem::size_of::<*mut LeanObject>() * 2) as u32,
    );
    lean_dec(v___x_7222_);
    if v_closed_7223_ == 0 {
        let mut v___x_7224_: u8 = 0;
        v___x_7224_ =
            l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_trySend_x27___redArg(
                v_v_7219_,
                v___y_7220_,
            );
        return v___x_7224_;
    } else {
        let mut v___x_7225_: u8 = 0;
        lean_dec(v_v_7219_);
        v___x_7225_ = 0;
        return v___x_7225_;
    }
}
pub unsafe fn l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_trySend___redArg___lam__0___boxed(
    mut v_v_7226_: *mut LeanObject,
    mut v___y_7227_: *mut LeanObject,
    mut v___y_7228_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_7229_: u8 = 0;
    let mut v_r_7230_: *mut LeanObject = core::ptr::null_mut();
    v_res_7229_ =
        l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_trySend___redArg___lam__0(
            v_v_7226_,
            v___y_7227_,
        );
    lean_dec(v___y_7227_);
    v_r_7230_ = lean_box((v_res_7229_) as usize);
    return v_r_7230_;
}
pub unsafe fn l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_trySend___redArg(
    mut v_ch_7231_: *mut LeanObject,
    mut v_v_7232_: *mut LeanObject,
) -> u8 {
    let mut v___f_7234_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7235_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7236_: u8 = 0;
    v___f_7234_ = lean_alloc_closure(
        l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_trySend___redArg___lam__0___boxed
            as *mut core::ffi::c_void,
        3,
        1,
    );
    lean_closure_set(v___f_7234_, 0, v_v_7232_);
    v___x_7235_ = l_Std_Mutex_atomically___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_trySend_spec__1___redArg(v_ch_7231_, v___f_7234_);
    v___x_7236_ = (lean_unbox(v___x_7235_) as u8);
    lean_dec(v___x_7235_);
    return v___x_7236_;
}
pub unsafe fn l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_trySend___redArg___boxed(
    mut v_ch_7237_: *mut LeanObject,
    mut v_v_7238_: *mut LeanObject,
    mut v_a_7239_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_7240_: u8 = 0;
    let mut v_r_7241_: *mut LeanObject = core::ptr::null_mut();
    v_res_7240_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_trySend___redArg(
        v_ch_7237_, v_v_7238_,
    );
    v_r_7241_ = lean_box((v_res_7240_) as usize);
    return v_r_7241_;
}
pub unsafe fn l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_trySend(
    mut v_00_u03b1_7242_: *mut LeanObject,
    mut v_ch_7243_: *mut LeanObject,
    mut v_v_7244_: *mut LeanObject,
) -> u8 {
    let mut v___x_7246_: u8 = 0;
    v___x_7246_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_trySend___redArg(
        v_ch_7243_, v_v_7244_,
    );
    return v___x_7246_;
}
pub unsafe fn l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_trySend___boxed(
    mut v_00_u03b1_7247_: *mut LeanObject,
    mut v_ch_7248_: *mut LeanObject,
    mut v_v_7249_: *mut LeanObject,
    mut v_a_7250_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_7251_: u8 = 0;
    let mut v_r_7252_: *mut LeanObject = core::ptr::null_mut();
    v_res_7251_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_trySend(
        v_00_u03b1_7247_,
        v_ch_7248_,
        v_v_7249_,
    );
    v_r_7252_ = lean_box((v_res_7251_) as usize);
    return v_r_7252_;
}
pub unsafe fn l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_send___redArg___lam__0(
    mut v_x_7253_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_7255_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_7256_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7257_: u8 = 0;
    let mut v___x_7258_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_7253_) == 0 {
                    state = 1;
                    continue;
                } else {
                    v_val_7256_ = lean_ctor_get(v_x_7253_, 0);
                    v___x_7257_ = (lean_unbox(v_val_7256_) as u8);
                    if v___x_7257_ == 0 {
                        state = 1;
                        continue;
                    } else {
                        v___x_7258_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_send___redArg___closed__2;
                        return v___x_7258_;
                    }
                }
            }
            1 => {
                v___x_7255_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_send___redArg___closed__0;
                return v___x_7255_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_send___redArg___lam__0___boxed(
    mut v_x_7259_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_7260_: *mut LeanObject = core::ptr::null_mut();
    v_res_7260_ =
        l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_send___redArg___lam__0(v_x_7259_);
    lean_dec(v_x_7259_);
    return v_res_7260_;
}
pub unsafe fn l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_send___redArg___lam__1(
    mut v_v_7261_: *mut LeanObject,
    mut v___f_7262_: *mut LeanObject,
    mut v___y_7263_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_7265_: *mut LeanObject = core::ptr::null_mut();
    let mut v_closed_7266_: u8 = 0;
    let mut v___x_7267_: u8 = 0;
    let mut v___x_7268_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7269_: *mut LeanObject = core::ptr::null_mut();
    let mut v_producers_7270_: *mut LeanObject = core::ptr::null_mut();
    let mut v_consumers_7271_: *mut LeanObject = core::ptr::null_mut();
    let mut v_closed_7272_: u8 = 0;
    let mut v___x_7274_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_7275_: u8 = 0;
    let mut v___x_7276_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7277_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7279_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7280_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7281_: u8 = 0;
    let mut v___x_7282_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7283_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7284_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7285_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7286_: u8 = 0;
    let mut v___x_7287_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7288_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_7265_ = lean_st_ref_get(v___y_7263_);
                v_closed_7266_ = lean_ctor_get_uint8(
                    v___x_7265_,
                    (core::mem::size_of::<*mut LeanObject>() * 2) as u32,
                );
                lean_dec(v___x_7265_);
                if v_closed_7266_ == 0 {
                    lean_inc(v_v_7261_);
                    v___x_7267_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_trySend_x27___redArg(v_v_7261_, v___y_7263_);
                    if v___x_7267_ == 0 {
                        v___x_7268_ = lean_io_promise_new();
                        v___x_7269_ = lean_st_ref_take(v___y_7263_);
                        v_producers_7270_ = lean_ctor_get(v___x_7269_, 0);
                        v_consumers_7271_ = lean_ctor_get(v___x_7269_, 1);
                        v_closed_7272_ = lean_ctor_get_uint8(
                            v___x_7269_,
                            (core::mem::size_of::<*mut LeanObject>() * 2) as u32,
                        );
                        v_isSharedCheck_7286_ = (!lean_is_exclusive(v___x_7269_)) as u8;
                        if v_isSharedCheck_7286_ == 0 {
                            v___x_7274_ = v___x_7269_;
                            v_isShared_7275_ = v_isSharedCheck_7286_;
                            state = 1;
                            continue;
                        } else {
                            lean_inc(v_consumers_7271_);
                            lean_inc(v_producers_7270_);
                            lean_dec(v___x_7269_);
                            v___x_7274_ = lean_box(0);
                            v_isShared_7275_ = v_isSharedCheck_7286_;
                            state = 1;
                            continue;
                        }
                    } else {
                        lean_dec_ref(v___f_7262_);
                        lean_dec(v_v_7261_);
                        v___x_7287_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_send___redArg___closed__3), core::ptr::addr_of_mut!(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_send___redArg___closed__3_once), _init_l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_send___redArg___closed__3);
                        return v___x_7287_;
                    }
                } else {
                    lean_dec_ref(v___f_7262_);
                    lean_dec(v_v_7261_);
                    v___x_7288_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_send___redArg___closed__1), core::ptr::addr_of_mut!(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_send___redArg___closed__1_once), _init_l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_send___redArg___closed__1);
                    return v___x_7288_;
                }
            }
            1 => {
                lean_inc(v___x_7268_);
                v___x_7276_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_7276_, 0, v_v_7261_);
                lean_ctor_set(v___x_7276_, 1, v___x_7268_);
                v___x_7277_ = l_Std_Queue_enqueue___redArg(v___x_7276_, v_producers_7270_);
                if v_isShared_7275_ == 0 {
                    lean_ctor_set(v___x_7274_, 0, v___x_7277_);
                    v___x_7279_ = v___x_7274_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_7285_ = lean_alloc_ctor(0, 2, (1) as u32);
                    lean_ctor_set(v_reuseFailAlloc_7285_, 0, v___x_7277_);
                    lean_ctor_set(v_reuseFailAlloc_7285_, 1, v_consumers_7271_);
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_7285_,
                        (core::mem::size_of::<*mut LeanObject>() * 2) as u32,
                        v_closed_7272_,
                    );
                    v___x_7279_ = v_reuseFailAlloc_7285_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_7280_ = lean_st_ref_set(v___y_7263_, v___x_7279_);
                v___x_7281_ = 1;
                v___x_7282_ = lean_io_promise_result_opt(v___x_7268_);
                lean_dec(v___x_7268_);
                v___x_7283_ = lean_unsigned_to_nat(0);
                v___x_7284_ = lean_task_map(v___f_7262_, v___x_7282_, v___x_7283_, v___x_7281_);
                return v___x_7284_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_send___redArg___lam__1___boxed(
    mut v_v_7289_: *mut LeanObject,
    mut v___f_7290_: *mut LeanObject,
    mut v___y_7291_: *mut LeanObject,
    mut v___y_7292_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_7293_: *mut LeanObject = core::ptr::null_mut();
    v_res_7293_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_send___redArg___lam__1(
        v_v_7289_,
        v___f_7290_,
        v___y_7291_,
    );
    lean_dec(v___y_7291_);
    return v_res_7293_;
}
pub unsafe fn l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_send___redArg(
    mut v_ch_7295_: *mut LeanObject,
    mut v_v_7296_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_7298_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_7299_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7300_: *mut LeanObject = core::ptr::null_mut();
    v___f_7298_ =
        l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_send___redArg___closed__0;
    v___f_7299_ = lean_alloc_closure(
        l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_send___redArg___lam__1___boxed
            as *mut core::ffi::c_void,
        4,
        2,
    );
    lean_closure_set(v___f_7299_, 0, v_v_7296_);
    lean_closure_set(v___f_7299_, 1, v___f_7298_);
    v___x_7300_ = l_Std_Mutex_atomically___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_trySend_spec__1___redArg(v_ch_7295_, v___f_7299_);
    return v___x_7300_;
}
pub unsafe fn l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_send___redArg___boxed(
    mut v_ch_7301_: *mut LeanObject,
    mut v_v_7302_: *mut LeanObject,
    mut v_a_7303_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_7304_: *mut LeanObject = core::ptr::null_mut();
    v_res_7304_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_send___redArg(
        v_ch_7301_, v_v_7302_,
    );
    return v_res_7304_;
}
pub unsafe fn l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_send(
    mut v_00_u03b1_7305_: *mut LeanObject,
    mut v_ch_7306_: *mut LeanObject,
    mut v_v_7307_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_7309_: *mut LeanObject = core::ptr::null_mut();
    v___x_7309_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_send___redArg(
        v_ch_7306_, v_v_7307_,
    );
    return v___x_7309_;
}
pub unsafe fn l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_send___boxed(
    mut v_00_u03b1_7310_: *mut LeanObject,
    mut v_ch_7311_: *mut LeanObject,
    mut v_v_7312_: *mut LeanObject,
    mut v_a_7313_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_7314_: *mut LeanObject = core::ptr::null_mut();
    v_res_7314_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_send(
        v_00_u03b1_7310_,
        v_ch_7311_,
        v_v_7312_,
    );
    return v_res_7314_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_close_spec__0___redArg(
    mut v_as_7315_: *mut LeanObject,
    mut v_sz_7316_: usize,
    mut v_i_7317_: usize,
    mut v_b_7318_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_7320_: u8 = 0;
    let mut v___x_7321_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_7322_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7323_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7324_: u8 = 0;
    let mut v___x_7325_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7326_: usize = 0;
    let mut v___x_7327_: usize = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_7320_ = lean_usize_dec_lt(v_i_7317_, v_sz_7316_);
                if v___x_7320_ == 0 {
                    v___x_7321_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_7321_, 0, v_b_7318_);
                    return v___x_7321_;
                } else {
                    v_a_7322_ = lean_array_uget_borrowed(v_as_7315_, v_i_7317_);
                    v___x_7323_ = lean_box(0);
                    v___x_7324_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Consumer_resolve___redArg(v_a_7322_, v___x_7323_);
                    v___x_7325_ = lean_box(0);
                    v___x_7326_ = 1usize;
                    v___x_7327_ = lean_usize_add(v_i_7317_, v___x_7326_);
                    v_i_7317_ = v___x_7327_;
                    v_b_7318_ = v___x_7325_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_close_spec__0___redArg___boxed(
    mut v_as_7329_: *mut LeanObject,
    mut v_sz_7330_: *mut LeanObject,
    mut v_i_7331_: *mut LeanObject,
    mut v_b_7332_: *mut LeanObject,
    mut v___y_7333_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sz_boxed_7334_: usize = 0;
    let mut v_i_boxed_7335_: usize = 0;
    let mut v_res_7336_: *mut LeanObject = core::ptr::null_mut();
    v_sz_boxed_7334_ = lean_unbox_usize(v_sz_7330_);
    lean_dec(v_sz_7330_);
    v_i_boxed_7335_ = lean_unbox_usize(v_i_7331_);
    lean_dec(v_i_7331_);
    v_res_7336_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_close_spec__0___redArg(v_as_7329_, v_sz_boxed_7334_, v_i_boxed_7335_, v_b_7332_);
    lean_dec_ref(v_as_7329_);
    return v_res_7336_;
}
pub unsafe fn l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_close___redArg___lam__0(
    mut v___y_7337_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_7339_: *mut LeanObject = core::ptr::null_mut();
    let mut v_closed_7340_: u8 = 0;
    let mut v_producers_7341_: *mut LeanObject = core::ptr::null_mut();
    let mut v_consumers_7342_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7344_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_7345_: u8 = 0;
    let mut v___x_7346_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7347_: *mut LeanObject = core::ptr::null_mut();
    let mut v_sz_7348_: usize = 0;
    let mut v___x_7349_: usize = 0;
    let mut v___x_7350_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7352_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_7353_: u8 = 0;
    let mut v___x_7354_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7355_: u8 = 0;
    let mut v___x_7357_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7358_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7360_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7361_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7362_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7363_: u8 = 0;
    let mut v_unused_7364_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7365_: u8 = 0;
    let mut v___x_7366_: u8 = 0;
    let mut v___x_7367_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7368_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_7339_ = lean_st_ref_get(v___y_7337_);
                v_closed_7340_ = lean_ctor_get_uint8(
                    v___x_7339_,
                    (core::mem::size_of::<*mut LeanObject>() * 2) as u32,
                );
                if v_closed_7340_ == 0 {
                    v_producers_7341_ = lean_ctor_get(v___x_7339_, 0);
                    v_consumers_7342_ = lean_ctor_get(v___x_7339_, 1);
                    v_isSharedCheck_7365_ = (!lean_is_exclusive(v___x_7339_)) as u8;
                    if v_isSharedCheck_7365_ == 0 {
                        v___x_7344_ = v___x_7339_;
                        v_isShared_7345_ = v_isSharedCheck_7365_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_consumers_7342_);
                        lean_inc(v_producers_7341_);
                        lean_dec(v___x_7339_);
                        v___x_7344_ = lean_box(0);
                        v_isShared_7345_ = v_isSharedCheck_7365_;
                        state = 1;
                        continue;
                    }
                } else {
                    lean_dec(v___x_7339_);
                    v___x_7366_ = 1;
                    v___x_7367_ = lean_box((v___x_7366_) as usize);
                    v___x_7368_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v___x_7368_, 0, v___x_7367_);
                    return v___x_7368_;
                }
            }
            1 => {
                v___x_7346_ = l_Std_Queue_toArray___redArg(v_consumers_7342_);
                v___x_7347_ = lean_box(0);
                v_sz_7348_ = lean_array_size(v___x_7346_);
                v___x_7349_ = 0usize;
                v___x_7350_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_close_spec__0___redArg(v___x_7346_, v_sz_7348_, v___x_7349_, v___x_7347_);
                lean_dec_ref(v___x_7346_);
                if lean_obj_tag(v___x_7350_) == 0 {
                    v_isSharedCheck_7363_ = (!lean_is_exclusive(v___x_7350_)) as u8;
                    if v_isSharedCheck_7363_ == 0 {
                        v_unused_7364_ = lean_ctor_get(v___x_7350_, 0);
                        lean_dec(v_unused_7364_);
                        v___x_7352_ = v___x_7350_;
                        v_isShared_7353_ = v_isSharedCheck_7363_;
                        state = 2;
                        continue;
                    } else {
                        lean_dec(v___x_7350_);
                        v___x_7352_ = lean_box(0);
                        v_isShared_7353_ = v_isSharedCheck_7363_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_7344_);
                    lean_dec_ref(v_producers_7341_);
                    return v___x_7350_;
                }
            }
            2 => {
                v___x_7354_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_close___redArg___lam__0___closed__0), core::ptr::addr_of_mut!(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_close___redArg___lam__0___closed__0_once), _init_l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_close___redArg___lam__0___closed__0);
                v___x_7355_ = 1;
                if v_isShared_7345_ == 0 {
                    lean_ctor_set(v___x_7344_, 1, v___x_7354_);
                    v___x_7357_ = v___x_7344_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_7362_ = lean_alloc_ctor(0, 2, (1) as u32);
                    lean_ctor_set(v_reuseFailAlloc_7362_, 0, v_producers_7341_);
                    lean_ctor_set(v_reuseFailAlloc_7362_, 1, v___x_7354_);
                    v___x_7357_ = v_reuseFailAlloc_7362_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                lean_ctor_set_uint8(
                    v___x_7357_,
                    (core::mem::size_of::<*mut LeanObject>() * 2) as u32,
                    v___x_7355_,
                );
                v___x_7358_ = lean_st_ref_set(v___y_7337_, v___x_7357_);
                if v_isShared_7353_ == 0 {
                    lean_ctor_set(v___x_7352_, 0, v___x_7347_);
                    v___x_7360_ = v___x_7352_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_7361_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_7361_, 0, v___x_7347_);
                    v___x_7360_ = v_reuseFailAlloc_7361_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_7360_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_close___redArg___lam__0___boxed(
    mut v___y_7369_: *mut LeanObject,
    mut v___y_7370_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_7371_: *mut LeanObject = core::ptr::null_mut();
    v_res_7371_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_close___redArg___lam__0(
        v___y_7369_,
    );
    lean_dec(v___y_7369_);
    return v_res_7371_;
}
pub unsafe fn l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_close___redArg(
    mut v_ch_7373_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_7375_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7376_: *mut LeanObject = core::ptr::null_mut();
    v___f_7375_ =
        l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_close___redArg___closed__0;
    v___x_7376_ = l_Std_Mutex_atomically___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_close_spec__1___redArg(v_ch_7373_, v___f_7375_);
    return v___x_7376_;
}
pub unsafe fn l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_close___redArg___boxed(
    mut v_ch_7377_: *mut LeanObject,
    mut v_a_7378_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_7379_: *mut LeanObject = core::ptr::null_mut();
    v_res_7379_ =
        l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_close___redArg(v_ch_7377_);
    return v_res_7379_;
}
pub unsafe fn l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_close(
    mut v_00_u03b1_7380_: *mut LeanObject,
    mut v_ch_7381_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_7383_: *mut LeanObject = core::ptr::null_mut();
    v___x_7383_ =
        l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_close___redArg(v_ch_7381_);
    return v___x_7383_;
}
pub unsafe fn l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_close___boxed(
    mut v_00_u03b1_7384_: *mut LeanObject,
    mut v_ch_7385_: *mut LeanObject,
    mut v_a_7386_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_7387_: *mut LeanObject = core::ptr::null_mut();
    v_res_7387_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_close(
        v_00_u03b1_7384_,
        v_ch_7385_,
    );
    return v_res_7387_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_close_spec__0(
    mut v_00_u03b1_7388_: *mut LeanObject,
    mut v_as_7389_: *mut LeanObject,
    mut v_sz_7390_: usize,
    mut v_i_7391_: usize,
    mut v_b_7392_: *mut LeanObject,
    mut v___y_7393_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_7395_: *mut LeanObject = core::ptr::null_mut();
    v___x_7395_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_close_spec__0___redArg(v_as_7389_, v_sz_7390_, v_i_7391_, v_b_7392_);
    return v___x_7395_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_close_spec__0___boxed(
    mut v_00_u03b1_7396_: *mut LeanObject,
    mut v_as_7397_: *mut LeanObject,
    mut v_sz_7398_: *mut LeanObject,
    mut v_i_7399_: *mut LeanObject,
    mut v_b_7400_: *mut LeanObject,
    mut v___y_7401_: *mut LeanObject,
    mut v___y_7402_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sz_boxed_7403_: usize = 0;
    let mut v_i_boxed_7404_: usize = 0;
    let mut v_res_7405_: *mut LeanObject = core::ptr::null_mut();
    v_sz_boxed_7403_ = lean_unbox_usize(v_sz_7398_);
    lean_dec(v_sz_7398_);
    v_i_boxed_7404_ = lean_unbox_usize(v_i_7399_);
    lean_dec(v_i_7399_);
    v_res_7405_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_close_spec__0(v_00_u03b1_7396_, v_as_7397_, v_sz_boxed_7403_, v_i_boxed_7404_, v_b_7400_, v___y_7401_);
    lean_dec(v___y_7401_);
    lean_dec_ref(v_as_7397_);
    return v_res_7405_;
}
pub unsafe fn l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_isClosed___redArg___lam__0(
    mut v___y_7406_: *mut LeanObject,
) -> u8 {
    let mut v___x_7408_: *mut LeanObject = core::ptr::null_mut();
    let mut v_closed_7409_: u8 = 0;
    v___x_7408_ = lean_st_ref_get(v___y_7406_);
    v_closed_7409_ = lean_ctor_get_uint8(
        v___x_7408_,
        (core::mem::size_of::<*mut LeanObject>() * 2) as u32,
    );
    lean_dec(v___x_7408_);
    return v_closed_7409_;
}
pub unsafe fn l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_isClosed___redArg___lam__0___boxed(
    mut v___y_7410_: *mut LeanObject,
    mut v___y_7411_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_7412_: u8 = 0;
    let mut v_r_7413_: *mut LeanObject = core::ptr::null_mut();
    v_res_7412_ =
        l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_isClosed___redArg___lam__0(
            v___y_7410_,
        );
    lean_dec(v___y_7410_);
    v_r_7413_ = lean_box((v_res_7412_) as usize);
    return v_r_7413_;
}
pub unsafe fn l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_isClosed___redArg(
    mut v_ch_7415_: *mut LeanObject,
) -> u8 {
    let mut v___f_7417_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7418_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7419_: u8 = 0;
    v___f_7417_ =
        l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_isClosed___redArg___closed__0;
    v___x_7418_ = l_Std_Mutex_atomically___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_trySend_spec__1___redArg(v_ch_7415_, v___f_7417_);
    v___x_7419_ = (lean_unbox(v___x_7418_) as u8);
    lean_dec(v___x_7418_);
    return v___x_7419_;
}
pub unsafe fn l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_isClosed___redArg___boxed(
    mut v_ch_7420_: *mut LeanObject,
    mut v_a_7421_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_7422_: u8 = 0;
    let mut v_r_7423_: *mut LeanObject = core::ptr::null_mut();
    v_res_7422_ =
        l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_isClosed___redArg(v_ch_7420_);
    v_r_7423_ = lean_box((v_res_7422_) as usize);
    return v_r_7423_;
}
pub unsafe fn l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_isClosed(
    mut v_00_u03b1_7424_: *mut LeanObject,
    mut v_ch_7425_: *mut LeanObject,
) -> u8 {
    let mut v___x_7427_: u8 = 0;
    v___x_7427_ =
        l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_isClosed___redArg(v_ch_7425_);
    return v___x_7427_;
}
pub unsafe fn l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_isClosed___boxed(
    mut v_00_u03b1_7428_: *mut LeanObject,
    mut v_ch_7429_: *mut LeanObject,
    mut v_a_7430_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_7431_: u8 = 0;
    let mut v_r_7432_: *mut LeanObject = core::ptr::null_mut();
    v_res_7431_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_isClosed(
        v_00_u03b1_7428_,
        v_ch_7429_,
    );
    v_r_7432_ = lean_box((v_res_7431_) as usize);
    return v_r_7432_;
}
pub unsafe fn l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_tryRecv_x27___redArg___lam__1(
    mut v_snd_7433_: *mut LeanObject,
    mut v_inst_7434_: *mut LeanObject,
    mut v_toBind_7435_: *mut LeanObject,
    mut v___f_7436_: *mut LeanObject,
    mut v_a_7437_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_7438_: u8 = 0;
    let mut v___x_7439_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7440_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7441_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7442_: *mut LeanObject = core::ptr::null_mut();
    v___x_7438_ = 1;
    v___x_7439_ = lean_box((v___x_7438_) as usize);
    v___x_7440_ = lean_alloc_closure(l_IO_Promise_resolve___boxed as *mut core::ffi::c_void, 4, 3);
    lean_closure_set(v___x_7440_, 0, lean_box(0));
    lean_closure_set(v___x_7440_, 1, v___x_7439_);
    lean_closure_set(v___x_7440_, 2, v_snd_7433_);
    v___x_7441_ = lean_apply_2(v_inst_7434_, lean_box(0), v___x_7440_);
    v___x_7442_ = lean_apply_4(
        v_toBind_7435_,
        lean_box(0),
        lean_box(0),
        v___x_7441_,
        v___f_7436_,
    );
    return v___x_7442_;
}
pub unsafe fn l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_tryRecv_x27___redArg___lam__0(
    mut v_toApplicative_7443_: *mut LeanObject,
    mut v_inst_7444_: *mut LeanObject,
    mut v_toBind_7445_: *mut LeanObject,
    mut v_a_7446_: *mut LeanObject,
    mut v_inst_7447_: *mut LeanObject,
    mut v_a_7448_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_producers_7449_: *mut LeanObject = core::ptr::null_mut();
    let mut v_consumers_7450_: *mut LeanObject = core::ptr::null_mut();
    let mut v_closed_7451_: u8 = 0;
    let mut v___x_7453_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_7454_: u8 = 0;
    let mut v___x_7455_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_7456_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_7457_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_7458_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_7459_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_7460_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_7461_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_7462_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7464_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7465_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7466_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7467_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7468_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toPure_7469_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7470_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7471_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7472_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_producers_7449_ = lean_ctor_get(v_a_7448_, 0);
                v_consumers_7450_ = lean_ctor_get(v_a_7448_, 1);
                v_closed_7451_ = lean_ctor_get_uint8(
                    v_a_7448_,
                    (core::mem::size_of::<*mut LeanObject>() * 2) as u32,
                );
                v_isSharedCheck_7472_ = (!lean_is_exclusive(v_a_7448_)) as u8;
                if v_isSharedCheck_7472_ == 0 {
                    v___x_7453_ = v_a_7448_;
                    v_isShared_7454_ = v_isSharedCheck_7472_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_consumers_7450_);
                    lean_inc(v_producers_7449_);
                    lean_dec(v_a_7448_);
                    v___x_7453_ = lean_box(0);
                    v_isShared_7454_ = v_isSharedCheck_7472_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_7455_ = l_Std_Queue_dequeue_x3f___redArg(v_producers_7449_);
                if lean_obj_tag(v___x_7455_) == 1 {
                    v_val_7456_ = lean_ctor_get(v___x_7455_, 0);
                    lean_inc(v_val_7456_);
                    lean_dec_ref_known(v___x_7455_, 1);
                    v_fst_7457_ = lean_ctor_get(v_val_7456_, 0);
                    lean_inc(v_fst_7457_);
                    v_snd_7458_ = lean_ctor_get(v_val_7456_, 1);
                    lean_inc(v_snd_7458_);
                    lean_dec(v_val_7456_);
                    v_fst_7459_ = lean_ctor_get(v_fst_7457_, 0);
                    lean_inc(v_fst_7459_);
                    v_snd_7460_ = lean_ctor_get(v_fst_7457_, 1);
                    lean_inc(v_snd_7460_);
                    lean_dec(v_fst_7457_);
                    v___f_7461_ = lean_alloc_closure(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_tryRecv_x27___redArg___lam__0 as *mut core::ffi::c_void, 3, 2);
                    lean_closure_set(v___f_7461_, 0, v_toApplicative_7443_);
                    lean_closure_set(v___f_7461_, 1, v_fst_7459_);
                    lean_inc(v_toBind_7445_);
                    v___f_7462_ = lean_alloc_closure(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_tryRecv_x27___redArg___lam__1 as *mut core::ffi::c_void, 5, 4);
                    lean_closure_set(v___f_7462_, 0, v_snd_7460_);
                    lean_closure_set(v___f_7462_, 1, v_inst_7444_);
                    lean_closure_set(v___f_7462_, 2, v_toBind_7445_);
                    lean_closure_set(v___f_7462_, 3, v___f_7461_);
                    if v_isShared_7454_ == 0 {
                        lean_ctor_set(v___x_7453_, 0, v_snd_7458_);
                        v___x_7464_ = v___x_7453_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_7468_ = lean_alloc_ctor(0, 2, (1) as u32);
                        lean_ctor_set(v_reuseFailAlloc_7468_, 0, v_snd_7458_);
                        lean_ctor_set(v_reuseFailAlloc_7468_, 1, v_consumers_7450_);
                        lean_ctor_set_uint8(
                            v_reuseFailAlloc_7468_,
                            (core::mem::size_of::<*mut LeanObject>() * 2) as u32,
                            v_closed_7451_,
                        );
                        v___x_7464_ = v_reuseFailAlloc_7468_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_dec(v___x_7455_);
                    lean_del_object(v___x_7453_);
                    lean_dec_ref(v_consumers_7450_);
                    lean_dec(v_inst_7447_);
                    lean_dec(v_toBind_7445_);
                    lean_dec(v_inst_7444_);
                    v_toPure_7469_ = lean_ctor_get(v_toApplicative_7443_, 1);
                    lean_inc(v_toPure_7469_);
                    lean_dec_ref(v_toApplicative_7443_);
                    v___x_7470_ = lean_box(0);
                    v___x_7471_ = lean_apply_2(v_toPure_7469_, lean_box(0), v___x_7470_);
                    return v___x_7471_;
                }
            }
            2 => {
                lean_inc(v_a_7446_);
                v___x_7465_ =
                    lean_alloc_closure(l_ST_Prim_Ref_set___boxed as *mut core::ffi::c_void, 5, 4);
                lean_closure_set(v___x_7465_, 0, lean_box(0));
                lean_closure_set(v___x_7465_, 1, lean_box(0));
                lean_closure_set(v___x_7465_, 2, v_a_7446_);
                lean_closure_set(v___x_7465_, 3, v___x_7464_);
                v___x_7466_ = lean_apply_2(v_inst_7447_, lean_box(0), v___x_7465_);
                v___x_7467_ = lean_apply_4(
                    v_toBind_7445_,
                    lean_box(0),
                    lean_box(0),
                    v___x_7466_,
                    v___f_7462_,
                );
                return v___x_7467_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_tryRecv_x27___redArg___lam__0___boxed(
    mut v_toApplicative_7473_: *mut LeanObject,
    mut v_inst_7474_: *mut LeanObject,
    mut v_toBind_7475_: *mut LeanObject,
    mut v_a_7476_: *mut LeanObject,
    mut v_inst_7477_: *mut LeanObject,
    mut v_a_7478_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_7479_: *mut LeanObject = core::ptr::null_mut();
    v_res_7479_ =
        l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_tryRecv_x27___redArg___lam__0(
            v_toApplicative_7473_,
            v_inst_7474_,
            v_toBind_7475_,
            v_a_7476_,
            v_inst_7477_,
            v_a_7478_,
        );
    lean_dec(v_a_7476_);
    return v_res_7479_;
}
pub unsafe fn l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_tryRecv_x27___redArg(
    mut v_inst_7480_: *mut LeanObject,
    mut v_inst_7481_: *mut LeanObject,
    mut v_inst_7482_: *mut LeanObject,
    mut v_a_7483_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toApplicative_7484_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toBind_7485_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_7486_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7487_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7488_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7489_: *mut LeanObject = core::ptr::null_mut();
    v_toApplicative_7484_ = lean_ctor_get(v_inst_7480_, 0);
    lean_inc_ref(v_toApplicative_7484_);
    v_toBind_7485_ = lean_ctor_get(v_inst_7480_, 1);
    lean_inc_n(v_toBind_7485_, 2);
    lean_dec_ref(v_inst_7480_);
    lean_inc(v_inst_7481_);
    lean_inc_n(v_a_7483_, 2);
    v___f_7486_ = lean_alloc_closure(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_tryRecv_x27___redArg___lam__0___boxed as *mut core::ffi::c_void, 6, 5);
    lean_closure_set(v___f_7486_, 0, v_toApplicative_7484_);
    lean_closure_set(v___f_7486_, 1, v_inst_7482_);
    lean_closure_set(v___f_7486_, 2, v_toBind_7485_);
    lean_closure_set(v___f_7486_, 3, v_a_7483_);
    lean_closure_set(v___f_7486_, 4, v_inst_7481_);
    v___x_7487_ = lean_alloc_closure(l_ST_Prim_Ref_get___boxed as *mut core::ffi::c_void, 4, 3);
    lean_closure_set(v___x_7487_, 0, lean_box(0));
    lean_closure_set(v___x_7487_, 1, lean_box(0));
    lean_closure_set(v___x_7487_, 2, v_a_7483_);
    v___x_7488_ = lean_apply_2(v_inst_7481_, lean_box(0), v___x_7487_);
    v___x_7489_ = lean_apply_4(
        v_toBind_7485_,
        lean_box(0),
        lean_box(0),
        v___x_7488_,
        v___f_7486_,
    );
    return v___x_7489_;
}
pub unsafe fn l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_tryRecv_x27___redArg___boxed(
    mut v_inst_7490_: *mut LeanObject,
    mut v_inst_7491_: *mut LeanObject,
    mut v_inst_7492_: *mut LeanObject,
    mut v_a_7493_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_7494_: *mut LeanObject = core::ptr::null_mut();
    v_res_7494_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_tryRecv_x27___redArg(
        v_inst_7490_,
        v_inst_7491_,
        v_inst_7492_,
        v_a_7493_,
    );
    lean_dec(v_a_7493_);
    return v_res_7494_;
}
pub unsafe fn l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_tryRecv_x27(
    mut v_m_7495_: *mut LeanObject,
    mut v_00_u03b1_7496_: *mut LeanObject,
    mut v_inst_7497_: *mut LeanObject,
    mut v_inst_7498_: *mut LeanObject,
    mut v_inst_7499_: *mut LeanObject,
    mut v_a_7500_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_7501_: *mut LeanObject = core::ptr::null_mut();
    v___x_7501_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_tryRecv_x27___redArg(
        v_inst_7497_,
        v_inst_7498_,
        v_inst_7499_,
        v_a_7500_,
    );
    return v___x_7501_;
}
pub unsafe fn l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_tryRecv_x27___boxed(
    mut v_m_7502_: *mut LeanObject,
    mut v_00_u03b1_7503_: *mut LeanObject,
    mut v_inst_7504_: *mut LeanObject,
    mut v_inst_7505_: *mut LeanObject,
    mut v_inst_7506_: *mut LeanObject,
    mut v_a_7507_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_7508_: *mut LeanObject = core::ptr::null_mut();
    v_res_7508_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_tryRecv_x27(
        v_m_7502_,
        v_00_u03b1_7503_,
        v_inst_7504_,
        v_inst_7505_,
        v_inst_7506_,
        v_a_7507_,
    );
    lean_dec(v_a_7507_);
    return v_res_7508_;
}
pub unsafe fn l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_tryRecv_spec__0___redArg(
    mut v_a_7509_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_7511_: *mut LeanObject = core::ptr::null_mut();
    let mut v_producers_7512_: *mut LeanObject = core::ptr::null_mut();
    let mut v_consumers_7513_: *mut LeanObject = core::ptr::null_mut();
    let mut v_closed_7514_: u8 = 0;
    let mut v___x_7516_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_7517_: u8 = 0;
    let mut v___x_7518_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_7519_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7521_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_7522_: u8 = 0;
    let mut v_fst_7523_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_7524_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_7525_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_7526_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7528_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7529_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7530_: u8 = 0;
    let mut v___x_7531_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7532_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7534_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7535_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7536_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7537_: u8 = 0;
    let mut v___x_7538_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7539_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_7511_ = lean_st_ref_get(v_a_7509_);
                v_producers_7512_ = lean_ctor_get(v___x_7511_, 0);
                v_consumers_7513_ = lean_ctor_get(v___x_7511_, 1);
                v_closed_7514_ = lean_ctor_get_uint8(
                    v___x_7511_,
                    (core::mem::size_of::<*mut LeanObject>() * 2) as u32,
                );
                v_isSharedCheck_7539_ = (!lean_is_exclusive(v___x_7511_)) as u8;
                if v_isSharedCheck_7539_ == 0 {
                    v___x_7516_ = v___x_7511_;
                    v_isShared_7517_ = v_isSharedCheck_7539_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_consumers_7513_);
                    lean_inc(v_producers_7512_);
                    lean_dec(v___x_7511_);
                    v___x_7516_ = lean_box(0);
                    v_isShared_7517_ = v_isSharedCheck_7539_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_7518_ = l_Std_Queue_dequeue_x3f___redArg(v_producers_7512_);
                if lean_obj_tag(v___x_7518_) == 1 {
                    v_val_7519_ = lean_ctor_get(v___x_7518_, 0);
                    v_isSharedCheck_7537_ = (!lean_is_exclusive(v___x_7518_)) as u8;
                    if v_isSharedCheck_7537_ == 0 {
                        v___x_7521_ = v___x_7518_;
                        v_isShared_7522_ = v_isSharedCheck_7537_;
                        state = 2;
                        continue;
                    } else {
                        lean_inc(v_val_7519_);
                        lean_dec(v___x_7518_);
                        v___x_7521_ = lean_box(0);
                        v_isShared_7522_ = v_isSharedCheck_7537_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_dec(v___x_7518_);
                    lean_del_object(v___x_7516_);
                    lean_dec_ref(v_consumers_7513_);
                    v___x_7538_ = lean_box(0);
                    return v___x_7538_;
                }
            }
            2 => {
                v_fst_7523_ = lean_ctor_get(v_val_7519_, 0);
                lean_inc(v_fst_7523_);
                v_snd_7524_ = lean_ctor_get(v_val_7519_, 1);
                lean_inc(v_snd_7524_);
                lean_dec(v_val_7519_);
                v_fst_7525_ = lean_ctor_get(v_fst_7523_, 0);
                lean_inc(v_fst_7525_);
                v_snd_7526_ = lean_ctor_get(v_fst_7523_, 1);
                lean_inc(v_snd_7526_);
                lean_dec(v_fst_7523_);
                if v_isShared_7517_ == 0 {
                    lean_ctor_set(v___x_7516_, 0, v_snd_7524_);
                    v___x_7528_ = v___x_7516_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_7536_ = lean_alloc_ctor(0, 2, (1) as u32);
                    lean_ctor_set(v_reuseFailAlloc_7536_, 0, v_snd_7524_);
                    lean_ctor_set(v_reuseFailAlloc_7536_, 1, v_consumers_7513_);
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_7536_,
                        (core::mem::size_of::<*mut LeanObject>() * 2) as u32,
                        v_closed_7514_,
                    );
                    v___x_7528_ = v_reuseFailAlloc_7536_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_7529_ = lean_st_ref_set(v_a_7509_, v___x_7528_);
                v___x_7530_ = 1;
                v___x_7531_ = lean_box((v___x_7530_) as usize);
                v___x_7532_ = lean_io_promise_resolve(v___x_7531_, v_snd_7526_);
                lean_dec(v_snd_7526_);
                if v_isShared_7522_ == 0 {
                    lean_ctor_set(v___x_7521_, 0, v_fst_7525_);
                    v___x_7534_ = v___x_7521_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_7535_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_7535_, 0, v_fst_7525_);
                    v___x_7534_ = v_reuseFailAlloc_7535_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_7534_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_tryRecv_spec__0___redArg___boxed(
    mut v_a_7540_: *mut LeanObject,
    mut v___y_7541_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_7542_: *mut LeanObject = core::ptr::null_mut();
    v_res_7542_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_tryRecv_spec__0___redArg(v_a_7540_);
    lean_dec(v_a_7540_);
    return v_res_7542_;
}
pub unsafe fn l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_tryRecv_spec__0(
    mut v_00_u03b1_7543_: *mut LeanObject,
    mut v_a_7544_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_7546_: *mut LeanObject = core::ptr::null_mut();
    v___x_7546_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_tryRecv_spec__0___redArg(v_a_7544_);
    return v___x_7546_;
}
pub unsafe fn l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_tryRecv_spec__0___boxed(
    mut v_00_u03b1_7547_: *mut LeanObject,
    mut v_a_7548_: *mut LeanObject,
    mut v___y_7549_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_7550_: *mut LeanObject = core::ptr::null_mut();
    v_res_7550_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_tryRecv_spec__0(v_00_u03b1_7547_, v_a_7548_);
    lean_dec(v_a_7548_);
    return v_res_7550_;
}
pub unsafe fn l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_tryRecv___redArg(
    mut v_ch_7552_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_7554_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7555_: *mut LeanObject = core::ptr::null_mut();
    v___f_7554_ =
        l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_tryRecv___redArg___closed__0;
    v___x_7555_ = l_Std_Mutex_atomically___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_trySend_spec__1___redArg(v_ch_7552_, v___f_7554_);
    return v___x_7555_;
}
pub unsafe fn l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_tryRecv___redArg___boxed(
    mut v_ch_7556_: *mut LeanObject,
    mut v_a_7557_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_7558_: *mut LeanObject = core::ptr::null_mut();
    v_res_7558_ =
        l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_tryRecv___redArg(v_ch_7556_);
    return v_res_7558_;
}
pub unsafe fn l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_tryRecv(
    mut v_00_u03b1_7559_: *mut LeanObject,
    mut v_ch_7560_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_7562_: *mut LeanObject = core::ptr::null_mut();
    v___x_7562_ =
        l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_tryRecv___redArg(v_ch_7560_);
    return v___x_7562_;
}
pub unsafe fn l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_tryRecv___boxed(
    mut v_00_u03b1_7563_: *mut LeanObject,
    mut v_ch_7564_: *mut LeanObject,
    mut v_a_7565_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_7566_: *mut LeanObject = core::ptr::null_mut();
    v_res_7566_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_tryRecv(
        v_00_u03b1_7563_,
        v_ch_7564_,
    );
    return v_res_7566_;
}
pub unsafe fn l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recv___redArg___lam__1(
    mut v___f_7567_: *mut LeanObject,
    mut v___y_7568_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_7570_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7571_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7572_: *mut LeanObject = core::ptr::null_mut();
    let mut v_closed_7573_: u8 = 0;
    let mut v_producers_7574_: *mut LeanObject = core::ptr::null_mut();
    let mut v_consumers_7575_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7577_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_7578_: u8 = 0;
    let mut v___x_7579_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7580_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7581_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7583_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7584_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7585_: u8 = 0;
    let mut v___x_7586_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7587_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7588_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7589_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7590_: u8 = 0;
    let mut v___x_7591_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_7570_ = lean_st_ref_get(v___y_7568_);
                v___x_7571_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_tryRecv_spec__0___redArg(v___y_7568_);
                if lean_obj_tag(v___x_7571_) == 1 {
                    lean_dec(v___x_7570_);
                    lean_dec_ref(v___f_7567_);
                    v___x_7572_ = lean_task_pure(v___x_7571_);
                    return v___x_7572_;
                } else {
                    lean_dec(v___x_7571_);
                    v_closed_7573_ = lean_ctor_get_uint8(
                        v___x_7570_,
                        (core::mem::size_of::<*mut LeanObject>() * 2) as u32,
                    );
                    if v_closed_7573_ == 0 {
                        v_producers_7574_ = lean_ctor_get(v___x_7570_, 0);
                        v_consumers_7575_ = lean_ctor_get(v___x_7570_, 1);
                        v_isSharedCheck_7590_ = (!lean_is_exclusive(v___x_7570_)) as u8;
                        if v_isSharedCheck_7590_ == 0 {
                            v___x_7577_ = v___x_7570_;
                            v_isShared_7578_ = v_isSharedCheck_7590_;
                            state = 1;
                            continue;
                        } else {
                            lean_inc(v_consumers_7575_);
                            lean_inc(v_producers_7574_);
                            lean_dec(v___x_7570_);
                            v___x_7577_ = lean_box(0);
                            v_isShared_7578_ = v_isSharedCheck_7590_;
                            state = 1;
                            continue;
                        }
                    } else {
                        lean_dec(v___x_7570_);
                        lean_dec_ref(v___f_7567_);
                        v___x_7591_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recv___redArg___lam__1___closed__0), core::ptr::addr_of_mut!(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recv___redArg___lam__1___closed__0_once), _init_l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recv___redArg___lam__1___closed__0);
                        return v___x_7591_;
                    }
                }
            }
            1 => {
                v___x_7579_ = lean_io_promise_new();
                lean_inc(v___x_7579_);
                v___x_7580_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_7580_, 0, v___x_7579_);
                v___x_7581_ = l_Std_Queue_enqueue___redArg(v___x_7580_, v_consumers_7575_);
                if v_isShared_7578_ == 0 {
                    lean_ctor_set(v___x_7577_, 1, v___x_7581_);
                    v___x_7583_ = v___x_7577_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_7589_ = lean_alloc_ctor(0, 2, (1) as u32);
                    lean_ctor_set(v_reuseFailAlloc_7589_, 0, v_producers_7574_);
                    lean_ctor_set(v_reuseFailAlloc_7589_, 1, v___x_7581_);
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_7589_,
                        (core::mem::size_of::<*mut LeanObject>() * 2) as u32,
                        v_closed_7573_,
                    );
                    v___x_7583_ = v_reuseFailAlloc_7589_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_7584_ = lean_st_ref_set(v___y_7568_, v___x_7583_);
                v___x_7585_ = 1;
                v___x_7586_ = lean_io_promise_result_opt(v___x_7579_);
                lean_dec(v___x_7579_);
                v___x_7587_ = lean_unsigned_to_nat(0);
                v___x_7588_ = lean_task_map(v___f_7567_, v___x_7586_, v___x_7587_, v___x_7585_);
                return v___x_7588_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recv___redArg___lam__1___boxed(
    mut v___f_7592_: *mut LeanObject,
    mut v___y_7593_: *mut LeanObject,
    mut v___y_7594_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_7595_: *mut LeanObject = core::ptr::null_mut();
    v_res_7595_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recv___redArg___lam__1(
        v___f_7592_,
        v___y_7593_,
    );
    lean_dec(v___y_7593_);
    return v_res_7595_;
}
pub unsafe fn l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recv___redArg(
    mut v_ch_7598_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_7600_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7601_: *mut LeanObject = core::ptr::null_mut();
    v___f_7600_ =
        l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recv___redArg___closed__0;
    v___x_7601_ = l_Std_Mutex_atomically___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_trySend_spec__1___redArg(v_ch_7598_, v___f_7600_);
    return v___x_7601_;
}
pub unsafe fn l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recv___redArg___boxed(
    mut v_ch_7602_: *mut LeanObject,
    mut v_a_7603_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_7604_: *mut LeanObject = core::ptr::null_mut();
    v_res_7604_ =
        l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recv___redArg(v_ch_7602_);
    return v_res_7604_;
}
pub unsafe fn l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recv(
    mut v_00_u03b1_7605_: *mut LeanObject,
    mut v_ch_7606_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_7608_: *mut LeanObject = core::ptr::null_mut();
    v___x_7608_ =
        l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recv___redArg(v_ch_7606_);
    return v___x_7608_;
}
pub unsafe fn l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recv___boxed(
    mut v_00_u03b1_7609_: *mut LeanObject,
    mut v_ch_7610_: *mut LeanObject,
    mut v_a_7611_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_7612_: *mut LeanObject = core::ptr::null_mut();
    v_res_7612_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recv(
        v_00_u03b1_7609_,
        v_ch_7610_,
    );
    return v_res_7612_;
}
pub unsafe fn l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvReady_x27___redArg___lam__0(
    mut v_toApplicative_7613_: *mut LeanObject,
    mut v_a_7614_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___y_7616_: u8 = 0;
    let mut v_toPure_7617_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7618_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7619_: *mut LeanObject = core::ptr::null_mut();
    let mut v_producers_7620_: *mut LeanObject = core::ptr::null_mut();
    let mut v_closed_7621_: u8 = 0;
    let mut v___x_7622_: u8 = 0;
    let mut v___x_7623_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_producers_7620_ = lean_ctor_get(v_a_7614_, 0);
                v_closed_7621_ = lean_ctor_get_uint8(
                    v_a_7614_,
                    (core::mem::size_of::<*mut LeanObject>() * 2) as u32,
                );
                v___x_7622_ = l_Std_Queue_isEmpty___redArg(v_producers_7620_);
                if v___x_7622_ == 0 {
                    v___x_7623_ = 1;
                    v___y_7616_ = v___x_7623_;
                    state = 1;
                    continue;
                } else {
                    v___y_7616_ = v_closed_7621_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_toPure_7617_ = lean_ctor_get(v_toApplicative_7613_, 1);
                lean_inc(v_toPure_7617_);
                lean_dec_ref(v_toApplicative_7613_);
                v___x_7618_ = lean_box((v___y_7616_) as usize);
                v___x_7619_ = lean_apply_2(v_toPure_7617_, lean_box(0), v___x_7618_);
                return v___x_7619_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvReady_x27___redArg___lam__0___boxed(
    mut v_toApplicative_7624_: *mut LeanObject,
    mut v_a_7625_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_7626_: *mut LeanObject = core::ptr::null_mut();
    v_res_7626_ =
        l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvReady_x27___redArg___lam__0(
            v_toApplicative_7624_,
            v_a_7625_,
        );
    lean_dec_ref(v_a_7625_);
    return v_res_7626_;
}
pub unsafe fn l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvReady_x27___redArg(
    mut v_inst_7627_: *mut LeanObject,
    mut v_inst_7628_: *mut LeanObject,
    mut v_a_7629_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toApplicative_7630_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toBind_7631_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_7632_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7633_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7634_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7635_: *mut LeanObject = core::ptr::null_mut();
    v_toApplicative_7630_ = lean_ctor_get(v_inst_7627_, 0);
    lean_inc_ref(v_toApplicative_7630_);
    v_toBind_7631_ = lean_ctor_get(v_inst_7627_, 1);
    lean_inc(v_toBind_7631_);
    lean_dec_ref(v_inst_7627_);
    v___f_7632_ = lean_alloc_closure(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvReady_x27___redArg___lam__0___boxed as *mut core::ffi::c_void, 2, 1);
    lean_closure_set(v___f_7632_, 0, v_toApplicative_7630_);
    lean_inc(v_a_7629_);
    v___x_7633_ = lean_alloc_closure(l_ST_Prim_Ref_get___boxed as *mut core::ffi::c_void, 4, 3);
    lean_closure_set(v___x_7633_, 0, lean_box(0));
    lean_closure_set(v___x_7633_, 1, lean_box(0));
    lean_closure_set(v___x_7633_, 2, v_a_7629_);
    v___x_7634_ = lean_apply_2(v_inst_7628_, lean_box(0), v___x_7633_);
    v___x_7635_ = lean_apply_4(
        v_toBind_7631_,
        lean_box(0),
        lean_box(0),
        v___x_7634_,
        v___f_7632_,
    );
    return v___x_7635_;
}
pub unsafe fn l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvReady_x27___redArg___boxed(
    mut v_inst_7636_: *mut LeanObject,
    mut v_inst_7637_: *mut LeanObject,
    mut v_a_7638_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_7639_: *mut LeanObject = core::ptr::null_mut();
    v_res_7639_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvReady_x27___redArg(
        v_inst_7636_,
        v_inst_7637_,
        v_a_7638_,
    );
    lean_dec(v_a_7638_);
    return v_res_7639_;
}
pub unsafe fn l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvReady_x27(
    mut v_m_7640_: *mut LeanObject,
    mut v_00_u03b1_7641_: *mut LeanObject,
    mut v_inst_7642_: *mut LeanObject,
    mut v_inst_7643_: *mut LeanObject,
    mut v_a_7644_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toApplicative_7645_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toBind_7646_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_7647_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7648_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7649_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7650_: *mut LeanObject = core::ptr::null_mut();
    v_toApplicative_7645_ = lean_ctor_get(v_inst_7642_, 0);
    lean_inc_ref(v_toApplicative_7645_);
    v_toBind_7646_ = lean_ctor_get(v_inst_7642_, 1);
    lean_inc(v_toBind_7646_);
    lean_dec_ref(v_inst_7642_);
    v___f_7647_ = lean_alloc_closure(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvReady_x27___redArg___lam__0___boxed as *mut core::ffi::c_void, 2, 1);
    lean_closure_set(v___f_7647_, 0, v_toApplicative_7645_);
    lean_inc(v_a_7644_);
    v___x_7648_ = lean_alloc_closure(l_ST_Prim_Ref_get___boxed as *mut core::ffi::c_void, 4, 3);
    lean_closure_set(v___x_7648_, 0, lean_box(0));
    lean_closure_set(v___x_7648_, 1, lean_box(0));
    lean_closure_set(v___x_7648_, 2, v_a_7644_);
    v___x_7649_ = lean_apply_2(v_inst_7643_, lean_box(0), v___x_7648_);
    v___x_7650_ = lean_apply_4(
        v_toBind_7646_,
        lean_box(0),
        lean_box(0),
        v___x_7649_,
        v___f_7647_,
    );
    return v___x_7650_;
}
pub unsafe fn l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvReady_x27___boxed(
    mut v_m_7651_: *mut LeanObject,
    mut v_00_u03b1_7652_: *mut LeanObject,
    mut v_inst_7653_: *mut LeanObject,
    mut v_inst_7654_: *mut LeanObject,
    mut v_a_7655_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_7656_: *mut LeanObject = core::ptr::null_mut();
    v_res_7656_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvReady_x27(
        v_m_7651_,
        v_00_u03b1_7652_,
        v_inst_7653_,
        v_inst_7654_,
        v_a_7655_,
    );
    lean_dec(v_a_7655_);
    return v_res_7656_;
}
pub unsafe fn l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector_spec__0___redArg___lam__1(
    mut v_snd_7657_: *mut LeanObject,
    mut v___f_7658_: *mut LeanObject,
    mut v_x_7659_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_7661_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7663_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_7664_: u8 = 0;
    let mut v___x_7666_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7667_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7668_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7669_: u8 = 0;
    let mut v___x_7671_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_7672_: u8 = 0;
    let mut v___x_7673_: u8 = 0;
    let mut v___x_7674_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7675_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7677_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7678_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7679_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7680_: u8 = 0;
    let mut v___x_7681_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7682_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7683_: u8 = 0;
    let mut v_unused_7684_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_7659_) == 0 {
                    lean_dec_ref(v___f_7658_);
                    v_a_7661_ = lean_ctor_get(v_x_7659_, 0);
                    v_isSharedCheck_7669_ = (!lean_is_exclusive(v_x_7659_)) as u8;
                    if v_isSharedCheck_7669_ == 0 {
                        v___x_7663_ = v_x_7659_;
                        v_isShared_7664_ = v_isSharedCheck_7669_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_7661_);
                        lean_dec(v_x_7659_);
                        v___x_7663_ = lean_box(0);
                        v_isShared_7664_ = v_isSharedCheck_7669_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_isSharedCheck_7683_ = (!lean_is_exclusive(v_x_7659_)) as u8;
                    if v_isSharedCheck_7683_ == 0 {
                        v_unused_7684_ = lean_ctor_get(v_x_7659_, 0);
                        lean_dec(v_unused_7684_);
                        v___x_7671_ = v_x_7659_;
                        v_isShared_7672_ = v_isSharedCheck_7683_;
                        state = 3;
                        continue;
                    } else {
                        lean_dec(v_x_7659_);
                        v___x_7671_ = lean_box(0);
                        v_isShared_7672_ = v_isSharedCheck_7683_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_7664_ == 0 {
                    v___x_7666_ = v___x_7663_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_7668_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_7668_, 0, v_a_7661_);
                    v___x_7666_ = v_reuseFailAlloc_7668_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_7667_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_7667_, 0, v___x_7666_);
                return v___x_7667_;
            }
            3 => {
                v___x_7673_ = 1;
                v___x_7674_ = lean_box((v___x_7673_) as usize);
                v___x_7675_ = lean_io_promise_resolve(v___x_7674_, v_snd_7657_);
                if v_isShared_7672_ == 0 {
                    lean_ctor_set(v___x_7671_, 0, v___x_7675_);
                    v___x_7677_ = v___x_7671_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_7682_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_7682_, 0, v___x_7675_);
                    v___x_7677_ = v_reuseFailAlloc_7682_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_7678_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_7678_, 0, v___x_7677_);
                v___x_7679_ = lean_unsigned_to_nat(0);
                v___x_7680_ = 0;
                v___x_7681_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(
                    lean_box(0),
                    lean_box(0),
                    v___x_7679_,
                    v___x_7680_,
                    v___x_7678_,
                    v___f_7658_,
                );
                return v___x_7681_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector_spec__0___redArg___lam__1___boxed(
    mut v_snd_7685_: *mut LeanObject,
    mut v___f_7686_: *mut LeanObject,
    mut v_x_7687_: *mut LeanObject,
    mut v___y_7688_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_7689_: *mut LeanObject = core::ptr::null_mut();
    v_res_7689_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector_spec__0___redArg___lam__1(v_snd_7685_, v___f_7686_, v_x_7687_);
    lean_dec(v_snd_7685_);
    return v_res_7689_;
}
pub unsafe fn l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector_spec__0___redArg___lam__0(
    mut v_a_7690_: *mut LeanObject,
    mut v_x_7691_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_7693_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7695_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_7696_: u8 = 0;
    let mut v___x_7698_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7699_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7700_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7701_: u8 = 0;
    let mut v_a_7702_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7704_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_7705_: u8 = 0;
    let mut v_producers_7706_: *mut LeanObject = core::ptr::null_mut();
    let mut v_consumers_7707_: *mut LeanObject = core::ptr::null_mut();
    let mut v_closed_7708_: u8 = 0;
    let mut v___x_7710_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_7711_: u8 = 0;
    let mut v___x_7712_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_7713_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7715_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_7716_: u8 = 0;
    let mut v_fst_7717_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_7718_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_7719_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_7720_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7722_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7723_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_7724_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_7725_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7727_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7729_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7730_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7731_: u8 = 0;
    let mut v___x_7732_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7733_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7734_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7735_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7736_: u8 = 0;
    let mut v___x_7737_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7738_: u8 = 0;
    let mut v_isSharedCheck_7739_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_7691_) == 0 {
                    v_a_7693_ = lean_ctor_get(v_x_7691_, 0);
                    v_isSharedCheck_7701_ = (!lean_is_exclusive(v_x_7691_)) as u8;
                    if v_isSharedCheck_7701_ == 0 {
                        v___x_7695_ = v_x_7691_;
                        v_isShared_7696_ = v_isSharedCheck_7701_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_7693_);
                        lean_dec(v_x_7691_);
                        v___x_7695_ = lean_box(0);
                        v_isShared_7696_ = v_isSharedCheck_7701_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_7702_ = lean_ctor_get(v_x_7691_, 0);
                    v_isSharedCheck_7739_ = (!lean_is_exclusive(v_x_7691_)) as u8;
                    if v_isSharedCheck_7739_ == 0 {
                        v___x_7704_ = v_x_7691_;
                        v_isShared_7705_ = v_isSharedCheck_7739_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_7702_);
                        lean_dec(v_x_7691_);
                        v___x_7704_ = lean_box(0);
                        v_isShared_7705_ = v_isSharedCheck_7739_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_7696_ == 0 {
                    v___x_7698_ = v___x_7695_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_7700_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_7700_, 0, v_a_7693_);
                    v___x_7698_ = v_reuseFailAlloc_7700_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_7699_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_7699_, 0, v___x_7698_);
                return v___x_7699_;
            }
            3 => {
                v_producers_7706_ = lean_ctor_get(v_a_7702_, 0);
                v_consumers_7707_ = lean_ctor_get(v_a_7702_, 1);
                v_closed_7708_ = lean_ctor_get_uint8(
                    v_a_7702_,
                    (core::mem::size_of::<*mut LeanObject>() * 2) as u32,
                );
                v_isSharedCheck_7738_ = (!lean_is_exclusive(v_a_7702_)) as u8;
                if v_isSharedCheck_7738_ == 0 {
                    v___x_7710_ = v_a_7702_;
                    v_isShared_7711_ = v_isSharedCheck_7738_;
                    state = 4;
                    continue;
                } else {
                    lean_inc(v_consumers_7707_);
                    lean_inc(v_producers_7706_);
                    lean_dec(v_a_7702_);
                    v___x_7710_ = lean_box(0);
                    v_isShared_7711_ = v_isSharedCheck_7738_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_7712_ = l_Std_Queue_dequeue_x3f___redArg(v_producers_7706_);
                if lean_obj_tag(v___x_7712_) == 1 {
                    v_val_7713_ = lean_ctor_get(v___x_7712_, 0);
                    v_isSharedCheck_7736_ = (!lean_is_exclusive(v___x_7712_)) as u8;
                    if v_isSharedCheck_7736_ == 0 {
                        v___x_7715_ = v___x_7712_;
                        v_isShared_7716_ = v_isSharedCheck_7736_;
                        state = 5;
                        continue;
                    } else {
                        lean_inc(v_val_7713_);
                        lean_dec(v___x_7712_);
                        v___x_7715_ = lean_box(0);
                        v_isShared_7716_ = v_isSharedCheck_7736_;
                        state = 5;
                        continue;
                    }
                } else {
                    lean_dec(v___x_7712_);
                    lean_del_object(v___x_7710_);
                    lean_dec_ref(v_consumers_7707_);
                    lean_del_object(v___x_7704_);
                    v___x_7737_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__0___redArg___lam__1___closed__1;
                    return v___x_7737_;
                }
            }
            5 => {
                v_fst_7717_ = lean_ctor_get(v_val_7713_, 0);
                lean_inc(v_fst_7717_);
                v_snd_7718_ = lean_ctor_get(v_val_7713_, 1);
                lean_inc(v_snd_7718_);
                lean_dec(v_val_7713_);
                v_fst_7719_ = lean_ctor_get(v_fst_7717_, 0);
                lean_inc(v_fst_7719_);
                v_snd_7720_ = lean_ctor_get(v_fst_7717_, 1);
                lean_inc(v_snd_7720_);
                lean_dec(v_fst_7717_);
                if v_isShared_7711_ == 0 {
                    lean_ctor_set(v___x_7710_, 0, v_snd_7718_);
                    v___x_7722_ = v___x_7710_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_7735_ = lean_alloc_ctor(0, 2, (1) as u32);
                    lean_ctor_set(v_reuseFailAlloc_7735_, 0, v_snd_7718_);
                    lean_ctor_set(v_reuseFailAlloc_7735_, 1, v_consumers_7707_);
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_7735_,
                        (core::mem::size_of::<*mut LeanObject>() * 2) as u32,
                        v_closed_7708_,
                    );
                    v___x_7722_ = v_reuseFailAlloc_7735_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                v___x_7723_ = lean_st_ref_set(v_a_7690_, v___x_7722_);
                v___f_7724_ = lean_alloc_closure(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__0___redArg___lam__0___boxed as *mut core::ffi::c_void, 3, 1);
                lean_closure_set(v___f_7724_, 0, v_fst_7719_);
                v___f_7725_ = lean_alloc_closure(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector_spec__0___redArg___lam__1___boxed as *mut core::ffi::c_void, 4, 2);
                lean_closure_set(v___f_7725_, 0, v_snd_7720_);
                lean_closure_set(v___f_7725_, 1, v___f_7724_);
                if v_isShared_7705_ == 0 {
                    lean_ctor_set(v___x_7704_, 0, v___x_7723_);
                    v___x_7727_ = v___x_7704_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_7734_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_7734_, 0, v___x_7723_);
                    v___x_7727_ = v_reuseFailAlloc_7734_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                if v_isShared_7716_ == 0 {
                    lean_ctor_set_tag(v___x_7715_, 0);
                    lean_ctor_set(v___x_7715_, 0, v___x_7727_);
                    v___x_7729_ = v___x_7715_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_7733_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_7733_, 0, v___x_7727_);
                    v___x_7729_ = v_reuseFailAlloc_7733_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                v___x_7730_ = lean_unsigned_to_nat(0);
                v___x_7731_ = 0;
                v___x_7732_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(
                    lean_box(0),
                    lean_box(0),
                    v___x_7730_,
                    v___x_7731_,
                    v___x_7729_,
                    v___f_7725_,
                );
                return v___x_7732_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector_spec__0___redArg___lam__0___boxed(
    mut v_a_7740_: *mut LeanObject,
    mut v_x_7741_: *mut LeanObject,
    mut v___y_7742_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_7743_: *mut LeanObject = core::ptr::null_mut();
    v_res_7743_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector_spec__0___redArg___lam__0(v_a_7740_, v_x_7741_);
    lean_dec(v_a_7740_);
    return v_res_7743_;
}
pub unsafe fn l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector_spec__0___redArg(
    mut v_a_7744_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_7746_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_7747_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7748_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7749_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7750_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7751_: u8 = 0;
    let mut v___x_7752_: *mut LeanObject = core::ptr::null_mut();
    v___x_7746_ = lean_st_ref_get(v_a_7744_);
    lean_inc(v_a_7744_);
    v___f_7747_ = lean_alloc_closure(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector_spec__0___redArg___lam__0___boxed as *mut core::ffi::c_void, 3, 1);
    lean_closure_set(v___f_7747_, 0, v_a_7744_);
    v___x_7748_ = lean_alloc_ctor(1, 1, (0) as u32);
    lean_ctor_set(v___x_7748_, 0, v___x_7746_);
    v___x_7749_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_7749_, 0, v___x_7748_);
    v___x_7750_ = lean_unsigned_to_nat(0);
    v___x_7751_ = 0;
    v___x_7752_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(
        lean_box(0),
        lean_box(0),
        v___x_7750_,
        v___x_7751_,
        v___x_7749_,
        v___f_7747_,
    );
    return v___x_7752_;
}
pub unsafe fn l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector_spec__0___redArg___boxed(
    mut v_a_7753_: *mut LeanObject,
    mut v___y_7754_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_7755_: *mut LeanObject = core::ptr::null_mut();
    v_res_7755_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector_spec__0___redArg(v_a_7753_);
    lean_dec(v_a_7753_);
    return v_res_7755_;
}
pub unsafe fn l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector_spec__0(
    mut v_00_u03b1_7756_: *mut LeanObject,
    mut v_a_7757_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_7759_: *mut LeanObject = core::ptr::null_mut();
    v___x_7759_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector_spec__0___redArg(v_a_7757_);
    return v___x_7759_;
}
pub unsafe fn l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector_spec__0___boxed(
    mut v_00_u03b1_7760_: *mut LeanObject,
    mut v_a_7761_: *mut LeanObject,
    mut v___y_7762_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_7763_: *mut LeanObject = core::ptr::null_mut();
    v_res_7763_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector_spec__0(v_00_u03b1_7760_, v_a_7761_);
    lean_dec(v_a_7761_);
    return v_res_7763_;
}
pub unsafe fn l_Std_Async_Waiter_race___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector_spec__1___redArg___lam__1(
    mut v_lose_7764_: *mut LeanObject,
    mut v___y_7765_: *mut LeanObject,
    mut v___f_7766_: *mut LeanObject,
    mut v_x_7767_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_7769_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7771_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_7772_: u8 = 0;
    let mut v___x_7774_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7775_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7776_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7777_: u8 = 0;
    let mut v_a_7778_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7779_: u8 = 0;
    let mut v___x_7780_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7781_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7782_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7783_: u8 = 0;
    let mut v___x_7784_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_7767_) == 0 {
                    lean_dec_ref(v___f_7766_);
                    lean_dec_ref(v_lose_7764_);
                    v_a_7769_ = lean_ctor_get(v_x_7767_, 0);
                    v_isSharedCheck_7777_ = (!lean_is_exclusive(v_x_7767_)) as u8;
                    if v_isSharedCheck_7777_ == 0 {
                        v___x_7771_ = v_x_7767_;
                        v_isShared_7772_ = v_isSharedCheck_7777_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_7769_);
                        lean_dec(v_x_7767_);
                        v___x_7771_ = lean_box(0);
                        v_isShared_7772_ = v_isSharedCheck_7777_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_7778_ = lean_ctor_get(v_x_7767_, 0);
                    lean_inc(v_a_7778_);
                    lean_dec_ref_known(v_x_7767_, 1);
                    v___x_7779_ = (lean_unbox(v_a_7778_) as u8);
                    lean_dec(v_a_7778_);
                    if v___x_7779_ == 0 {
                        lean_dec_ref(v___f_7766_);
                        lean_inc(v___y_7765_);
                        v___x_7780_ = lean_apply_2(v_lose_7764_, v___y_7765_, lean_box(0));
                        return v___x_7780_;
                    } else {
                        lean_dec_ref(v_lose_7764_);
                        v___x_7781_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector_spec__0___redArg(v___y_7765_);
                        v___x_7782_ = lean_unsigned_to_nat(0);
                        v___x_7783_ = 0;
                        v___x_7784_ =
                            l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(
                                lean_box(0),
                                lean_box(0),
                                v___x_7782_,
                                v___x_7783_,
                                v___x_7781_,
                                v___f_7766_,
                            );
                        return v___x_7784_;
                    }
                }
            }
            1 => {
                if v_isShared_7772_ == 0 {
                    v___x_7774_ = v___x_7771_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_7776_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_7776_, 0, v_a_7769_);
                    v___x_7774_ = v_reuseFailAlloc_7776_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_7775_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_7775_, 0, v___x_7774_);
                return v___x_7775_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Async_Waiter_race___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector_spec__1___redArg___lam__1___boxed(
    mut v_lose_7785_: *mut LeanObject,
    mut v___y_7786_: *mut LeanObject,
    mut v___f_7787_: *mut LeanObject,
    mut v_x_7788_: *mut LeanObject,
    mut v___y_7789_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_7790_: *mut LeanObject = core::ptr::null_mut();
    v_res_7790_ = l_Std_Async_Waiter_race___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector_spec__1___redArg___lam__1(v_lose_7785_, v___y_7786_, v___f_7787_, v_x_7788_);
    lean_dec(v___y_7786_);
    return v_res_7790_;
}
pub unsafe fn l_Std_Async_Waiter_race___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector_spec__1___redArg(
    mut v_w_7791_: *mut LeanObject,
    mut v_lose_7792_: *mut LeanObject,
    mut v___y_7793_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_finished_7795_: *mut LeanObject = core::ptr::null_mut();
    let mut v_promise_7796_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7797_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_7798_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_7799_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7801_: u8 = 0;
    let mut v___x_7802_: u8 = 0;
    let mut v___x_7803_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7804_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7805_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7806_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7807_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7808_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7809_: u8 = 0;
    let mut v___x_7810_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7811_: u8 = 0;
    let mut v___x_7812_: u8 = 0;
    let mut v___x_7813_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_finished_7795_ = lean_ctor_get(v_w_7791_, 0);
                lean_inc(v_finished_7795_);
                v_promise_7796_ = lean_ctor_get(v_w_7791_, 1);
                lean_inc(v_promise_7796_);
                lean_dec_ref(v_w_7791_);
                v___x_7797_ = lean_st_ref_take(v_finished_7795_);
                v___f_7798_ = lean_alloc_closure(l_Std_Async_Waiter_race___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__1___redArg___lam__0___boxed as *mut core::ffi::c_void, 3, 1);
                lean_closure_set(v___f_7798_, 0, v_promise_7796_);
                lean_inc(v___y_7793_);
                v___f_7799_ = lean_alloc_closure(l_Std_Async_Waiter_race___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector_spec__1___redArg___lam__1___boxed as *mut core::ffi::c_void, 5, 3);
                lean_closure_set(v___f_7799_, 0, v_lose_7792_);
                lean_closure_set(v___f_7799_, 1, v___y_7793_);
                lean_closure_set(v___f_7799_, 2, v___f_7798_);
                v___x_7811_ = (lean_unbox(v___x_7797_) as u8);
                lean_dec(v___x_7797_);
                if v___x_7811_ == 0 {
                    v___x_7812_ = 1;
                    v___y_7801_ = v___x_7812_;
                    state = 1;
                    continue;
                } else {
                    v___x_7813_ = 0;
                    v___y_7801_ = v___x_7813_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_7802_ = 1;
                v___x_7803_ = lean_box((v___x_7802_) as usize);
                v___x_7804_ = lean_st_ref_set(v_finished_7795_, v___x_7803_);
                lean_dec(v_finished_7795_);
                v___x_7805_ = lean_box((v___y_7801_) as usize);
                v___x_7806_ = lean_alloc_ctor(1, 1, (0) as u32);
                lean_ctor_set(v___x_7806_, 0, v___x_7805_);
                v___x_7807_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_7807_, 0, v___x_7806_);
                v___x_7808_ = lean_unsigned_to_nat(0);
                v___x_7809_ = 0;
                v___x_7810_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(
                    lean_box(0),
                    lean_box(0),
                    v___x_7808_,
                    v___x_7809_,
                    v___x_7807_,
                    v___f_7799_,
                );
                return v___x_7810_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Async_Waiter_race___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector_spec__1___redArg___boxed(
    mut v_w_7814_: *mut LeanObject,
    mut v_lose_7815_: *mut LeanObject,
    mut v___y_7816_: *mut LeanObject,
    mut v___y_7817_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_7818_: *mut LeanObject = core::ptr::null_mut();
    v_res_7818_ = l_Std_Async_Waiter_race___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector_spec__1___redArg(v_w_7814_, v_lose_7815_, v___y_7816_);
    lean_dec(v___y_7816_);
    return v_res_7818_;
}
pub unsafe fn l_Std_Async_Waiter_race___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector_spec__1(
    mut v_00_u03b1_7819_: *mut LeanObject,
    mut v_w_7820_: *mut LeanObject,
    mut v_lose_7821_: *mut LeanObject,
    mut v___y_7822_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_7824_: *mut LeanObject = core::ptr::null_mut();
    v___x_7824_ = l_Std_Async_Waiter_race___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector_spec__1___redArg(v_w_7820_, v_lose_7821_, v___y_7822_);
    return v___x_7824_;
}
pub unsafe fn l_Std_Async_Waiter_race___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector_spec__1___boxed(
    mut v_00_u03b1_7825_: *mut LeanObject,
    mut v_w_7826_: *mut LeanObject,
    mut v_lose_7827_: *mut LeanObject,
    mut v___y_7828_: *mut LeanObject,
    mut v___y_7829_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_7830_: *mut LeanObject = core::ptr::null_mut();
    v_res_7830_ = l_Std_Async_Waiter_race___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector_spec__1(v_00_u03b1_7825_, v_w_7826_, v_lose_7827_, v___y_7828_);
    lean_dec(v___y_7828_);
    return v_res_7830_;
}
pub unsafe fn l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector___redArg___lam__1(
    mut v_x_7831_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___y_7834_: u8 = 0;
    let mut v___x_7835_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7836_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7837_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_7838_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7840_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_7841_: u8 = 0;
    let mut v___x_7843_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7844_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7845_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7846_: u8 = 0;
    let mut v_a_7847_: *mut LeanObject = core::ptr::null_mut();
    let mut v_producers_7848_: *mut LeanObject = core::ptr::null_mut();
    let mut v_closed_7849_: u8 = 0;
    let mut v___x_7850_: u8 = 0;
    let mut v___x_7851_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_7831_) == 0 {
                    v_a_7838_ = lean_ctor_get(v_x_7831_, 0);
                    v_isSharedCheck_7846_ = (!lean_is_exclusive(v_x_7831_)) as u8;
                    if v_isSharedCheck_7846_ == 0 {
                        v___x_7840_ = v_x_7831_;
                        v_isShared_7841_ = v_isSharedCheck_7846_;
                        state = 2;
                        continue;
                    } else {
                        lean_inc(v_a_7838_);
                        lean_dec(v_x_7831_);
                        v___x_7840_ = lean_box(0);
                        v_isShared_7841_ = v_isSharedCheck_7846_;
                        state = 2;
                        continue;
                    }
                } else {
                    v_a_7847_ = lean_ctor_get(v_x_7831_, 0);
                    lean_inc(v_a_7847_);
                    lean_dec_ref_known(v_x_7831_, 1);
                    v_producers_7848_ = lean_ctor_get(v_a_7847_, 0);
                    lean_inc_ref(v_producers_7848_);
                    v_closed_7849_ = lean_ctor_get_uint8(
                        v_a_7847_,
                        (core::mem::size_of::<*mut LeanObject>() * 2) as u32,
                    );
                    lean_dec(v_a_7847_);
                    v___x_7850_ = l_Std_Queue_isEmpty___redArg(v_producers_7848_);
                    lean_dec_ref(v_producers_7848_);
                    if v___x_7850_ == 0 {
                        v___x_7851_ = 1;
                        v___y_7834_ = v___x_7851_;
                        state = 1;
                        continue;
                    } else {
                        v___y_7834_ = v_closed_7849_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_7835_ = lean_box((v___y_7834_) as usize);
                v___x_7836_ = lean_alloc_ctor(1, 1, (0) as u32);
                lean_ctor_set(v___x_7836_, 0, v___x_7835_);
                v___x_7837_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_7837_, 0, v___x_7836_);
                return v___x_7837_;
            }
            2 => {
                if v_isShared_7841_ == 0 {
                    v___x_7843_ = v___x_7840_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_7845_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_7845_, 0, v_a_7838_);
                    v___x_7843_ = v_reuseFailAlloc_7845_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_7844_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_7844_, 0, v___x_7843_);
                return v___x_7844_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector___redArg___lam__1___boxed(
    mut v_x_7852_: *mut LeanObject,
    mut v___y_7853_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_7854_: *mut LeanObject = core::ptr::null_mut();
    v_res_7854_ =
        l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector___redArg___lam__1(
            v_x_7852_,
        );
    return v_res_7854_;
}
pub unsafe fn l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector___redArg___lam__2(
    mut v___y_7855_: *mut LeanObject,
    mut v_waiter_7856_: *mut LeanObject,
    mut v_x_7857_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_7859_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7861_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_7862_: u8 = 0;
    let mut v___x_7864_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7865_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7866_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7867_: u8 = 0;
    let mut v_a_7868_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7869_: u8 = 0;
    let mut v___x_7870_: *mut LeanObject = core::ptr::null_mut();
    let mut v_producers_7871_: *mut LeanObject = core::ptr::null_mut();
    let mut v_consumers_7872_: *mut LeanObject = core::ptr::null_mut();
    let mut v_closed_7873_: u8 = 0;
    let mut v___x_7875_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_7876_: u8 = 0;
    let mut v___x_7877_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7878_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7880_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7881_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7882_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7883_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7884_: u8 = 0;
    let mut v_lose_7885_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7886_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_7857_) == 0 {
                    lean_dec_ref(v_waiter_7856_);
                    v_a_7859_ = lean_ctor_get(v_x_7857_, 0);
                    v_isSharedCheck_7867_ = (!lean_is_exclusive(v_x_7857_)) as u8;
                    if v_isSharedCheck_7867_ == 0 {
                        v___x_7861_ = v_x_7857_;
                        v_isShared_7862_ = v_isSharedCheck_7867_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_7859_);
                        lean_dec(v_x_7857_);
                        v___x_7861_ = lean_box(0);
                        v_isShared_7862_ = v_isSharedCheck_7867_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_7868_ = lean_ctor_get(v_x_7857_, 0);
                    lean_inc(v_a_7868_);
                    lean_dec_ref_known(v_x_7857_, 1);
                    v___x_7869_ = (lean_unbox(v_a_7868_) as u8);
                    lean_dec(v_a_7868_);
                    if v___x_7869_ == 0 {
                        v___x_7870_ = lean_st_ref_take(v___y_7855_);
                        v_producers_7871_ = lean_ctor_get(v___x_7870_, 0);
                        v_consumers_7872_ = lean_ctor_get(v___x_7870_, 1);
                        v_closed_7873_ = lean_ctor_get_uint8(
                            v___x_7870_,
                            (core::mem::size_of::<*mut LeanObject>() * 2) as u32,
                        );
                        v_isSharedCheck_7884_ = (!lean_is_exclusive(v___x_7870_)) as u8;
                        if v_isSharedCheck_7884_ == 0 {
                            v___x_7875_ = v___x_7870_;
                            v_isShared_7876_ = v_isSharedCheck_7884_;
                            state = 3;
                            continue;
                        } else {
                            lean_inc(v_consumers_7872_);
                            lean_inc(v_producers_7871_);
                            lean_dec(v___x_7870_);
                            v___x_7875_ = lean_box(0);
                            v_isShared_7876_ = v_isSharedCheck_7884_;
                            state = 3;
                            continue;
                        }
                    } else {
                        v_lose_7885_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector___redArg___lam__3___closed__2;
                        v___x_7886_ = l_Std_Async_Waiter_race___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector_spec__1___redArg(v_waiter_7856_, v_lose_7885_, v___y_7855_);
                        return v___x_7886_;
                    }
                }
            }
            1 => {
                if v_isShared_7862_ == 0 {
                    v___x_7864_ = v___x_7861_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_7866_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_7866_, 0, v_a_7859_);
                    v___x_7864_ = v_reuseFailAlloc_7866_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_7865_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_7865_, 0, v___x_7864_);
                return v___x_7865_;
            }
            3 => {
                v___x_7877_ = lean_alloc_ctor(1, 1, (0) as u32);
                lean_ctor_set(v___x_7877_, 0, v_waiter_7856_);
                v___x_7878_ = l_Std_Queue_enqueue___redArg(v___x_7877_, v_consumers_7872_);
                if v_isShared_7876_ == 0 {
                    lean_ctor_set(v___x_7875_, 1, v___x_7878_);
                    v___x_7880_ = v___x_7875_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_7883_ = lean_alloc_ctor(0, 2, (1) as u32);
                    lean_ctor_set(v_reuseFailAlloc_7883_, 0, v_producers_7871_);
                    lean_ctor_set(v_reuseFailAlloc_7883_, 1, v___x_7878_);
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_7883_,
                        (core::mem::size_of::<*mut LeanObject>() * 2) as u32,
                        v_closed_7873_,
                    );
                    v___x_7880_ = v_reuseFailAlloc_7883_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_7881_ = lean_st_ref_set(v___y_7855_, v___x_7880_);
                v___x_7882_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector___redArg___lam__3___closed__1;
                return v___x_7882_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector___redArg___lam__2___boxed(
    mut v___y_7887_: *mut LeanObject,
    mut v_waiter_7888_: *mut LeanObject,
    mut v_x_7889_: *mut LeanObject,
    mut v___y_7890_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_7891_: *mut LeanObject = core::ptr::null_mut();
    v_res_7891_ =
        l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector___redArg___lam__2(
            v___y_7887_,
            v_waiter_7888_,
            v_x_7889_,
        );
    lean_dec(v___y_7887_);
    return v_res_7891_;
}
pub unsafe fn l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector___redArg___lam__0(
    mut v___f_7892_: *mut LeanObject,
    mut v_waiter_7893_: *mut LeanObject,
    mut v___y_7894_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_7896_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7897_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7898_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7899_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7900_: u8 = 0;
    let mut v___x_7901_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_7902_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7903_: *mut LeanObject = core::ptr::null_mut();
    v___x_7896_ = lean_st_ref_get(v___y_7894_);
    v___x_7897_ = lean_alloc_ctor(1, 1, (0) as u32);
    lean_ctor_set(v___x_7897_, 0, v___x_7896_);
    v___x_7898_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_7898_, 0, v___x_7897_);
    v___x_7899_ = lean_unsigned_to_nat(0);
    v___x_7900_ = 0;
    v___x_7901_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(
        lean_box(0),
        lean_box(0),
        v___x_7899_,
        v___x_7900_,
        v___x_7898_,
        v___f_7892_,
    );
    lean_inc(v___y_7894_);
    v___f_7902_ = lean_alloc_closure(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector___redArg___lam__2___boxed as *mut core::ffi::c_void, 4, 2);
    lean_closure_set(v___f_7902_, 0, v___y_7894_);
    lean_closure_set(v___f_7902_, 1, v_waiter_7893_);
    v___x_7903_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(
        lean_box(0),
        lean_box(0),
        v___x_7899_,
        v___x_7900_,
        v___x_7901_,
        v___f_7902_,
    );
    return v___x_7903_;
}
pub unsafe fn l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector___redArg___lam__0___boxed(
    mut v___f_7904_: *mut LeanObject,
    mut v_waiter_7905_: *mut LeanObject,
    mut v___y_7906_: *mut LeanObject,
    mut v___y_7907_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_7908_: *mut LeanObject = core::ptr::null_mut();
    v_res_7908_ =
        l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector___redArg___lam__0(
            v___f_7904_,
            v_waiter_7905_,
            v___y_7906_,
        );
    lean_dec(v___y_7906_);
    return v_res_7908_;
}
pub unsafe fn l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector___redArg___lam__3(
    mut v___f_7909_: *mut LeanObject,
    mut v_ch_7910_: *mut LeanObject,
    mut v_waiter_7911_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_7913_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7914_: *mut LeanObject = core::ptr::null_mut();
    v___f_7913_ = lean_alloc_closure(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector___redArg___lam__0___boxed as *mut core::ffi::c_void, 4, 2);
    lean_closure_set(v___f_7913_, 0, v___f_7909_);
    lean_closure_set(v___f_7913_, 1, v_waiter_7911_);
    v___x_7914_ = l_Std_Mutex_atomically___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__2___redArg(v_ch_7910_, v___f_7913_);
    return v___x_7914_;
}
pub unsafe fn l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector___redArg___lam__3___boxed(
    mut v___f_7915_: *mut LeanObject,
    mut v_ch_7916_: *mut LeanObject,
    mut v_waiter_7917_: *mut LeanObject,
    mut v___y_7918_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_7919_: *mut LeanObject = core::ptr::null_mut();
    v_res_7919_ =
        l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector___redArg___lam__3(
            v___f_7915_,
            v_ch_7916_,
            v_waiter_7917_,
        );
    return v_res_7919_;
}
pub unsafe fn l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector___redArg___lam__5(
    mut v___y_7920_: *mut LeanObject,
    mut v___f_7921_: *mut LeanObject,
    mut v_x_7922_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_7924_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7926_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_7927_: u8 = 0;
    let mut v___x_7929_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7930_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7931_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7932_: u8 = 0;
    let mut v_a_7933_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7934_: u8 = 0;
    let mut v___x_7935_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7936_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7937_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7938_: u8 = 0;
    let mut v___x_7939_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_7922_) == 0 {
                    lean_dec_ref(v___f_7921_);
                    v_a_7924_ = lean_ctor_get(v_x_7922_, 0);
                    v_isSharedCheck_7932_ = (!lean_is_exclusive(v_x_7922_)) as u8;
                    if v_isSharedCheck_7932_ == 0 {
                        v___x_7926_ = v_x_7922_;
                        v_isShared_7927_ = v_isSharedCheck_7932_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_7924_);
                        lean_dec(v_x_7922_);
                        v___x_7926_ = lean_box(0);
                        v_isShared_7927_ = v_isSharedCheck_7932_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_7933_ = lean_ctor_get(v_x_7922_, 0);
                    lean_inc(v_a_7933_);
                    lean_dec_ref_known(v_x_7922_, 1);
                    v___x_7934_ = (lean_unbox(v_a_7933_) as u8);
                    lean_dec(v_a_7933_);
                    if v___x_7934_ == 0 {
                        lean_dec_ref(v___f_7921_);
                        v___x_7935_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector___redArg___lam__7___closed__1;
                        return v___x_7935_;
                    } else {
                        v___x_7936_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector_spec__0___redArg(v___y_7920_);
                        v___x_7937_ = lean_unsigned_to_nat(0);
                        v___x_7938_ = 0;
                        v___x_7939_ =
                            l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(
                                lean_box(0),
                                lean_box(0),
                                v___x_7937_,
                                v___x_7938_,
                                v___x_7936_,
                                v___f_7921_,
                            );
                        return v___x_7939_;
                    }
                }
            }
            1 => {
                if v_isShared_7927_ == 0 {
                    v___x_7929_ = v___x_7926_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_7931_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_7931_, 0, v_a_7924_);
                    v___x_7929_ = v_reuseFailAlloc_7931_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_7930_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_7930_, 0, v___x_7929_);
                return v___x_7930_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector___redArg___lam__5___boxed(
    mut v___y_7940_: *mut LeanObject,
    mut v___f_7941_: *mut LeanObject,
    mut v_x_7942_: *mut LeanObject,
    mut v___y_7943_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_7944_: *mut LeanObject = core::ptr::null_mut();
    v_res_7944_ =
        l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector___redArg___lam__5(
            v___y_7940_,
            v___f_7941_,
            v_x_7942_,
        );
    lean_dec(v___y_7940_);
    return v_res_7944_;
}
pub unsafe fn l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector___redArg___lam__4(
    mut v___f_7945_: *mut LeanObject,
    mut v___f_7946_: *mut LeanObject,
    mut v___y_7947_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_7949_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7950_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7951_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7952_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7953_: u8 = 0;
    let mut v___x_7954_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_7955_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7956_: *mut LeanObject = core::ptr::null_mut();
    v___x_7949_ = lean_st_ref_get(v___y_7947_);
    v___x_7950_ = lean_alloc_ctor(1, 1, (0) as u32);
    lean_ctor_set(v___x_7950_, 0, v___x_7949_);
    v___x_7951_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_7951_, 0, v___x_7950_);
    v___x_7952_ = lean_unsigned_to_nat(0);
    v___x_7953_ = 0;
    v___x_7954_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(
        lean_box(0),
        lean_box(0),
        v___x_7952_,
        v___x_7953_,
        v___x_7951_,
        v___f_7945_,
    );
    lean_inc(v___y_7947_);
    v___f_7955_ = lean_alloc_closure(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector___redArg___lam__5___boxed as *mut core::ffi::c_void, 4, 2);
    lean_closure_set(v___f_7955_, 0, v___y_7947_);
    lean_closure_set(v___f_7955_, 1, v___f_7946_);
    v___x_7956_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(
        lean_box(0),
        lean_box(0),
        v___x_7952_,
        v___x_7953_,
        v___x_7954_,
        v___f_7955_,
    );
    return v___x_7956_;
}
pub unsafe fn l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector___redArg___lam__4___boxed(
    mut v___f_7957_: *mut LeanObject,
    mut v___f_7958_: *mut LeanObject,
    mut v___y_7959_: *mut LeanObject,
    mut v___y_7960_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_7961_: *mut LeanObject = core::ptr::null_mut();
    v_res_7961_ =
        l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector___redArg___lam__4(
            v___f_7957_,
            v___f_7958_,
            v___y_7959_,
        );
    lean_dec(v___y_7959_);
    return v_res_7961_;
}
pub unsafe fn l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector___redArg___lam__6(
    mut v_producers_7962_: *mut LeanObject,
    mut v_closed_7963_: u8,
    mut v___y_7964_: *mut LeanObject,
    mut v_x_7965_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_7967_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7969_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_7970_: u8 = 0;
    let mut v___x_7972_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7973_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7974_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7975_: u8 = 0;
    let mut v_a_7976_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7978_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_7979_: u8 = 0;
    let mut v___x_7980_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7981_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7983_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7984_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7985_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7986_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_7965_) == 0 {
                    lean_dec_ref(v_producers_7962_);
                    v_a_7967_ = lean_ctor_get(v_x_7965_, 0);
                    v_isSharedCheck_7975_ = (!lean_is_exclusive(v_x_7965_)) as u8;
                    if v_isSharedCheck_7975_ == 0 {
                        v___x_7969_ = v_x_7965_;
                        v_isShared_7970_ = v_isSharedCheck_7975_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_7967_);
                        lean_dec(v_x_7965_);
                        v___x_7969_ = lean_box(0);
                        v_isShared_7970_ = v_isSharedCheck_7975_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_7976_ = lean_ctor_get(v_x_7965_, 0);
                    v_isSharedCheck_7986_ = (!lean_is_exclusive(v_x_7965_)) as u8;
                    if v_isSharedCheck_7986_ == 0 {
                        v___x_7978_ = v_x_7965_;
                        v_isShared_7979_ = v_isSharedCheck_7986_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_7976_);
                        lean_dec(v_x_7965_);
                        v___x_7978_ = lean_box(0);
                        v_isShared_7979_ = v_isSharedCheck_7986_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_7970_ == 0 {
                    v___x_7972_ = v___x_7969_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_7974_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_7974_, 0, v_a_7967_);
                    v___x_7972_ = v_reuseFailAlloc_7974_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_7973_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_7973_, 0, v___x_7972_);
                return v___x_7973_;
            }
            3 => {
                v___x_7980_ = lean_alloc_ctor(0, 2, (1) as u32);
                lean_ctor_set(v___x_7980_, 0, v_producers_7962_);
                lean_ctor_set(v___x_7980_, 1, v_a_7976_);
                lean_ctor_set_uint8(
                    v___x_7980_,
                    (core::mem::size_of::<*mut LeanObject>() * 2) as u32,
                    v_closed_7963_,
                );
                v___x_7981_ = lean_st_ref_set(v___y_7964_, v___x_7980_);
                if v_isShared_7979_ == 0 {
                    lean_ctor_set(v___x_7978_, 0, v___x_7981_);
                    v___x_7983_ = v___x_7978_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_7985_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_7985_, 0, v___x_7981_);
                    v___x_7983_ = v_reuseFailAlloc_7985_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_7984_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_7984_, 0, v___x_7983_);
                return v___x_7984_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector___redArg___lam__6___boxed(
    mut v_producers_7987_: *mut LeanObject,
    mut v_closed_7988_: *mut LeanObject,
    mut v___y_7989_: *mut LeanObject,
    mut v_x_7990_: *mut LeanObject,
    mut v___y_7991_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_closed_boxed_7992_: u8 = 0;
    let mut v_res_7993_: *mut LeanObject = core::ptr::null_mut();
    v_closed_boxed_7992_ = (lean_unbox(v_closed_7988_) as u8);
    v_res_7993_ =
        l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector___redArg___lam__6(
            v_producers_7987_,
            v_closed_boxed_7992_,
            v___y_7989_,
            v_x_7990_,
        );
    lean_dec(v___y_7989_);
    return v_res_7993_;
}
pub unsafe fn l_List_filterAuxM___at___00Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector_spec__2_spec__2___redArg___lam__0___boxed(
    mut v_tail_7994_: *mut LeanObject,
    mut v_x_7995_: *mut LeanObject,
    mut v_head_7996_: *mut LeanObject,
    mut v_x_7997_: *mut LeanObject,
    mut v___y_7998_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_7999_: *mut LeanObject = core::ptr::null_mut();
    v_res_7999_ = l_List_filterAuxM___at___00Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector_spec__2_spec__2___redArg___lam__0(v_tail_7994_, v_x_7995_, v_head_7996_, v_x_7997_);
    return v_res_7999_;
}
pub unsafe fn l_List_filterAuxM___at___00Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector_spec__2_spec__2___redArg(
    mut v_x_8000_: *mut LeanObject,
    mut v_x_8001_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_8003_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8004_: *mut LeanObject = core::ptr::null_mut();
    let mut v_head_8005_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_8006_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_8007_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_8009_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8010_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8011_: u8 = 0;
    let mut v___x_8012_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8013_: *mut LeanObject = core::ptr::null_mut();
    let mut v_finished_8014_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8016_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_8017_: u8 = 0;
    let mut v_finished_8018_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8019_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_8020_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8022_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8023_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8024_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8025_: u8 = 0;
    let mut v___x_8026_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8027_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_8028_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_8000_) == 0 {
                    v___x_8003_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v___x_8003_, 0, v_x_8001_);
                    v___x_8004_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_8004_, 0, v___x_8003_);
                    return v___x_8004_;
                } else {
                    v_head_8005_ = lean_ctor_get(v_x_8000_, 0);
                    lean_inc_n(v_head_8005_, 2);
                    v_tail_8006_ = lean_ctor_get(v_x_8000_, 1);
                    lean_inc(v_tail_8006_);
                    lean_dec_ref_known(v_x_8000_, 2);
                    v___f_8007_ = lean_alloc_closure(l_List_filterAuxM___at___00Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector_spec__2_spec__2___redArg___lam__0___boxed as *mut core::ffi::c_void, 5, 3);
                    lean_closure_set(v___f_8007_, 0, v_tail_8006_);
                    lean_closure_set(v___f_8007_, 1, v_x_8001_);
                    lean_closure_set(v___f_8007_, 2, v_head_8005_);
                    if lean_obj_tag(v_head_8005_) == 0 {
                        lean_dec_ref_known(v_head_8005_, 1);
                        v___x_8013_ = l_List_filterAuxM___at___00Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__3_spec__3___redArg___closed__1;
                        v_val_8009_ = v___x_8013_;
                        state = 1;
                        continue;
                    } else {
                        v_finished_8014_ = lean_ctor_get(v_head_8005_, 0);
                        v_isSharedCheck_8028_ = (!lean_is_exclusive(v_head_8005_)) as u8;
                        if v_isSharedCheck_8028_ == 0 {
                            v___x_8016_ = v_head_8005_;
                            v_isShared_8017_ = v_isSharedCheck_8028_;
                            state = 2;
                            continue;
                        } else {
                            lean_inc(v_finished_8014_);
                            lean_dec(v_head_8005_);
                            v___x_8016_ = lean_box(0);
                            v_isShared_8017_ = v_isSharedCheck_8028_;
                            state = 2;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v___x_8010_ = lean_unsigned_to_nat(0);
                v___x_8011_ = 0;
                v___x_8012_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(
                    lean_box(0),
                    lean_box(0),
                    v___x_8010_,
                    v___x_8011_,
                    v_val_8009_,
                    v___f_8007_,
                );
                return v___x_8012_;
            }
            2 => {
                v_finished_8018_ = lean_ctor_get(v_finished_8014_, 0);
                lean_inc(v_finished_8018_);
                lean_dec_ref(v_finished_8014_);
                v___x_8019_ = lean_st_ref_get(v_finished_8018_);
                lean_dec(v_finished_8018_);
                v___f_8020_ = l_List_filterAuxM___at___00Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__3_spec__3___redArg___closed__2;
                if v_isShared_8017_ == 0 {
                    lean_ctor_set(v___x_8016_, 0, v___x_8019_);
                    v___x_8022_ = v___x_8016_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_8027_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_8027_, 0, v___x_8019_);
                    v___x_8022_ = v_reuseFailAlloc_8027_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_8023_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_8023_, 0, v___x_8022_);
                v___x_8024_ = lean_unsigned_to_nat(0);
                v___x_8025_ = 0;
                v___x_8026_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(
                    lean_box(0),
                    lean_box(0),
                    v___x_8024_,
                    v___x_8025_,
                    v___x_8023_,
                    v___f_8020_,
                );
                v_val_8009_ = v___x_8026_;
                state = 1;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_filterAuxM___at___00Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector_spec__2_spec__2___redArg___lam__0(
    mut v_tail_8029_: *mut LeanObject,
    mut v_x_8030_: *mut LeanObject,
    mut v_head_8031_: *mut LeanObject,
    mut v_x_8032_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_8034_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8036_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_8037_: u8 = 0;
    let mut v___x_8039_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8040_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8041_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_8042_: u8 = 0;
    let mut v_a_8043_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8044_: u8 = 0;
    let mut v___x_8045_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8046_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8047_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_8032_) == 0 {
                    lean_dec_ref(v_head_8031_);
                    lean_dec(v_x_8030_);
                    lean_dec(v_tail_8029_);
                    v_a_8034_ = lean_ctor_get(v_x_8032_, 0);
                    v_isSharedCheck_8042_ = (!lean_is_exclusive(v_x_8032_)) as u8;
                    if v_isSharedCheck_8042_ == 0 {
                        v___x_8036_ = v_x_8032_;
                        v_isShared_8037_ = v_isSharedCheck_8042_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_8034_);
                        lean_dec(v_x_8032_);
                        v___x_8036_ = lean_box(0);
                        v_isShared_8037_ = v_isSharedCheck_8042_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_8043_ = lean_ctor_get(v_x_8032_, 0);
                    lean_inc(v_a_8043_);
                    lean_dec_ref_known(v_x_8032_, 1);
                    v___x_8044_ = (lean_unbox(v_a_8043_) as u8);
                    lean_dec(v_a_8043_);
                    if v___x_8044_ == 0 {
                        lean_dec_ref(v_head_8031_);
                        v___x_8045_ = l_List_filterAuxM___at___00Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector_spec__2_spec__2___redArg(v_tail_8029_, v_x_8030_);
                        return v___x_8045_;
                    } else {
                        v___x_8046_ = lean_alloc_ctor(1, 2, (0) as u32);
                        lean_ctor_set(v___x_8046_, 0, v_head_8031_);
                        lean_ctor_set(v___x_8046_, 1, v_x_8030_);
                        v___x_8047_ = l_List_filterAuxM___at___00Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector_spec__2_spec__2___redArg(v_tail_8029_, v___x_8046_);
                        return v___x_8047_;
                    }
                }
            }
            1 => {
                if v_isShared_8037_ == 0 {
                    v___x_8039_ = v___x_8036_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_8041_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_8041_, 0, v_a_8034_);
                    v___x_8039_ = v_reuseFailAlloc_8041_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_8040_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_8040_, 0, v___x_8039_);
                return v___x_8040_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_filterAuxM___at___00Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector_spec__2_spec__2___redArg___boxed(
    mut v_x_8048_: *mut LeanObject,
    mut v_x_8049_: *mut LeanObject,
    mut v___y_8050_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_8051_: *mut LeanObject = core::ptr::null_mut();
    v_res_8051_ = l_List_filterAuxM___at___00Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector_spec__2_spec__2___redArg(v_x_8048_, v_x_8049_);
    return v_res_8051_;
}
pub unsafe fn l_Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector_spec__2___redArg___lam__3(
    mut v_eList_8052_: *mut LeanObject,
    mut v___x_8053_: *mut LeanObject,
    mut v___f_8054_: *mut LeanObject,
    mut v_x_8055_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_8057_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8059_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_8060_: u8 = 0;
    let mut v___x_8062_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8063_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8064_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_8065_: u8 = 0;
    let mut v_a_8066_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8067_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8068_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8069_: u8 = 0;
    let mut v___x_8070_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_8071_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8072_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_8055_) == 0 {
                    lean_dec_ref(v___f_8054_);
                    lean_dec(v___x_8053_);
                    lean_dec(v_eList_8052_);
                    v_a_8057_ = lean_ctor_get(v_x_8055_, 0);
                    v_isSharedCheck_8065_ = (!lean_is_exclusive(v_x_8055_)) as u8;
                    if v_isSharedCheck_8065_ == 0 {
                        v___x_8059_ = v_x_8055_;
                        v_isShared_8060_ = v_isSharedCheck_8065_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_8057_);
                        lean_dec(v_x_8055_);
                        v___x_8059_ = lean_box(0);
                        v_isShared_8060_ = v_isSharedCheck_8065_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_8066_ = lean_ctor_get(v_x_8055_, 0);
                    lean_inc(v_a_8066_);
                    lean_dec_ref_known(v_x_8055_, 1);
                    lean_inc(v___x_8053_);
                    v___x_8067_ = l_List_filterAuxM___at___00Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector_spec__2_spec__2___redArg(v_eList_8052_, v___x_8053_);
                    v___x_8068_ = lean_unsigned_to_nat(0);
                    v___x_8069_ = 0;
                    v___x_8070_ =
                        l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(
                            lean_box(0),
                            lean_box(0),
                            v___x_8068_,
                            v___x_8069_,
                            v___x_8067_,
                            v___f_8054_,
                        );
                    v___f_8071_ = lean_alloc_closure(l_Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__3___redArg___lam__2___boxed as *mut core::ffi::c_void, 4, 2);
                    lean_closure_set(v___f_8071_, 0, v_a_8066_);
                    lean_closure_set(v___f_8071_, 1, v___x_8053_);
                    v___x_8072_ =
                        l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(
                            lean_box(0),
                            lean_box(0),
                            v___x_8068_,
                            v___x_8069_,
                            v___x_8070_,
                            v___f_8071_,
                        );
                    return v___x_8072_;
                }
            }
            1 => {
                if v_isShared_8060_ == 0 {
                    v___x_8062_ = v___x_8059_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_8064_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_8064_, 0, v_a_8057_);
                    v___x_8062_ = v_reuseFailAlloc_8064_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_8063_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_8063_, 0, v___x_8062_);
                return v___x_8063_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector_spec__2___redArg___lam__3___boxed(
    mut v_eList_8073_: *mut LeanObject,
    mut v___x_8074_: *mut LeanObject,
    mut v___f_8075_: *mut LeanObject,
    mut v_x_8076_: *mut LeanObject,
    mut v___y_8077_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_8078_: *mut LeanObject = core::ptr::null_mut();
    v_res_8078_ = l_Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector_spec__2___redArg___lam__3(v_eList_8073_, v___x_8074_, v___f_8075_, v_x_8076_);
    return v_res_8078_;
}
pub unsafe fn l_Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector_spec__2___redArg(
    mut v_q_8079_: *mut LeanObject,
    mut v___y_8080_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_eList_8082_: *mut LeanObject = core::ptr::null_mut();
    let mut v_dList_8083_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8084_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8085_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_8086_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8087_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8088_: u8 = 0;
    let mut v___x_8089_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_8090_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8091_: *mut LeanObject = core::ptr::null_mut();
    v_eList_8082_ = lean_ctor_get(v_q_8079_, 0);
    lean_inc(v_eList_8082_);
    v_dList_8083_ = lean_ctor_get(v_q_8079_, 1);
    lean_inc(v_dList_8083_);
    lean_dec_ref(v_q_8079_);
    v___x_8084_ = lean_box(0);
    v___x_8085_ = l_List_filterAuxM___at___00Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector_spec__2_spec__2___redArg(v_dList_8083_, v___x_8084_);
    v___f_8086_ = l_Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__3___redArg___closed__0;
    v___x_8087_ = lean_unsigned_to_nat(0);
    v___x_8088_ = 0;
    v___x_8089_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(
        lean_box(0),
        lean_box(0),
        v___x_8087_,
        v___x_8088_,
        v___x_8085_,
        v___f_8086_,
    );
    v___f_8090_ = lean_alloc_closure(l_Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector_spec__2___redArg___lam__3___boxed as *mut core::ffi::c_void, 5, 3);
    lean_closure_set(v___f_8090_, 0, v_eList_8082_);
    lean_closure_set(v___f_8090_, 1, v___x_8084_);
    lean_closure_set(v___f_8090_, 2, v___f_8086_);
    v___x_8091_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(
        lean_box(0),
        lean_box(0),
        v___x_8087_,
        v___x_8088_,
        v___x_8089_,
        v___f_8090_,
    );
    return v___x_8091_;
}
pub unsafe fn l_Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector_spec__2___redArg___boxed(
    mut v_q_8092_: *mut LeanObject,
    mut v___y_8093_: *mut LeanObject,
    mut v___y_8094_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_8095_: *mut LeanObject = core::ptr::null_mut();
    v_res_8095_ = l_Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector_spec__2___redArg(v_q_8092_, v___y_8093_);
    lean_dec(v___y_8093_);
    return v_res_8095_;
}
pub unsafe fn l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector___redArg___lam__7(
    mut v___y_8096_: *mut LeanObject,
    mut v_x_8097_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_8099_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8101_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_8102_: u8 = 0;
    let mut v___x_8104_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8105_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8106_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_8107_: u8 = 0;
    let mut v_a_8108_: *mut LeanObject = core::ptr::null_mut();
    let mut v_producers_8109_: *mut LeanObject = core::ptr::null_mut();
    let mut v_consumers_8110_: *mut LeanObject = core::ptr::null_mut();
    let mut v_closed_8111_: u8 = 0;
    let mut v___x_8112_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8113_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_8114_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8115_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8116_: u8 = 0;
    let mut v___x_8117_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_8097_) == 0 {
                    v_a_8099_ = lean_ctor_get(v_x_8097_, 0);
                    v_isSharedCheck_8107_ = (!lean_is_exclusive(v_x_8097_)) as u8;
                    if v_isSharedCheck_8107_ == 0 {
                        v___x_8101_ = v_x_8097_;
                        v_isShared_8102_ = v_isSharedCheck_8107_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_8099_);
                        lean_dec(v_x_8097_);
                        v___x_8101_ = lean_box(0);
                        v_isShared_8102_ = v_isSharedCheck_8107_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_8108_ = lean_ctor_get(v_x_8097_, 0);
                    lean_inc(v_a_8108_);
                    lean_dec_ref_known(v_x_8097_, 1);
                    v_producers_8109_ = lean_ctor_get(v_a_8108_, 0);
                    lean_inc_ref(v_producers_8109_);
                    v_consumers_8110_ = lean_ctor_get(v_a_8108_, 1);
                    lean_inc_ref(v_consumers_8110_);
                    v_closed_8111_ = lean_ctor_get_uint8(
                        v_a_8108_,
                        (core::mem::size_of::<*mut LeanObject>() * 2) as u32,
                    );
                    lean_dec(v_a_8108_);
                    v___x_8112_ = l_Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector_spec__2___redArg(v_consumers_8110_, v___y_8096_);
                    v___x_8113_ = lean_box((v_closed_8111_) as usize);
                    lean_inc(v___y_8096_);
                    v___f_8114_ = lean_alloc_closure(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector___redArg___lam__6___boxed as *mut core::ffi::c_void, 5, 3);
                    lean_closure_set(v___f_8114_, 0, v_producers_8109_);
                    lean_closure_set(v___f_8114_, 1, v___x_8113_);
                    lean_closure_set(v___f_8114_, 2, v___y_8096_);
                    v___x_8115_ = lean_unsigned_to_nat(0);
                    v___x_8116_ = 0;
                    v___x_8117_ =
                        l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(
                            lean_box(0),
                            lean_box(0),
                            v___x_8115_,
                            v___x_8116_,
                            v___x_8112_,
                            v___f_8114_,
                        );
                    return v___x_8117_;
                }
            }
            1 => {
                if v_isShared_8102_ == 0 {
                    v___x_8104_ = v___x_8101_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_8106_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_8106_, 0, v_a_8099_);
                    v___x_8104_ = v_reuseFailAlloc_8106_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_8105_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_8105_, 0, v___x_8104_);
                return v___x_8105_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector___redArg___lam__7___boxed(
    mut v___y_8118_: *mut LeanObject,
    mut v_x_8119_: *mut LeanObject,
    mut v___y_8120_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_8121_: *mut LeanObject = core::ptr::null_mut();
    v_res_8121_ =
        l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector___redArg___lam__7(
            v___y_8118_,
            v_x_8119_,
        );
    lean_dec(v___y_8118_);
    return v_res_8121_;
}
pub unsafe fn l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector___redArg___lam__8(
    mut v___y_8122_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_8124_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_8125_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8126_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8127_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8128_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8129_: u8 = 0;
    let mut v___x_8130_: *mut LeanObject = core::ptr::null_mut();
    v___x_8124_ = lean_st_ref_get(v___y_8122_);
    lean_inc(v___y_8122_);
    v___f_8125_ = lean_alloc_closure(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector___redArg___lam__7___boxed as *mut core::ffi::c_void, 3, 1);
    lean_closure_set(v___f_8125_, 0, v___y_8122_);
    v___x_8126_ = lean_alloc_ctor(1, 1, (0) as u32);
    lean_ctor_set(v___x_8126_, 0, v___x_8124_);
    v___x_8127_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_8127_, 0, v___x_8126_);
    v___x_8128_ = lean_unsigned_to_nat(0);
    v___x_8129_ = 0;
    v___x_8130_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(
        lean_box(0),
        lean_box(0),
        v___x_8128_,
        v___x_8129_,
        v___x_8127_,
        v___f_8125_,
    );
    return v___x_8130_;
}
pub unsafe fn l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector___redArg___lam__8___boxed(
    mut v___y_8131_: *mut LeanObject,
    mut v___y_8132_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_8133_: *mut LeanObject = core::ptr::null_mut();
    v_res_8133_ =
        l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector___redArg___lam__8(
            v___y_8131_,
        );
    lean_dec(v___y_8131_);
    return v_res_8133_;
}
pub unsafe fn l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector___redArg(
    mut v_ch_8139_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_8140_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_8141_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_8142_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_8143_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8144_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8145_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8146_: *mut LeanObject = core::ptr::null_mut();
    v___f_8140_ =
        l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector___redArg___closed__0;
    lean_inc_ref_n(v_ch_8139_, 2);
    v___f_8141_ = lean_alloc_closure(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector___redArg___lam__3___boxed as *mut core::ffi::c_void, 4, 2);
    lean_closure_set(v___f_8141_, 0, v___f_8140_);
    lean_closure_set(v___f_8141_, 1, v_ch_8139_);
    v___f_8142_ =
        l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector___redArg___closed__1;
    v___f_8143_ =
        l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector___redArg___closed__2;
    v___x_8144_ = lean_alloc_closure(l_Std_Mutex_atomically___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__2___boxed as *mut core::ffi::c_void, 5, 4);
    lean_closure_set(v___x_8144_, 0, lean_box(0));
    lean_closure_set(v___x_8144_, 1, lean_box(0));
    lean_closure_set(v___x_8144_, 2, v_ch_8139_);
    lean_closure_set(v___x_8144_, 3, v___f_8142_);
    v___x_8145_ = lean_alloc_closure(l_Std_Mutex_atomically___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__2___boxed as *mut core::ffi::c_void, 5, 4);
    lean_closure_set(v___x_8145_, 0, lean_box(0));
    lean_closure_set(v___x_8145_, 1, lean_box(0));
    lean_closure_set(v___x_8145_, 2, v_ch_8139_);
    lean_closure_set(v___x_8145_, 3, v___f_8143_);
    v___x_8146_ = lean_alloc_ctor(0, 3, (0) as u32);
    lean_ctor_set(v___x_8146_, 0, v___x_8144_);
    lean_ctor_set(v___x_8146_, 1, v___f_8141_);
    lean_ctor_set(v___x_8146_, 2, v___x_8145_);
    return v___x_8146_;
}
pub unsafe fn l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector(
    mut v_00_u03b1_8147_: *mut LeanObject,
    mut v_ch_8148_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_8149_: *mut LeanObject = core::ptr::null_mut();
    v___x_8149_ =
        l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector___redArg(v_ch_8148_);
    return v___x_8149_;
}
pub unsafe fn l_Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector_spec__2(
    mut v_00_u03b1_8150_: *mut LeanObject,
    mut v_q_8151_: *mut LeanObject,
    mut v___y_8152_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_8154_: *mut LeanObject = core::ptr::null_mut();
    v___x_8154_ = l_Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector_spec__2___redArg(v_q_8151_, v___y_8152_);
    return v___x_8154_;
}
pub unsafe fn l_Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector_spec__2___boxed(
    mut v_00_u03b1_8155_: *mut LeanObject,
    mut v_q_8156_: *mut LeanObject,
    mut v___y_8157_: *mut LeanObject,
    mut v___y_8158_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_8159_: *mut LeanObject = core::ptr::null_mut();
    v_res_8159_ = l_Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector_spec__2(v_00_u03b1_8155_, v_q_8156_, v___y_8157_);
    lean_dec(v___y_8157_);
    return v_res_8159_;
}
pub unsafe fn l_List_filterAuxM___at___00Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector_spec__2_spec__2(
    mut v_00_u03b1_8160_: *mut LeanObject,
    mut v_x_8161_: *mut LeanObject,
    mut v_x_8162_: *mut LeanObject,
    mut v___y_8163_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_8165_: *mut LeanObject = core::ptr::null_mut();
    v___x_8165_ = l_List_filterAuxM___at___00Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector_spec__2_spec__2___redArg(v_x_8161_, v_x_8162_);
    return v___x_8165_;
}
pub unsafe fn l_List_filterAuxM___at___00Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector_spec__2_spec__2___boxed(
    mut v_00_u03b1_8166_: *mut LeanObject,
    mut v_x_8167_: *mut LeanObject,
    mut v_x_8168_: *mut LeanObject,
    mut v___y_8169_: *mut LeanObject,
    mut v___y_8170_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_8171_: *mut LeanObject = core::ptr::null_mut();
    v_res_8171_ = l_List_filterAuxM___at___00Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector_spec__2_spec__2(v_00_u03b1_8166_, v_x_8167_, v_x_8168_, v___y_8169_);
    lean_dec(v___y_8169_);
    return v_res_8171_;
}
pub unsafe fn l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_Consumer_resolve___redArg(
    mut v_c_8172_: *mut LeanObject,
    mut v_b_8173_: u8,
) -> *mut LeanObject {
    let mut v_promise_8175_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8176_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8177_: *mut LeanObject = core::ptr::null_mut();
    v_promise_8175_ = lean_ctor_get(v_c_8172_, 0);
    v___x_8176_ = lean_box((v_b_8173_) as usize);
    v___x_8177_ = lean_io_promise_resolve(v___x_8176_, v_promise_8175_);
    return v___x_8177_;
}
pub unsafe fn l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_Consumer_resolve___redArg___boxed(
    mut v_c_8178_: *mut LeanObject,
    mut v_b_8179_: *mut LeanObject,
    mut v_a_8180_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_b_boxed_8181_: u8 = 0;
    let mut v_res_8182_: *mut LeanObject = core::ptr::null_mut();
    v_b_boxed_8181_ = (lean_unbox(v_b_8179_) as u8);
    v_res_8182_ =
        l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_Consumer_resolve___redArg(
            v_c_8178_,
            v_b_boxed_8181_,
        );
    lean_dec_ref(v_c_8178_);
    return v_res_8182_;
}
pub unsafe fn l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_Consumer_resolve(
    mut v_00_u03b1_8183_: *mut LeanObject,
    mut v_c_8184_: *mut LeanObject,
    mut v_b_8185_: u8,
) -> *mut LeanObject {
    let mut v___x_8187_: *mut LeanObject = core::ptr::null_mut();
    v___x_8187_ =
        l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_Consumer_resolve___redArg(
            v_c_8184_, v_b_8185_,
        );
    return v___x_8187_;
}
pub unsafe fn l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_Consumer_resolve___boxed(
    mut v_00_u03b1_8188_: *mut LeanObject,
    mut v_c_8189_: *mut LeanObject,
    mut v_b_8190_: *mut LeanObject,
    mut v_a_8191_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_b_boxed_8192_: u8 = 0;
    let mut v_res_8193_: *mut LeanObject = core::ptr::null_mut();
    v_b_boxed_8192_ = (lean_unbox(v_b_8190_) as u8);
    v_res_8193_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_Consumer_resolve(
        v_00_u03b1_8188_,
        v_c_8189_,
        v_b_boxed_8192_,
    );
    lean_dec_ref(v_c_8189_);
    return v_res_8193_;
}
pub unsafe fn l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_new___redArg___lam__0(
    mut v_x_8194_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_8196_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8197_: *mut LeanObject = core::ptr::null_mut();
    v___x_8196_ = lean_box(0);
    v___x_8197_ = lean_st_mk_ref(v___x_8196_);
    return v___x_8197_;
}
pub unsafe fn l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_new___redArg___lam__0___boxed(
    mut v_x_8198_: *mut LeanObject,
    mut v___y_8199_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_8200_: *mut LeanObject = core::ptr::null_mut();
    v_res_8200_ =
        l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_new___redArg___lam__0(
            v_x_8198_,
        );
    lean_dec(v_x_8198_);
    return v_res_8200_;
}
pub unsafe fn l___private_Init_Data_Vector_Basic_0__Vector_mapM_go___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_new_spec__0___redArg(
    mut v_n_8201_: *mut LeanObject,
    mut v_f_8202_: *mut LeanObject,
    mut v_xs_8203_: *mut LeanObject,
    mut v_k_8204_: *mut LeanObject,
    mut v_acc_8205_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_8207_: u8 = 0;
    let mut v___x_8208_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8209_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8210_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8211_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8212_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_8207_ = lean_nat_dec_lt(v_k_8204_, v_n_8201_);
                if v___x_8207_ == 0 {
                    lean_dec(v_k_8204_);
                    lean_dec_ref(v_f_8202_);
                    return v_acc_8205_;
                } else {
                    v___x_8208_ = lean_array_fget_borrowed(v_xs_8203_, v_k_8204_);
                    lean_inc_ref(v_f_8202_);
                    lean_inc(v___x_8208_);
                    v___x_8209_ = lean_apply_2(v_f_8202_, v___x_8208_, lean_box(0));
                    v___x_8210_ = lean_unsigned_to_nat(1);
                    v___x_8211_ = lean_nat_add(v_k_8204_, v___x_8210_);
                    lean_dec(v_k_8204_);
                    v___x_8212_ = lean_array_push(v_acc_8205_, v___x_8209_);
                    v_k_8204_ = v___x_8211_;
                    v_acc_8205_ = v___x_8212_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Vector_Basic_0__Vector_mapM_go___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_new_spec__0___redArg___boxed(
    mut v_n_8214_: *mut LeanObject,
    mut v_f_8215_: *mut LeanObject,
    mut v_xs_8216_: *mut LeanObject,
    mut v_k_8217_: *mut LeanObject,
    mut v_acc_8218_: *mut LeanObject,
    mut v___y_8219_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_8220_: *mut LeanObject = core::ptr::null_mut();
    v_res_8220_ = l___private_Init_Data_Vector_Basic_0__Vector_mapM_go___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_new_spec__0___redArg(v_n_8214_, v_f_8215_, v_xs_8216_, v_k_8217_, v_acc_8218_);
    lean_dec_ref(v_xs_8216_);
    lean_dec(v_n_8214_);
    return v_res_8220_;
}
pub unsafe fn l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_new___redArg(
    mut v_capacity_8224_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_8226_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8227_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8228_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8229_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8230_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8231_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8232_: u8 = 0;
    let mut v___x_8233_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8234_: *mut LeanObject = core::ptr::null_mut();
    v___f_8226_ =
        l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_new___redArg___closed__0;
    lean_inc(v_capacity_8224_);
    v___x_8227_ = l_Array_range(v_capacity_8224_);
    v___x_8228_ = lean_unsigned_to_nat(0);
    v___x_8229_ =
        l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_new___redArg___closed__1;
    v___x_8230_ = l___private_Init_Data_Vector_Basic_0__Vector_mapM_go___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_new_spec__0___redArg(v_capacity_8224_, v___f_8226_, v___x_8227_, v___x_8228_, v___x_8229_);
    lean_dec_ref(v___x_8227_);
    v___x_8231_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_new___redArg___closed__0), core::ptr::addr_of_mut!(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_new___redArg___closed__0_once), _init_l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_new___redArg___closed__0);
    v___x_8232_ = 0;
    v___x_8233_ = lean_alloc_ctor(0, 7, (1) as u32);
    lean_ctor_set(v___x_8233_, 0, v___x_8231_);
    lean_ctor_set(v___x_8233_, 1, v___x_8231_);
    lean_ctor_set(v___x_8233_, 2, v_capacity_8224_);
    lean_ctor_set(v___x_8233_, 3, v___x_8230_);
    lean_ctor_set(v___x_8233_, 4, v___x_8228_);
    lean_ctor_set(v___x_8233_, 5, v___x_8228_);
    lean_ctor_set(v___x_8233_, 6, v___x_8228_);
    lean_ctor_set_uint8(
        v___x_8233_,
        (core::mem::size_of::<*mut LeanObject>() * 7) as u32,
        v___x_8232_,
    );
    v___x_8234_ = l_Std_Mutex_new___redArg(v___x_8233_);
    return v___x_8234_;
}
pub unsafe fn l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_new___redArg___boxed(
    mut v_capacity_8235_: *mut LeanObject,
    mut v_a_8236_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_8237_: *mut LeanObject = core::ptr::null_mut();
    v_res_8237_ =
        l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_new___redArg(v_capacity_8235_);
    return v_res_8237_;
}
pub unsafe fn l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_new(
    mut v_00_u03b1_8238_: *mut LeanObject,
    mut v_capacity_8239_: *mut LeanObject,
    mut v_hcap_8240_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_8242_: *mut LeanObject = core::ptr::null_mut();
    v___x_8242_ =
        l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_new___redArg(v_capacity_8239_);
    return v___x_8242_;
}
pub unsafe fn l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_new___boxed(
    mut v_00_u03b1_8243_: *mut LeanObject,
    mut v_capacity_8244_: *mut LeanObject,
    mut v_hcap_8245_: *mut LeanObject,
    mut v_a_8246_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_8247_: *mut LeanObject = core::ptr::null_mut();
    v_res_8247_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_new(
        v_00_u03b1_8243_,
        v_capacity_8244_,
        v_hcap_8245_,
    );
    return v_res_8247_;
}
pub unsafe fn l___private_Init_Data_Vector_Basic_0__Vector_mapM_go___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_new_spec__0(
    mut v_00_u03b1_8248_: *mut LeanObject,
    mut v_00_u03b2_8249_: *mut LeanObject,
    mut v_n_8250_: *mut LeanObject,
    mut v_f_8251_: *mut LeanObject,
    mut v_xs_8252_: *mut LeanObject,
    mut v_k_8253_: *mut LeanObject,
    mut v_h_8254_: *mut LeanObject,
    mut v_acc_8255_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_8257_: *mut LeanObject = core::ptr::null_mut();
    v___x_8257_ = l___private_Init_Data_Vector_Basic_0__Vector_mapM_go___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_new_spec__0___redArg(v_n_8250_, v_f_8251_, v_xs_8252_, v_k_8253_, v_acc_8255_);
    return v___x_8257_;
}
pub unsafe fn l___private_Init_Data_Vector_Basic_0__Vector_mapM_go___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_new_spec__0___boxed(
    mut v_00_u03b1_8258_: *mut LeanObject,
    mut v_00_u03b2_8259_: *mut LeanObject,
    mut v_n_8260_: *mut LeanObject,
    mut v_f_8261_: *mut LeanObject,
    mut v_xs_8262_: *mut LeanObject,
    mut v_k_8263_: *mut LeanObject,
    mut v_h_8264_: *mut LeanObject,
    mut v_acc_8265_: *mut LeanObject,
    mut v___y_8266_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_8267_: *mut LeanObject = core::ptr::null_mut();
    v_res_8267_ = l___private_Init_Data_Vector_Basic_0__Vector_mapM_go___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_new_spec__0(v_00_u03b1_8258_, v_00_u03b2_8259_, v_n_8260_, v_f_8261_, v_xs_8262_, v_k_8263_, v_h_8264_, v_acc_8265_);
    lean_dec_ref(v_xs_8262_);
    lean_dec(v_n_8260_);
    return v_res_8267_;
}
pub unsafe fn l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_incMod(
    mut v_idx_8268_: *mut LeanObject,
    mut v_cap_8269_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_8270_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8271_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8272_: u8 = 0;
    v___x_8270_ = lean_unsigned_to_nat(1);
    v___x_8271_ = lean_nat_add(v_idx_8268_, v___x_8270_);
    v___x_8272_ = lean_nat_dec_eq(v___x_8271_, v_cap_8269_);
    if v___x_8272_ == 0 {
        return v___x_8271_;
    } else {
        let mut v___x_8273_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v___x_8271_);
        v___x_8273_ = lean_unsigned_to_nat(0);
        return v___x_8273_;
    }
}
pub unsafe fn l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_incMod___boxed(
    mut v_idx_8274_: *mut LeanObject,
    mut v_cap_8275_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_8276_: *mut LeanObject = core::ptr::null_mut();
    v_res_8276_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_incMod(
        v_idx_8274_,
        v_cap_8275_,
    );
    lean_dec(v_cap_8275_);
    lean_dec(v_idx_8274_);
    return v_res_8276_;
}
pub unsafe fn l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_trySend_x27___redArg(
    mut v_v_8277_: *mut LeanObject,
    mut v_a_8278_: *mut LeanObject,
) -> u8 {
    let mut v_st_8281_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_8282_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8283_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8284_: u8 = 0;
    let mut v___x_8285_: *mut LeanObject = core::ptr::null_mut();
    let mut v_producers_8286_: *mut LeanObject = core::ptr::null_mut();
    let mut v_consumers_8287_: *mut LeanObject = core::ptr::null_mut();
    let mut v_capacity_8288_: *mut LeanObject = core::ptr::null_mut();
    let mut v_buf_8289_: *mut LeanObject = core::ptr::null_mut();
    let mut v_bufCount_8290_: *mut LeanObject = core::ptr::null_mut();
    let mut v_sendIdx_8291_: *mut LeanObject = core::ptr::null_mut();
    let mut v_recvIdx_8292_: *mut LeanObject = core::ptr::null_mut();
    let mut v_closed_8293_: u8 = 0;
    let mut v___x_8295_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_8296_: u8 = 0;
    let mut v___x_8297_: u8 = 0;
    let mut v___x_8298_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8299_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8300_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8301_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8302_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_8304_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8306_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8307_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_8308_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_8309_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_8310_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8311_: u8 = 0;
    let mut v___x_8312_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8313_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8314_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8315_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8316_: u8 = 0;
    let mut v___x_8317_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8318_: u8 = 0;
    let mut v_isSharedCheck_8319_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_8285_ = lean_st_ref_get(v_a_8278_);
                v_producers_8286_ = lean_ctor_get(v___x_8285_, 0);
                v_consumers_8287_ = lean_ctor_get(v___x_8285_, 1);
                v_capacity_8288_ = lean_ctor_get(v___x_8285_, 2);
                v_buf_8289_ = lean_ctor_get(v___x_8285_, 3);
                v_bufCount_8290_ = lean_ctor_get(v___x_8285_, 4);
                v_sendIdx_8291_ = lean_ctor_get(v___x_8285_, 5);
                v_recvIdx_8292_ = lean_ctor_get(v___x_8285_, 6);
                v_closed_8293_ = lean_ctor_get_uint8(
                    v___x_8285_,
                    (core::mem::size_of::<*mut LeanObject>() * 7) as u32,
                );
                v_isSharedCheck_8319_ = (!lean_is_exclusive(v___x_8285_)) as u8;
                if v_isSharedCheck_8319_ == 0 {
                    v___x_8295_ = v___x_8285_;
                    v_isShared_8296_ = v_isSharedCheck_8319_;
                    state = 2;
                    continue;
                } else {
                    lean_inc(v_recvIdx_8292_);
                    lean_inc(v_sendIdx_8291_);
                    lean_inc(v_bufCount_8290_);
                    lean_inc(v_buf_8289_);
                    lean_inc(v_capacity_8288_);
                    lean_inc(v_consumers_8287_);
                    lean_inc(v_producers_8286_);
                    lean_dec(v___x_8285_);
                    v___x_8295_ = lean_box(0);
                    v_isShared_8296_ = v_isSharedCheck_8319_;
                    state = 2;
                    continue;
                }
            }
            1 => {
                v___x_8283_ = lean_st_ref_set(v___y_8282_, v_st_8281_);
                v___x_8284_ = 1;
                return v___x_8284_;
            }
            2 => {
                v___x_8297_ = lean_nat_dec_eq(v_bufCount_8290_, v_capacity_8288_);
                if v___x_8297_ == 0 {
                    v___x_8298_ = lean_array_fget_borrowed(v_buf_8289_, v_sendIdx_8291_);
                    v___x_8299_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v___x_8299_, 0, v_v_8277_);
                    v___x_8300_ = lean_st_ref_set(v___x_8298_, v___x_8299_);
                    v___x_8301_ = lean_unsigned_to_nat(1);
                    v___x_8302_ = lean_nat_add(v_bufCount_8290_, v___x_8301_);
                    lean_dec(v_bufCount_8290_);
                    v___x_8315_ = lean_nat_add(v_sendIdx_8291_, v___x_8301_);
                    lean_dec(v_sendIdx_8291_);
                    v___x_8316_ = lean_nat_dec_eq(v___x_8315_, v_capacity_8288_);
                    if v___x_8316_ == 0 {
                        v___y_8304_ = v___x_8315_;
                        state = 3;
                        continue;
                    } else {
                        lean_dec(v___x_8315_);
                        v___x_8317_ = lean_unsigned_to_nat(0);
                        v___y_8304_ = v___x_8317_;
                        state = 3;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_8295_);
                    lean_dec(v_recvIdx_8292_);
                    lean_dec(v_sendIdx_8291_);
                    lean_dec(v_bufCount_8290_);
                    lean_dec_ref(v_buf_8289_);
                    lean_dec(v_capacity_8288_);
                    lean_dec_ref(v_consumers_8287_);
                    lean_dec_ref(v_producers_8286_);
                    lean_dec(v_v_8277_);
                    v___x_8318_ = 0;
                    return v___x_8318_;
                }
            }
            3 => {
                lean_inc(v_recvIdx_8292_);
                lean_inc(v___y_8304_);
                lean_inc(v___x_8302_);
                lean_inc_ref(v_buf_8289_);
                lean_inc(v_capacity_8288_);
                lean_inc_ref(v_consumers_8287_);
                lean_inc_ref(v_producers_8286_);
                if v_isShared_8296_ == 0 {
                    lean_ctor_set(v___x_8295_, 5, v___y_8304_);
                    lean_ctor_set(v___x_8295_, 4, v___x_8302_);
                    v___x_8306_ = v___x_8295_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_8314_ = lean_alloc_ctor(0, 7, (1) as u32);
                    lean_ctor_set(v_reuseFailAlloc_8314_, 0, v_producers_8286_);
                    lean_ctor_set(v_reuseFailAlloc_8314_, 1, v_consumers_8287_);
                    lean_ctor_set(v_reuseFailAlloc_8314_, 2, v_capacity_8288_);
                    lean_ctor_set(v_reuseFailAlloc_8314_, 3, v_buf_8289_);
                    lean_ctor_set(v_reuseFailAlloc_8314_, 4, v___x_8302_);
                    lean_ctor_set(v_reuseFailAlloc_8314_, 5, v___y_8304_);
                    lean_ctor_set(v_reuseFailAlloc_8314_, 6, v_recvIdx_8292_);
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_8314_,
                        (core::mem::size_of::<*mut LeanObject>() * 7) as u32,
                        v_closed_8293_,
                    );
                    v___x_8306_ = v_reuseFailAlloc_8314_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_8307_ = l_Std_Queue_dequeue_x3f___redArg(v_consumers_8287_);
                if lean_obj_tag(v___x_8307_) == 1 {
                    lean_dec_ref(v___x_8306_);
                    v_val_8308_ = lean_ctor_get(v___x_8307_, 0);
                    lean_inc(v_val_8308_);
                    lean_dec_ref_known(v___x_8307_, 1);
                    v_fst_8309_ = lean_ctor_get(v_val_8308_, 0);
                    lean_inc(v_fst_8309_);
                    v_snd_8310_ = lean_ctor_get(v_val_8308_, 1);
                    lean_inc(v_snd_8310_);
                    lean_dec(v_val_8308_);
                    v___x_8311_ = 1;
                    v___x_8312_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_Consumer_resolve___redArg(v_fst_8309_, v___x_8311_);
                    lean_dec(v_fst_8309_);
                    v___x_8313_ = lean_alloc_ctor(0, 7, (1) as u32);
                    lean_ctor_set(v___x_8313_, 0, v_producers_8286_);
                    lean_ctor_set(v___x_8313_, 1, v_snd_8310_);
                    lean_ctor_set(v___x_8313_, 2, v_capacity_8288_);
                    lean_ctor_set(v___x_8313_, 3, v_buf_8289_);
                    lean_ctor_set(v___x_8313_, 4, v___x_8302_);
                    lean_ctor_set(v___x_8313_, 5, v___y_8304_);
                    lean_ctor_set(v___x_8313_, 6, v_recvIdx_8292_);
                    lean_ctor_set_uint8(
                        v___x_8313_,
                        (core::mem::size_of::<*mut LeanObject>() * 7) as u32,
                        v_closed_8293_,
                    );
                    v_st_8281_ = v___x_8313_;
                    v___y_8282_ = v_a_8278_;
                    state = 1;
                    continue;
                } else {
                    lean_dec(v___x_8307_);
                    lean_dec(v___y_8304_);
                    lean_dec(v___x_8302_);
                    lean_dec(v_recvIdx_8292_);
                    lean_dec_ref(v_buf_8289_);
                    lean_dec(v_capacity_8288_);
                    lean_dec_ref(v_producers_8286_);
                    v_st_8281_ = v___x_8306_;
                    v___y_8282_ = v_a_8278_;
                    state = 1;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_trySend_x27___redArg___boxed(
    mut v_v_8320_: *mut LeanObject,
    mut v_a_8321_: *mut LeanObject,
    mut v_a_8322_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_8323_: u8 = 0;
    let mut v_r_8324_: *mut LeanObject = core::ptr::null_mut();
    v_res_8323_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_trySend_x27___redArg(
        v_v_8320_, v_a_8321_,
    );
    lean_dec(v_a_8321_);
    v_r_8324_ = lean_box((v_res_8323_) as usize);
    return v_r_8324_;
}
pub unsafe fn l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_trySend_x27(
    mut v_00_u03b1_8325_: *mut LeanObject,
    mut v_v_8326_: *mut LeanObject,
    mut v_a_8327_: *mut LeanObject,
) -> u8 {
    let mut v___x_8329_: u8 = 0;
    v___x_8329_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_trySend_x27___redArg(
        v_v_8326_, v_a_8327_,
    );
    return v___x_8329_;
}
pub unsafe fn l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_trySend_x27___boxed(
    mut v_00_u03b1_8330_: *mut LeanObject,
    mut v_v_8331_: *mut LeanObject,
    mut v_a_8332_: *mut LeanObject,
    mut v_a_8333_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_8334_: u8 = 0;
    let mut v_r_8335_: *mut LeanObject = core::ptr::null_mut();
    v_res_8334_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_trySend_x27(
        v_00_u03b1_8330_,
        v_v_8331_,
        v_a_8332_,
    );
    lean_dec(v_a_8332_);
    v_r_8335_ = lean_box((v_res_8334_) as usize);
    return v_r_8335_;
}
pub unsafe fn l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_trySend___redArg___lam__0(
    mut v_v_8336_: *mut LeanObject,
    mut v___y_8337_: *mut LeanObject,
) -> u8 {
    let mut v___x_8339_: *mut LeanObject = core::ptr::null_mut();
    let mut v_closed_8340_: u8 = 0;
    v___x_8339_ = lean_st_ref_get(v___y_8337_);
    v_closed_8340_ = lean_ctor_get_uint8(
        v___x_8339_,
        (core::mem::size_of::<*mut LeanObject>() * 7) as u32,
    );
    lean_dec(v___x_8339_);
    if v_closed_8340_ == 0 {
        let mut v___x_8341_: u8 = 0;
        v___x_8341_ =
            l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_trySend_x27___redArg(
                v_v_8336_,
                v___y_8337_,
            );
        return v___x_8341_;
    } else {
        let mut v___x_8342_: u8 = 0;
        lean_dec(v_v_8336_);
        v___x_8342_ = 0;
        return v___x_8342_;
    }
}
pub unsafe fn l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_trySend___redArg___lam__0___boxed(
    mut v_v_8343_: *mut LeanObject,
    mut v___y_8344_: *mut LeanObject,
    mut v___y_8345_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_8346_: u8 = 0;
    let mut v_r_8347_: *mut LeanObject = core::ptr::null_mut();
    v_res_8346_ =
        l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_trySend___redArg___lam__0(
            v_v_8343_,
            v___y_8344_,
        );
    lean_dec(v___y_8344_);
    v_r_8347_ = lean_box((v_res_8346_) as usize);
    return v_r_8347_;
}
pub unsafe fn l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_trySend___redArg(
    mut v_ch_8348_: *mut LeanObject,
    mut v_v_8349_: *mut LeanObject,
) -> u8 {
    let mut v___f_8351_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8352_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8353_: u8 = 0;
    v___f_8351_ = lean_alloc_closure(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_trySend___redArg___lam__0___boxed as *mut core::ffi::c_void, 3, 1);
    lean_closure_set(v___f_8351_, 0, v_v_8349_);
    v___x_8352_ = l_Std_Mutex_atomically___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_trySend_spec__1___redArg(v_ch_8348_, v___f_8351_);
    v___x_8353_ = (lean_unbox(v___x_8352_) as u8);
    lean_dec(v___x_8352_);
    return v___x_8353_;
}
pub unsafe fn l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_trySend___redArg___boxed(
    mut v_ch_8354_: *mut LeanObject,
    mut v_v_8355_: *mut LeanObject,
    mut v_a_8356_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_8357_: u8 = 0;
    let mut v_r_8358_: *mut LeanObject = core::ptr::null_mut();
    v_res_8357_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_trySend___redArg(
        v_ch_8354_, v_v_8355_,
    );
    v_r_8358_ = lean_box((v_res_8357_) as usize);
    return v_r_8358_;
}
pub unsafe fn l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_trySend(
    mut v_00_u03b1_8359_: *mut LeanObject,
    mut v_ch_8360_: *mut LeanObject,
    mut v_v_8361_: *mut LeanObject,
) -> u8 {
    let mut v___x_8363_: u8 = 0;
    v___x_8363_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_trySend___redArg(
        v_ch_8360_, v_v_8361_,
    );
    return v___x_8363_;
}
pub unsafe fn l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_trySend___boxed(
    mut v_00_u03b1_8364_: *mut LeanObject,
    mut v_ch_8365_: *mut LeanObject,
    mut v_v_8366_: *mut LeanObject,
    mut v_a_8367_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_8368_: u8 = 0;
    let mut v_r_8369_: *mut LeanObject = core::ptr::null_mut();
    v_res_8368_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_trySend(
        v_00_u03b1_8364_,
        v_ch_8365_,
        v_v_8366_,
    );
    v_r_8369_ = lean_box((v_res_8368_) as usize);
    return v_r_8369_;
}
pub unsafe fn l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_send___redArg___lam__1(
    mut v_v_8370_: *mut LeanObject,
    mut v___f_8371_: *mut LeanObject,
    mut v___y_8372_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_8374_: *mut LeanObject = core::ptr::null_mut();
    let mut v_closed_8375_: u8 = 0;
    let mut v___x_8376_: u8 = 0;
    let mut v___x_8377_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8378_: *mut LeanObject = core::ptr::null_mut();
    let mut v_producers_8379_: *mut LeanObject = core::ptr::null_mut();
    let mut v_consumers_8380_: *mut LeanObject = core::ptr::null_mut();
    let mut v_capacity_8381_: *mut LeanObject = core::ptr::null_mut();
    let mut v_buf_8382_: *mut LeanObject = core::ptr::null_mut();
    let mut v_bufCount_8383_: *mut LeanObject = core::ptr::null_mut();
    let mut v_sendIdx_8384_: *mut LeanObject = core::ptr::null_mut();
    let mut v_recvIdx_8385_: *mut LeanObject = core::ptr::null_mut();
    let mut v_closed_8386_: u8 = 0;
    let mut v___x_8388_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_8389_: u8 = 0;
    let mut v___x_8390_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8392_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8393_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8394_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8395_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8396_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8397_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_8398_: u8 = 0;
    let mut v___x_8399_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8400_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_8374_ = lean_st_ref_get(v___y_8372_);
                v_closed_8375_ = lean_ctor_get_uint8(
                    v___x_8374_,
                    (core::mem::size_of::<*mut LeanObject>() * 7) as u32,
                );
                lean_dec(v___x_8374_);
                if v_closed_8375_ == 0 {
                    v___x_8376_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_trySend_x27___redArg(v_v_8370_, v___y_8372_);
                    if v___x_8376_ == 0 {
                        v___x_8377_ = lean_io_promise_new();
                        v___x_8378_ = lean_st_ref_take(v___y_8372_);
                        v_producers_8379_ = lean_ctor_get(v___x_8378_, 0);
                        v_consumers_8380_ = lean_ctor_get(v___x_8378_, 1);
                        v_capacity_8381_ = lean_ctor_get(v___x_8378_, 2);
                        v_buf_8382_ = lean_ctor_get(v___x_8378_, 3);
                        v_bufCount_8383_ = lean_ctor_get(v___x_8378_, 4);
                        v_sendIdx_8384_ = lean_ctor_get(v___x_8378_, 5);
                        v_recvIdx_8385_ = lean_ctor_get(v___x_8378_, 6);
                        v_closed_8386_ = lean_ctor_get_uint8(
                            v___x_8378_,
                            (core::mem::size_of::<*mut LeanObject>() * 7) as u32,
                        );
                        v_isSharedCheck_8398_ = (!lean_is_exclusive(v___x_8378_)) as u8;
                        if v_isSharedCheck_8398_ == 0 {
                            v___x_8388_ = v___x_8378_;
                            v_isShared_8389_ = v_isSharedCheck_8398_;
                            state = 1;
                            continue;
                        } else {
                            lean_inc(v_recvIdx_8385_);
                            lean_inc(v_sendIdx_8384_);
                            lean_inc(v_bufCount_8383_);
                            lean_inc(v_buf_8382_);
                            lean_inc(v_capacity_8381_);
                            lean_inc(v_consumers_8380_);
                            lean_inc(v_producers_8379_);
                            lean_dec(v___x_8378_);
                            v___x_8388_ = lean_box(0);
                            v_isShared_8389_ = v_isSharedCheck_8398_;
                            state = 1;
                            continue;
                        }
                    } else {
                        lean_dec_ref(v___f_8371_);
                        v___x_8399_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_send___redArg___closed__3), core::ptr::addr_of_mut!(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_send___redArg___closed__3_once), _init_l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_send___redArg___closed__3);
                        return v___x_8399_;
                    }
                } else {
                    lean_dec_ref(v___f_8371_);
                    lean_dec(v_v_8370_);
                    v___x_8400_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_send___redArg___closed__1), core::ptr::addr_of_mut!(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_send___redArg___closed__1_once), _init_l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_send___redArg___closed__1);
                    return v___x_8400_;
                }
            }
            1 => {
                lean_inc(v___x_8377_);
                v___x_8390_ = l_Std_Queue_enqueue___redArg(v___x_8377_, v_producers_8379_);
                if v_isShared_8389_ == 0 {
                    lean_ctor_set(v___x_8388_, 0, v___x_8390_);
                    v___x_8392_ = v___x_8388_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_8397_ = lean_alloc_ctor(0, 7, (1) as u32);
                    lean_ctor_set(v_reuseFailAlloc_8397_, 0, v___x_8390_);
                    lean_ctor_set(v_reuseFailAlloc_8397_, 1, v_consumers_8380_);
                    lean_ctor_set(v_reuseFailAlloc_8397_, 2, v_capacity_8381_);
                    lean_ctor_set(v_reuseFailAlloc_8397_, 3, v_buf_8382_);
                    lean_ctor_set(v_reuseFailAlloc_8397_, 4, v_bufCount_8383_);
                    lean_ctor_set(v_reuseFailAlloc_8397_, 5, v_sendIdx_8384_);
                    lean_ctor_set(v_reuseFailAlloc_8397_, 6, v_recvIdx_8385_);
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_8397_,
                        (core::mem::size_of::<*mut LeanObject>() * 7) as u32,
                        v_closed_8386_,
                    );
                    v___x_8392_ = v_reuseFailAlloc_8397_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_8393_ = lean_st_ref_set(v___y_8372_, v___x_8392_);
                v___x_8394_ = lean_io_promise_result_opt(v___x_8377_);
                lean_dec(v___x_8377_);
                v___x_8395_ = lean_unsigned_to_nat(0);
                v___x_8396_ = lean_io_bind_task(v___x_8394_, v___f_8371_, v___x_8395_, v___x_8376_);
                return v___x_8396_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_send___redArg___lam__1___boxed(
    mut v_v_8401_: *mut LeanObject,
    mut v___f_8402_: *mut LeanObject,
    mut v___y_8403_: *mut LeanObject,
    mut v___y_8404_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_8405_: *mut LeanObject = core::ptr::null_mut();
    v_res_8405_ =
        l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_send___redArg___lam__1(
            v_v_8401_,
            v___f_8402_,
            v___y_8403_,
        );
    lean_dec(v___y_8403_);
    return v_res_8405_;
}
pub unsafe fn l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_send___redArg___lam__0(
    mut v_ch_8406_: *mut LeanObject,
    mut v_v_8407_: *mut LeanObject,
    mut v_res_8408_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_8411_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_8412_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8413_: u8 = 0;
    let mut v___x_8414_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_res_8408_) == 0 {
                    lean_dec(v_v_8407_);
                    lean_dec_ref(v_ch_8406_);
                    state = 1;
                    continue;
                } else {
                    v_val_8412_ = lean_ctor_get(v_res_8408_, 0);
                    v___x_8413_ = (lean_unbox(v_val_8412_) as u8);
                    if v___x_8413_ == 0 {
                        lean_dec(v_v_8407_);
                        lean_dec_ref(v_ch_8406_);
                        state = 1;
                        continue;
                    } else {
                        v___x_8414_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_send___redArg(v_ch_8406_, v_v_8407_);
                        return v___x_8414_;
                    }
                }
            }
            1 => {
                v___x_8411_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_send___redArg___closed__1), core::ptr::addr_of_mut!(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_send___redArg___closed__1_once), _init_l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_send___redArg___closed__1);
                return v___x_8411_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_send___redArg___lam__0___boxed(
    mut v_ch_8415_: *mut LeanObject,
    mut v_v_8416_: *mut LeanObject,
    mut v_res_8417_: *mut LeanObject,
    mut v___y_8418_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_8419_: *mut LeanObject = core::ptr::null_mut();
    v_res_8419_ =
        l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_send___redArg___lam__0(
            v_ch_8415_,
            v_v_8416_,
            v_res_8417_,
        );
    lean_dec(v_res_8417_);
    return v_res_8419_;
}
pub unsafe fn l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_send___redArg(
    mut v_ch_8420_: *mut LeanObject,
    mut v_v_8421_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_8423_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_8424_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8425_: *mut LeanObject = core::ptr::null_mut();
    lean_inc(v_v_8421_);
    lean_inc_ref(v_ch_8420_);
    v___f_8423_ = lean_alloc_closure(
        l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_send___redArg___lam__0___boxed
            as *mut core::ffi::c_void,
        4,
        2,
    );
    lean_closure_set(v___f_8423_, 0, v_ch_8420_);
    lean_closure_set(v___f_8423_, 1, v_v_8421_);
    v___f_8424_ = lean_alloc_closure(
        l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_send___redArg___lam__1___boxed
            as *mut core::ffi::c_void,
        4,
        2,
    );
    lean_closure_set(v___f_8424_, 0, v_v_8421_);
    lean_closure_set(v___f_8424_, 1, v___f_8423_);
    v___x_8425_ = l_Std_Mutex_atomically___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_trySend_spec__1___redArg(v_ch_8420_, v___f_8424_);
    return v___x_8425_;
}
pub unsafe fn l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_send___redArg___boxed(
    mut v_ch_8426_: *mut LeanObject,
    mut v_v_8427_: *mut LeanObject,
    mut v_a_8428_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_8429_: *mut LeanObject = core::ptr::null_mut();
    v_res_8429_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_send___redArg(
        v_ch_8426_, v_v_8427_,
    );
    return v_res_8429_;
}
pub unsafe fn l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_send(
    mut v_00_u03b1_8430_: *mut LeanObject,
    mut v_ch_8431_: *mut LeanObject,
    mut v_v_8432_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_8434_: *mut LeanObject = core::ptr::null_mut();
    v___x_8434_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_send___redArg(
        v_ch_8431_, v_v_8432_,
    );
    return v___x_8434_;
}
pub unsafe fn l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_send___boxed(
    mut v_00_u03b1_8435_: *mut LeanObject,
    mut v_ch_8436_: *mut LeanObject,
    mut v_v_8437_: *mut LeanObject,
    mut v_a_8438_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_8439_: *mut LeanObject = core::ptr::null_mut();
    v_res_8439_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_send(
        v_00_u03b1_8435_,
        v_ch_8436_,
        v_v_8437_,
    );
    return v_res_8439_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_close_spec__0___redArg(
    mut v___x_8440_: u8,
    mut v_as_8441_: *mut LeanObject,
    mut v_sz_8442_: usize,
    mut v_i_8443_: usize,
    mut v_b_8444_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_8446_: u8 = 0;
    let mut v___x_8447_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_8448_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8449_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8450_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8451_: usize = 0;
    let mut v___x_8452_: usize = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_8446_ = lean_usize_dec_lt(v_i_8443_, v_sz_8442_);
                if v___x_8446_ == 0 {
                    v___x_8447_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_8447_, 0, v_b_8444_);
                    return v___x_8447_;
                } else {
                    v_a_8448_ = lean_array_uget_borrowed(v_as_8441_, v_i_8443_);
                    v___x_8449_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_Consumer_resolve___redArg(v_a_8448_, v___x_8440_);
                    v___x_8450_ = lean_box(0);
                    v___x_8451_ = 1usize;
                    v___x_8452_ = lean_usize_add(v_i_8443_, v___x_8451_);
                    v_i_8443_ = v___x_8452_;
                    v_b_8444_ = v___x_8450_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_close_spec__0___redArg___boxed(
    mut v___x_8454_: *mut LeanObject,
    mut v_as_8455_: *mut LeanObject,
    mut v_sz_8456_: *mut LeanObject,
    mut v_i_8457_: *mut LeanObject,
    mut v_b_8458_: *mut LeanObject,
    mut v___y_8459_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1136__boxed_8460_: u8 = 0;
    let mut v_sz_boxed_8461_: usize = 0;
    let mut v_i_boxed_8462_: usize = 0;
    let mut v_res_8463_: *mut LeanObject = core::ptr::null_mut();
    v___x_1136__boxed_8460_ = (lean_unbox(v___x_8454_) as u8);
    v_sz_boxed_8461_ = lean_unbox_usize(v_sz_8456_);
    lean_dec(v_sz_8456_);
    v_i_boxed_8462_ = lean_unbox_usize(v_i_8457_);
    lean_dec(v_i_8457_);
    v_res_8463_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_close_spec__0___redArg(v___x_1136__boxed_8460_, v_as_8455_, v_sz_boxed_8461_, v_i_boxed_8462_, v_b_8458_);
    lean_dec_ref(v_as_8455_);
    return v_res_8463_;
}
pub unsafe fn _init_l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_close___redArg___lam__0___closed__0()
-> *mut LeanObject {
    let mut v___x_8464_: *mut LeanObject = core::ptr::null_mut();
    v___x_8464_ = l_Std_Queue_empty(lean_box(0));
    return v___x_8464_;
}
pub unsafe fn l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_close___redArg___lam__0(
    mut v___y_8465_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_8467_: *mut LeanObject = core::ptr::null_mut();
    let mut v_closed_8468_: u8 = 0;
    let mut v_producers_8469_: *mut LeanObject = core::ptr::null_mut();
    let mut v_consumers_8470_: *mut LeanObject = core::ptr::null_mut();
    let mut v_capacity_8471_: *mut LeanObject = core::ptr::null_mut();
    let mut v_buf_8472_: *mut LeanObject = core::ptr::null_mut();
    let mut v_bufCount_8473_: *mut LeanObject = core::ptr::null_mut();
    let mut v_sendIdx_8474_: *mut LeanObject = core::ptr::null_mut();
    let mut v_recvIdx_8475_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8477_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_8478_: u8 = 0;
    let mut v___x_8479_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8480_: *mut LeanObject = core::ptr::null_mut();
    let mut v_sz_8481_: usize = 0;
    let mut v___x_8482_: usize = 0;
    let mut v___x_8483_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8485_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_8486_: u8 = 0;
    let mut v___x_8487_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8488_: u8 = 0;
    let mut v___x_8490_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8491_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8493_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8494_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8495_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_8496_: u8 = 0;
    let mut v_unused_8497_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_8498_: u8 = 0;
    let mut v___x_8499_: u8 = 0;
    let mut v___x_8500_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8501_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_8467_ = lean_st_ref_get(v___y_8465_);
                v_closed_8468_ = lean_ctor_get_uint8(
                    v___x_8467_,
                    (core::mem::size_of::<*mut LeanObject>() * 7) as u32,
                );
                if v_closed_8468_ == 0 {
                    v_producers_8469_ = lean_ctor_get(v___x_8467_, 0);
                    v_consumers_8470_ = lean_ctor_get(v___x_8467_, 1);
                    v_capacity_8471_ = lean_ctor_get(v___x_8467_, 2);
                    v_buf_8472_ = lean_ctor_get(v___x_8467_, 3);
                    v_bufCount_8473_ = lean_ctor_get(v___x_8467_, 4);
                    v_sendIdx_8474_ = lean_ctor_get(v___x_8467_, 5);
                    v_recvIdx_8475_ = lean_ctor_get(v___x_8467_, 6);
                    v_isSharedCheck_8498_ = (!lean_is_exclusive(v___x_8467_)) as u8;
                    if v_isSharedCheck_8498_ == 0 {
                        v___x_8477_ = v___x_8467_;
                        v_isShared_8478_ = v_isSharedCheck_8498_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_recvIdx_8475_);
                        lean_inc(v_sendIdx_8474_);
                        lean_inc(v_bufCount_8473_);
                        lean_inc(v_buf_8472_);
                        lean_inc(v_capacity_8471_);
                        lean_inc(v_consumers_8470_);
                        lean_inc(v_producers_8469_);
                        lean_dec(v___x_8467_);
                        v___x_8477_ = lean_box(0);
                        v_isShared_8478_ = v_isSharedCheck_8498_;
                        state = 1;
                        continue;
                    }
                } else {
                    lean_dec(v___x_8467_);
                    v___x_8499_ = 1;
                    v___x_8500_ = lean_box((v___x_8499_) as usize);
                    v___x_8501_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v___x_8501_, 0, v___x_8500_);
                    return v___x_8501_;
                }
            }
            1 => {
                v___x_8479_ = l_Std_Queue_toArray___redArg(v_consumers_8470_);
                v___x_8480_ = lean_box(0);
                v_sz_8481_ = lean_array_size(v___x_8479_);
                v___x_8482_ = 0usize;
                v___x_8483_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_close_spec__0___redArg(v_closed_8468_, v___x_8479_, v_sz_8481_, v___x_8482_, v___x_8480_);
                lean_dec_ref(v___x_8479_);
                if lean_obj_tag(v___x_8483_) == 0 {
                    v_isSharedCheck_8496_ = (!lean_is_exclusive(v___x_8483_)) as u8;
                    if v_isSharedCheck_8496_ == 0 {
                        v_unused_8497_ = lean_ctor_get(v___x_8483_, 0);
                        lean_dec(v_unused_8497_);
                        v___x_8485_ = v___x_8483_;
                        v_isShared_8486_ = v_isSharedCheck_8496_;
                        state = 2;
                        continue;
                    } else {
                        lean_dec(v___x_8483_);
                        v___x_8485_ = lean_box(0);
                        v_isShared_8486_ = v_isSharedCheck_8496_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_8477_);
                    lean_dec(v_recvIdx_8475_);
                    lean_dec(v_sendIdx_8474_);
                    lean_dec(v_bufCount_8473_);
                    lean_dec_ref(v_buf_8472_);
                    lean_dec(v_capacity_8471_);
                    lean_dec_ref(v_producers_8469_);
                    return v___x_8483_;
                }
            }
            2 => {
                v___x_8487_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_close___redArg___lam__0___closed__0), core::ptr::addr_of_mut!(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_close___redArg___lam__0___closed__0_once), _init_l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_close___redArg___lam__0___closed__0);
                v___x_8488_ = 1;
                if v_isShared_8478_ == 0 {
                    lean_ctor_set(v___x_8477_, 1, v___x_8487_);
                    v___x_8490_ = v___x_8477_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_8495_ = lean_alloc_ctor(0, 7, (1) as u32);
                    lean_ctor_set(v_reuseFailAlloc_8495_, 0, v_producers_8469_);
                    lean_ctor_set(v_reuseFailAlloc_8495_, 1, v___x_8487_);
                    lean_ctor_set(v_reuseFailAlloc_8495_, 2, v_capacity_8471_);
                    lean_ctor_set(v_reuseFailAlloc_8495_, 3, v_buf_8472_);
                    lean_ctor_set(v_reuseFailAlloc_8495_, 4, v_bufCount_8473_);
                    lean_ctor_set(v_reuseFailAlloc_8495_, 5, v_sendIdx_8474_);
                    lean_ctor_set(v_reuseFailAlloc_8495_, 6, v_recvIdx_8475_);
                    v___x_8490_ = v_reuseFailAlloc_8495_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                lean_ctor_set_uint8(
                    v___x_8490_,
                    (core::mem::size_of::<*mut LeanObject>() * 7) as u32,
                    v___x_8488_,
                );
                v___x_8491_ = lean_st_ref_set(v___y_8465_, v___x_8490_);
                if v_isShared_8486_ == 0 {
                    lean_ctor_set(v___x_8485_, 0, v___x_8480_);
                    v___x_8493_ = v___x_8485_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_8494_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_8494_, 0, v___x_8480_);
                    v___x_8493_ = v_reuseFailAlloc_8494_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_8493_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_close___redArg___lam__0___boxed(
    mut v___y_8502_: *mut LeanObject,
    mut v___y_8503_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_8504_: *mut LeanObject = core::ptr::null_mut();
    v_res_8504_ =
        l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_close___redArg___lam__0(
            v___y_8502_,
        );
    lean_dec(v___y_8502_);
    return v_res_8504_;
}
pub unsafe fn l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_close___redArg(
    mut v_ch_8506_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_8508_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8509_: *mut LeanObject = core::ptr::null_mut();
    v___f_8508_ =
        l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_close___redArg___closed__0;
    v___x_8509_ = l_Std_Mutex_atomically___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_close_spec__1___redArg(v_ch_8506_, v___f_8508_);
    return v___x_8509_;
}
pub unsafe fn l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_close___redArg___boxed(
    mut v_ch_8510_: *mut LeanObject,
    mut v_a_8511_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_8512_: *mut LeanObject = core::ptr::null_mut();
    v_res_8512_ =
        l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_close___redArg(v_ch_8510_);
    return v_res_8512_;
}
pub unsafe fn l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_close(
    mut v_00_u03b1_8513_: *mut LeanObject,
    mut v_ch_8514_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_8516_: *mut LeanObject = core::ptr::null_mut();
    v___x_8516_ =
        l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_close___redArg(v_ch_8514_);
    return v___x_8516_;
}
pub unsafe fn l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_close___boxed(
    mut v_00_u03b1_8517_: *mut LeanObject,
    mut v_ch_8518_: *mut LeanObject,
    mut v_a_8519_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_8520_: *mut LeanObject = core::ptr::null_mut();
    v_res_8520_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_close(
        v_00_u03b1_8517_,
        v_ch_8518_,
    );
    return v_res_8520_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_close_spec__0(
    mut v_00_u03b1_8521_: *mut LeanObject,
    mut v___x_8522_: u8,
    mut v_as_8523_: *mut LeanObject,
    mut v_sz_8524_: usize,
    mut v_i_8525_: usize,
    mut v_b_8526_: *mut LeanObject,
    mut v___y_8527_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_8529_: *mut LeanObject = core::ptr::null_mut();
    v___x_8529_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_close_spec__0___redArg(v___x_8522_, v_as_8523_, v_sz_8524_, v_i_8525_, v_b_8526_);
    return v___x_8529_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_close_spec__0___boxed(
    mut v_00_u03b1_8530_: *mut LeanObject,
    mut v___x_8531_: *mut LeanObject,
    mut v_as_8532_: *mut LeanObject,
    mut v_sz_8533_: *mut LeanObject,
    mut v_i_8534_: *mut LeanObject,
    mut v_b_8535_: *mut LeanObject,
    mut v___y_8536_: *mut LeanObject,
    mut v___y_8537_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1234__boxed_8538_: u8 = 0;
    let mut v_sz_boxed_8539_: usize = 0;
    let mut v_i_boxed_8540_: usize = 0;
    let mut v_res_8541_: *mut LeanObject = core::ptr::null_mut();
    v___x_1234__boxed_8538_ = (lean_unbox(v___x_8531_) as u8);
    v_sz_boxed_8539_ = lean_unbox_usize(v_sz_8533_);
    lean_dec(v_sz_8533_);
    v_i_boxed_8540_ = lean_unbox_usize(v_i_8534_);
    lean_dec(v_i_8534_);
    v_res_8541_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_close_spec__0(v_00_u03b1_8530_, v___x_1234__boxed_8538_, v_as_8532_, v_sz_boxed_8539_, v_i_boxed_8540_, v_b_8535_, v___y_8536_);
    lean_dec(v___y_8536_);
    lean_dec_ref(v_as_8532_);
    return v_res_8541_;
}
pub unsafe fn l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_isClosed___redArg___lam__0(
    mut v___y_8542_: *mut LeanObject,
) -> u8 {
    let mut v___x_8544_: *mut LeanObject = core::ptr::null_mut();
    let mut v_closed_8545_: u8 = 0;
    v___x_8544_ = lean_st_ref_get(v___y_8542_);
    v_closed_8545_ = lean_ctor_get_uint8(
        v___x_8544_,
        (core::mem::size_of::<*mut LeanObject>() * 7) as u32,
    );
    lean_dec(v___x_8544_);
    return v_closed_8545_;
}
pub unsafe fn l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_isClosed___redArg___lam__0___boxed(
    mut v___y_8546_: *mut LeanObject,
    mut v___y_8547_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_8548_: u8 = 0;
    let mut v_r_8549_: *mut LeanObject = core::ptr::null_mut();
    v_res_8548_ =
        l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_isClosed___redArg___lam__0(
            v___y_8546_,
        );
    lean_dec(v___y_8546_);
    v_r_8549_ = lean_box((v_res_8548_) as usize);
    return v_r_8549_;
}
pub unsafe fn l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_isClosed___redArg(
    mut v_ch_8551_: *mut LeanObject,
) -> u8 {
    let mut v___f_8553_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8554_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8555_: u8 = 0;
    v___f_8553_ =
        l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_isClosed___redArg___closed__0;
    v___x_8554_ = l_Std_Mutex_atomically___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_trySend_spec__1___redArg(v_ch_8551_, v___f_8553_);
    v___x_8555_ = (lean_unbox(v___x_8554_) as u8);
    lean_dec(v___x_8554_);
    return v___x_8555_;
}
pub unsafe fn l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_isClosed___redArg___boxed(
    mut v_ch_8556_: *mut LeanObject,
    mut v_a_8557_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_8558_: u8 = 0;
    let mut v_r_8559_: *mut LeanObject = core::ptr::null_mut();
    v_res_8558_ =
        l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_isClosed___redArg(v_ch_8556_);
    v_r_8559_ = lean_box((v_res_8558_) as usize);
    return v_r_8559_;
}
pub unsafe fn l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_isClosed(
    mut v_00_u03b1_8560_: *mut LeanObject,
    mut v_ch_8561_: *mut LeanObject,
) -> u8 {
    let mut v___x_8563_: u8 = 0;
    v___x_8563_ =
        l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_isClosed___redArg(v_ch_8561_);
    return v___x_8563_;
}
pub unsafe fn l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_isClosed___boxed(
    mut v_00_u03b1_8564_: *mut LeanObject,
    mut v_ch_8565_: *mut LeanObject,
    mut v_a_8566_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_8567_: u8 = 0;
    let mut v_r_8568_: *mut LeanObject = core::ptr::null_mut();
    v_res_8567_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_isClosed(
        v_00_u03b1_8564_,
        v_ch_8565_,
    );
    v_r_8568_ = lean_box((v_res_8567_) as usize);
    return v_r_8568_;
}
pub unsafe fn l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27___redArg___lam__0(
    mut v_toApplicative_8569_: *mut LeanObject,
    mut v_a_8570_: *mut LeanObject,
    mut v_a_8571_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toPure_8572_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8573_: *mut LeanObject = core::ptr::null_mut();
    v_toPure_8572_ = lean_ctor_get(v_toApplicative_8569_, 1);
    lean_inc(v_toPure_8572_);
    lean_dec_ref(v_toApplicative_8569_);
    v___x_8573_ = lean_apply_2(v_toPure_8572_, lean_box(0), v_a_8570_);
    return v___x_8573_;
}
pub unsafe fn l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27___redArg___lam__1(
    mut v_inst_8574_: *mut LeanObject,
    mut v_toBind_8575_: *mut LeanObject,
    mut v___f_8576_: *mut LeanObject,
    mut v_____r_8577_: *mut LeanObject,
    mut v_st_8578_: *mut LeanObject,
    mut v___y_8579_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_8580_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8581_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8582_: *mut LeanObject = core::ptr::null_mut();
    lean_inc(v___y_8579_);
    v___x_8580_ = lean_alloc_closure(l_ST_Prim_Ref_set___boxed as *mut core::ffi::c_void, 5, 4);
    lean_closure_set(v___x_8580_, 0, lean_box(0));
    lean_closure_set(v___x_8580_, 1, lean_box(0));
    lean_closure_set(v___x_8580_, 2, v___y_8579_);
    lean_closure_set(v___x_8580_, 3, v_st_8578_);
    v___x_8581_ = lean_apply_2(v_inst_8574_, lean_box(0), v___x_8580_);
    v___x_8582_ = lean_apply_4(
        v_toBind_8575_,
        lean_box(0),
        lean_box(0),
        v___x_8581_,
        v___f_8576_,
    );
    return v___x_8582_;
}
pub unsafe fn l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27___redArg___lam__1___boxed(
    mut v_inst_8583_: *mut LeanObject,
    mut v_toBind_8584_: *mut LeanObject,
    mut v___f_8585_: *mut LeanObject,
    mut v_____r_8586_: *mut LeanObject,
    mut v_st_8587_: *mut LeanObject,
    mut v___y_8588_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_8589_: *mut LeanObject = core::ptr::null_mut();
    v_res_8589_ =
        l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27___redArg___lam__1(
            v_inst_8583_,
            v_toBind_8584_,
            v___f_8585_,
            v_____r_8586_,
            v_st_8587_,
            v___y_8588_,
        );
    lean_dec(v___y_8588_);
    return v_res_8589_;
}
pub unsafe fn l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27___redArg___lam__2(
    mut v_snd_8590_: *mut LeanObject,
    mut v_consumers_8591_: *mut LeanObject,
    mut v_capacity_8592_: *mut LeanObject,
    mut v_buf_8593_: *mut LeanObject,
    mut v___x_8594_: *mut LeanObject,
    mut v_sendIdx_8595_: *mut LeanObject,
    mut v___y_8596_: *mut LeanObject,
    mut v_closed_8597_: u8,
    mut v___f_8598_: *mut LeanObject,
    mut v_a_8599_: *mut LeanObject,
    mut v_a_8600_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_8601_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8602_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8603_: *mut LeanObject = core::ptr::null_mut();
    v___x_8601_ = lean_alloc_ctor(0, 7, (1) as u32);
    lean_ctor_set(v___x_8601_, 0, v_snd_8590_);
    lean_ctor_set(v___x_8601_, 1, v_consumers_8591_);
    lean_ctor_set(v___x_8601_, 2, v_capacity_8592_);
    lean_ctor_set(v___x_8601_, 3, v_buf_8593_);
    lean_ctor_set(v___x_8601_, 4, v___x_8594_);
    lean_ctor_set(v___x_8601_, 5, v_sendIdx_8595_);
    lean_ctor_set(v___x_8601_, 6, v___y_8596_);
    lean_ctor_set_uint8(
        v___x_8601_,
        (core::mem::size_of::<*mut LeanObject>() * 7) as u32,
        v_closed_8597_,
    );
    v___x_8602_ = lean_box(0);
    lean_inc(v_a_8599_);
    v___x_8603_ = lean_apply_3(v___f_8598_, v___x_8602_, v___x_8601_, v_a_8599_);
    return v___x_8603_;
}
pub unsafe fn l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27___redArg___lam__2___boxed(
    mut v_snd_8604_: *mut LeanObject,
    mut v_consumers_8605_: *mut LeanObject,
    mut v_capacity_8606_: *mut LeanObject,
    mut v_buf_8607_: *mut LeanObject,
    mut v___x_8608_: *mut LeanObject,
    mut v_sendIdx_8609_: *mut LeanObject,
    mut v___y_8610_: *mut LeanObject,
    mut v_closed_8611_: *mut LeanObject,
    mut v___f_8612_: *mut LeanObject,
    mut v_a_8613_: *mut LeanObject,
    mut v_a_8614_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_closed_boxed_8615_: u8 = 0;
    let mut v_res_8616_: *mut LeanObject = core::ptr::null_mut();
    v_closed_boxed_8615_ = (lean_unbox(v_closed_8611_) as u8);
    v_res_8616_ =
        l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27___redArg___lam__2(
            v_snd_8604_,
            v_consumers_8605_,
            v_capacity_8606_,
            v_buf_8607_,
            v___x_8608_,
            v_sendIdx_8609_,
            v___y_8610_,
            v_closed_boxed_8615_,
            v___f_8612_,
            v_a_8613_,
            v_a_8614_,
        );
    lean_dec(v_a_8613_);
    return v_res_8616_;
}
pub unsafe fn l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27___redArg___lam__3(
    mut v_toApplicative_8617_: *mut LeanObject,
    mut v_inst_8618_: *mut LeanObject,
    mut v_toBind_8619_: *mut LeanObject,
    mut v_bufCount_8620_: *mut LeanObject,
    mut v_producers_8621_: *mut LeanObject,
    mut v_consumers_8622_: *mut LeanObject,
    mut v_capacity_8623_: *mut LeanObject,
    mut v_buf_8624_: *mut LeanObject,
    mut v_sendIdx_8625_: *mut LeanObject,
    mut v_closed_8626_: u8,
    mut v_a_8627_: *mut LeanObject,
    mut v___x_8628_: u8,
    mut v_inst_8629_: *mut LeanObject,
    mut v_recvIdx_8630_: *mut LeanObject,
    mut v___x_8631_: *mut LeanObject,
    mut v_a_8632_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_8633_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_8634_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_8636_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8637_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8638_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8639_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8640_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_8641_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_8642_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_8643_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8644_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_8645_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8646_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8647_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8648_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8649_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8650_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8651_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8652_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8653_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8654_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___f_8633_ = lean_alloc_closure(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27___redArg___lam__0 as *mut core::ffi::c_void, 3, 2);
                lean_closure_set(v___f_8633_, 0, v_toApplicative_8617_);
                lean_closure_set(v___f_8633_, 1, v_a_8632_);
                lean_inc_ref(v___f_8633_);
                lean_inc(v_toBind_8619_);
                lean_inc(v_inst_8618_);
                v___f_8634_ = lean_alloc_closure(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27___redArg___lam__1___boxed as *mut core::ffi::c_void, 6, 3);
                lean_closure_set(v___f_8634_, 0, v_inst_8618_);
                lean_closure_set(v___f_8634_, 1, v_toBind_8619_);
                lean_closure_set(v___f_8634_, 2, v___f_8633_);
                v___x_8652_ = lean_unsigned_to_nat(1);
                v___x_8653_ = lean_nat_add(v_recvIdx_8630_, v___x_8652_);
                v___x_8654_ = lean_nat_dec_eq(v___x_8653_, v_capacity_8623_);
                if v___x_8654_ == 0 {
                    lean_dec(v___x_8631_);
                    v___y_8636_ = v___x_8653_;
                    state = 1;
                    continue;
                } else {
                    lean_dec(v___x_8653_);
                    v___y_8636_ = v___x_8631_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_8637_ = lean_unsigned_to_nat(1);
                v___x_8638_ = lean_nat_sub(v_bufCount_8620_, v___x_8637_);
                lean_inc(v___y_8636_);
                lean_inc(v_sendIdx_8625_);
                lean_inc(v___x_8638_);
                lean_inc_ref(v_buf_8624_);
                lean_inc(v_capacity_8623_);
                lean_inc_ref(v_consumers_8622_);
                lean_inc_ref(v_producers_8621_);
                v___x_8639_ = lean_alloc_ctor(0, 7, (1) as u32);
                lean_ctor_set(v___x_8639_, 0, v_producers_8621_);
                lean_ctor_set(v___x_8639_, 1, v_consumers_8622_);
                lean_ctor_set(v___x_8639_, 2, v_capacity_8623_);
                lean_ctor_set(v___x_8639_, 3, v_buf_8624_);
                lean_ctor_set(v___x_8639_, 4, v___x_8638_);
                lean_ctor_set(v___x_8639_, 5, v_sendIdx_8625_);
                lean_ctor_set(v___x_8639_, 6, v___y_8636_);
                lean_ctor_set_uint8(
                    v___x_8639_,
                    (core::mem::size_of::<*mut LeanObject>() * 7) as u32,
                    v_closed_8626_,
                );
                v___x_8640_ = l_Std_Queue_dequeue_x3f___redArg(v_producers_8621_);
                if lean_obj_tag(v___x_8640_) == 1 {
                    lean_dec_ref_known(v___x_8639_, 7);
                    lean_dec_ref(v___f_8633_);
                    lean_dec(v_inst_8618_);
                    v_val_8641_ = lean_ctor_get(v___x_8640_, 0);
                    lean_inc(v_val_8641_);
                    lean_dec_ref_known(v___x_8640_, 1);
                    v_fst_8642_ = lean_ctor_get(v_val_8641_, 0);
                    lean_inc(v_fst_8642_);
                    v_snd_8643_ = lean_ctor_get(v_val_8641_, 1);
                    lean_inc(v_snd_8643_);
                    lean_dec(v_val_8641_);
                    v___x_8644_ = lean_box((v_closed_8626_) as usize);
                    lean_inc(v_a_8627_);
                    v___f_8645_ = lean_alloc_closure(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27___redArg___lam__2___boxed as *mut core::ffi::c_void, 11, 10);
                    lean_closure_set(v___f_8645_, 0, v_snd_8643_);
                    lean_closure_set(v___f_8645_, 1, v_consumers_8622_);
                    lean_closure_set(v___f_8645_, 2, v_capacity_8623_);
                    lean_closure_set(v___f_8645_, 3, v_buf_8624_);
                    lean_closure_set(v___f_8645_, 4, v___x_8638_);
                    lean_closure_set(v___f_8645_, 5, v_sendIdx_8625_);
                    lean_closure_set(v___f_8645_, 6, v___y_8636_);
                    lean_closure_set(v___f_8645_, 7, v___x_8644_);
                    lean_closure_set(v___f_8645_, 8, v___f_8634_);
                    lean_closure_set(v___f_8645_, 9, v_a_8627_);
                    v___x_8646_ = lean_box((v___x_8628_) as usize);
                    v___x_8647_ = lean_alloc_closure(
                        l_IO_Promise_resolve___boxed as *mut core::ffi::c_void,
                        4,
                        3,
                    );
                    lean_closure_set(v___x_8647_, 0, lean_box(0));
                    lean_closure_set(v___x_8647_, 1, v___x_8646_);
                    lean_closure_set(v___x_8647_, 2, v_fst_8642_);
                    v___x_8648_ = lean_apply_2(v_inst_8629_, lean_box(0), v___x_8647_);
                    v___x_8649_ = lean_apply_4(
                        v_toBind_8619_,
                        lean_box(0),
                        lean_box(0),
                        v___x_8648_,
                        v___f_8645_,
                    );
                    return v___x_8649_;
                } else {
                    lean_dec(v___x_8640_);
                    lean_dec(v___x_8638_);
                    lean_dec(v___y_8636_);
                    lean_dec_ref(v___f_8634_);
                    lean_dec(v_inst_8629_);
                    lean_dec(v_sendIdx_8625_);
                    lean_dec_ref(v_buf_8624_);
                    lean_dec(v_capacity_8623_);
                    lean_dec_ref(v_consumers_8622_);
                    v___x_8650_ = lean_box(0);
                    v___x_8651_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27___redArg___lam__1(v_inst_8618_, v_toBind_8619_, v___f_8633_, v___x_8650_, v___x_8639_, v_a_8627_);
                    return v___x_8651_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27___redArg___lam__3___boxed(
    mut v_toApplicative_8655_: *mut LeanObject,
    mut v_inst_8656_: *mut LeanObject,
    mut v_toBind_8657_: *mut LeanObject,
    mut v_bufCount_8658_: *mut LeanObject,
    mut v_producers_8659_: *mut LeanObject,
    mut v_consumers_8660_: *mut LeanObject,
    mut v_capacity_8661_: *mut LeanObject,
    mut v_buf_8662_: *mut LeanObject,
    mut v_sendIdx_8663_: *mut LeanObject,
    mut v_closed_8664_: *mut LeanObject,
    mut v_a_8665_: *mut LeanObject,
    mut v___x_8666_: *mut LeanObject,
    mut v_inst_8667_: *mut LeanObject,
    mut v_recvIdx_8668_: *mut LeanObject,
    mut v___x_8669_: *mut LeanObject,
    mut v_a_8670_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_closed_boxed_8671_: u8 = 0;
    let mut v___x_679__boxed_8672_: u8 = 0;
    let mut v_res_8673_: *mut LeanObject = core::ptr::null_mut();
    v_closed_boxed_8671_ = (lean_unbox(v_closed_8664_) as u8);
    v___x_679__boxed_8672_ = (lean_unbox(v___x_8666_) as u8);
    v_res_8673_ =
        l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27___redArg___lam__3(
            v_toApplicative_8655_,
            v_inst_8656_,
            v_toBind_8657_,
            v_bufCount_8658_,
            v_producers_8659_,
            v_consumers_8660_,
            v_capacity_8661_,
            v_buf_8662_,
            v_sendIdx_8663_,
            v_closed_boxed_8671_,
            v_a_8665_,
            v___x_679__boxed_8672_,
            v_inst_8667_,
            v_recvIdx_8668_,
            v___x_8669_,
            v_a_8670_,
        );
    lean_dec(v_recvIdx_8668_);
    lean_dec(v_a_8665_);
    lean_dec(v_bufCount_8658_);
    return v_res_8673_;
}
pub unsafe fn l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27___redArg___lam__4(
    mut v_toApplicative_8674_: *mut LeanObject,
    mut v_inst_8675_: *mut LeanObject,
    mut v_toBind_8676_: *mut LeanObject,
    mut v_a_8677_: *mut LeanObject,
    mut v_inst_8678_: *mut LeanObject,
    mut v_a_8679_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_producers_8680_: *mut LeanObject = core::ptr::null_mut();
    let mut v_consumers_8681_: *mut LeanObject = core::ptr::null_mut();
    let mut v_capacity_8682_: *mut LeanObject = core::ptr::null_mut();
    let mut v_buf_8683_: *mut LeanObject = core::ptr::null_mut();
    let mut v_bufCount_8684_: *mut LeanObject = core::ptr::null_mut();
    let mut v_sendIdx_8685_: *mut LeanObject = core::ptr::null_mut();
    let mut v_recvIdx_8686_: *mut LeanObject = core::ptr::null_mut();
    let mut v_closed_8687_: u8 = 0;
    let mut v___x_8688_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8689_: u8 = 0;
    v_producers_8680_ = lean_ctor_get(v_a_8679_, 0);
    lean_inc_ref(v_producers_8680_);
    v_consumers_8681_ = lean_ctor_get(v_a_8679_, 1);
    lean_inc_ref(v_consumers_8681_);
    v_capacity_8682_ = lean_ctor_get(v_a_8679_, 2);
    lean_inc(v_capacity_8682_);
    v_buf_8683_ = lean_ctor_get(v_a_8679_, 3);
    lean_inc_ref(v_buf_8683_);
    v_bufCount_8684_ = lean_ctor_get(v_a_8679_, 4);
    lean_inc(v_bufCount_8684_);
    v_sendIdx_8685_ = lean_ctor_get(v_a_8679_, 5);
    lean_inc(v_sendIdx_8685_);
    v_recvIdx_8686_ = lean_ctor_get(v_a_8679_, 6);
    lean_inc(v_recvIdx_8686_);
    v_closed_8687_ = lean_ctor_get_uint8(
        v_a_8679_,
        (core::mem::size_of::<*mut LeanObject>() * 7) as u32,
    );
    lean_dec_ref(v_a_8679_);
    v___x_8688_ = lean_unsigned_to_nat(0);
    v___x_8689_ = lean_nat_dec_eq(v_bufCount_8684_, v___x_8688_);
    if v___x_8689_ == 0 {
        let mut v___x_8690_: u8 = 0;
        let mut v___x_8691_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_8692_: *mut LeanObject = core::ptr::null_mut();
        let mut v___f_8693_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_8694_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_8695_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_8696_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_8697_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_8698_: *mut LeanObject = core::ptr::null_mut();
        v___x_8690_ = 1;
        v___x_8691_ = lean_box((v_closed_8687_) as usize);
        v___x_8692_ = lean_box((v___x_8690_) as usize);
        lean_inc(v_recvIdx_8686_);
        lean_inc(v_a_8677_);
        lean_inc_ref(v_buf_8683_);
        lean_inc(v_toBind_8676_);
        lean_inc(v_inst_8675_);
        v___f_8693_ = lean_alloc_closure(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27___redArg___lam__3___boxed as *mut core::ffi::c_void, 16, 15);
        lean_closure_set(v___f_8693_, 0, v_toApplicative_8674_);
        lean_closure_set(v___f_8693_, 1, v_inst_8675_);
        lean_closure_set(v___f_8693_, 2, v_toBind_8676_);
        lean_closure_set(v___f_8693_, 3, v_bufCount_8684_);
        lean_closure_set(v___f_8693_, 4, v_producers_8680_);
        lean_closure_set(v___f_8693_, 5, v_consumers_8681_);
        lean_closure_set(v___f_8693_, 6, v_capacity_8682_);
        lean_closure_set(v___f_8693_, 7, v_buf_8683_);
        lean_closure_set(v___f_8693_, 8, v_sendIdx_8685_);
        lean_closure_set(v___f_8693_, 9, v___x_8691_);
        lean_closure_set(v___f_8693_, 10, v_a_8677_);
        lean_closure_set(v___f_8693_, 11, v___x_8692_);
        lean_closure_set(v___f_8693_, 12, v_inst_8678_);
        lean_closure_set(v___f_8693_, 13, v_recvIdx_8686_);
        lean_closure_set(v___f_8693_, 14, v___x_8688_);
        v___x_8694_ = lean_array_fget(v_buf_8683_, v_recvIdx_8686_);
        lean_dec(v_recvIdx_8686_);
        lean_dec_ref(v_buf_8683_);
        v___x_8695_ = lean_box(0);
        v___x_8696_ =
            lean_alloc_closure(l_ST_Prim_Ref_swap___boxed as *mut core::ffi::c_void, 5, 4);
        lean_closure_set(v___x_8696_, 0, lean_box(0));
        lean_closure_set(v___x_8696_, 1, lean_box(0));
        lean_closure_set(v___x_8696_, 2, v___x_8694_);
        lean_closure_set(v___x_8696_, 3, v___x_8695_);
        v___x_8697_ = lean_apply_2(v_inst_8675_, lean_box(0), v___x_8696_);
        v___x_8698_ = lean_apply_4(
            v_toBind_8676_,
            lean_box(0),
            lean_box(0),
            v___x_8697_,
            v___f_8693_,
        );
        return v___x_8698_;
    } else {
        let mut v_toPure_8699_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_8700_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_8701_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_recvIdx_8686_);
        lean_dec(v_sendIdx_8685_);
        lean_dec(v_bufCount_8684_);
        lean_dec_ref(v_buf_8683_);
        lean_dec(v_capacity_8682_);
        lean_dec_ref(v_consumers_8681_);
        lean_dec_ref(v_producers_8680_);
        lean_dec(v_inst_8678_);
        lean_dec(v_toBind_8676_);
        lean_dec(v_inst_8675_);
        v_toPure_8699_ = lean_ctor_get(v_toApplicative_8674_, 1);
        lean_inc(v_toPure_8699_);
        lean_dec_ref(v_toApplicative_8674_);
        v___x_8700_ = lean_box(0);
        v___x_8701_ = lean_apply_2(v_toPure_8699_, lean_box(0), v___x_8700_);
        return v___x_8701_;
    }
}
pub unsafe fn l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27___redArg___lam__4___boxed(
    mut v_toApplicative_8702_: *mut LeanObject,
    mut v_inst_8703_: *mut LeanObject,
    mut v_toBind_8704_: *mut LeanObject,
    mut v_a_8705_: *mut LeanObject,
    mut v_inst_8706_: *mut LeanObject,
    mut v_a_8707_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_8708_: *mut LeanObject = core::ptr::null_mut();
    v_res_8708_ =
        l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27___redArg___lam__4(
            v_toApplicative_8702_,
            v_inst_8703_,
            v_toBind_8704_,
            v_a_8705_,
            v_inst_8706_,
            v_a_8707_,
        );
    lean_dec(v_a_8705_);
    return v_res_8708_;
}
pub unsafe fn l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27___redArg(
    mut v_inst_8709_: *mut LeanObject,
    mut v_inst_8710_: *mut LeanObject,
    mut v_inst_8711_: *mut LeanObject,
    mut v_a_8712_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toApplicative_8713_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toBind_8714_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_8715_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8716_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8717_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8718_: *mut LeanObject = core::ptr::null_mut();
    v_toApplicative_8713_ = lean_ctor_get(v_inst_8709_, 0);
    lean_inc_ref(v_toApplicative_8713_);
    v_toBind_8714_ = lean_ctor_get(v_inst_8709_, 1);
    lean_inc_n(v_toBind_8714_, 2);
    lean_dec_ref(v_inst_8709_);
    lean_inc_n(v_a_8712_, 2);
    lean_inc(v_inst_8710_);
    v___f_8715_ = lean_alloc_closure(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27___redArg___lam__4___boxed as *mut core::ffi::c_void, 6, 5);
    lean_closure_set(v___f_8715_, 0, v_toApplicative_8713_);
    lean_closure_set(v___f_8715_, 1, v_inst_8710_);
    lean_closure_set(v___f_8715_, 2, v_toBind_8714_);
    lean_closure_set(v___f_8715_, 3, v_a_8712_);
    lean_closure_set(v___f_8715_, 4, v_inst_8711_);
    v___x_8716_ = lean_alloc_closure(l_ST_Prim_Ref_get___boxed as *mut core::ffi::c_void, 4, 3);
    lean_closure_set(v___x_8716_, 0, lean_box(0));
    lean_closure_set(v___x_8716_, 1, lean_box(0));
    lean_closure_set(v___x_8716_, 2, v_a_8712_);
    v___x_8717_ = lean_apply_2(v_inst_8710_, lean_box(0), v___x_8716_);
    v___x_8718_ = lean_apply_4(
        v_toBind_8714_,
        lean_box(0),
        lean_box(0),
        v___x_8717_,
        v___f_8715_,
    );
    return v___x_8718_;
}
pub unsafe fn l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27___redArg___boxed(
    mut v_inst_8719_: *mut LeanObject,
    mut v_inst_8720_: *mut LeanObject,
    mut v_inst_8721_: *mut LeanObject,
    mut v_a_8722_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_8723_: *mut LeanObject = core::ptr::null_mut();
    v_res_8723_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27___redArg(
        v_inst_8719_,
        v_inst_8720_,
        v_inst_8721_,
        v_a_8722_,
    );
    lean_dec(v_a_8722_);
    return v_res_8723_;
}
pub unsafe fn l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27(
    mut v_m_8724_: *mut LeanObject,
    mut v_00_u03b1_8725_: *mut LeanObject,
    mut v_inst_8726_: *mut LeanObject,
    mut v_inst_8727_: *mut LeanObject,
    mut v_inst_8728_: *mut LeanObject,
    mut v_a_8729_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_8730_: *mut LeanObject = core::ptr::null_mut();
    v___x_8730_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27___redArg(
        v_inst_8726_,
        v_inst_8727_,
        v_inst_8728_,
        v_a_8729_,
    );
    return v___x_8730_;
}
pub unsafe fn l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27___boxed(
    mut v_m_8731_: *mut LeanObject,
    mut v_00_u03b1_8732_: *mut LeanObject,
    mut v_inst_8733_: *mut LeanObject,
    mut v_inst_8734_: *mut LeanObject,
    mut v_inst_8735_: *mut LeanObject,
    mut v_a_8736_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_8737_: *mut LeanObject = core::ptr::null_mut();
    v_res_8737_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27(
        v_m_8731_,
        v_00_u03b1_8732_,
        v_inst_8733_,
        v_inst_8734_,
        v_inst_8735_,
        v_a_8736_,
    );
    lean_dec(v_a_8736_);
    return v_res_8737_;
}
pub unsafe fn l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_spec__0___redArg(
    mut v_a_8738_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_8740_: *mut LeanObject = core::ptr::null_mut();
    let mut v_producers_8741_: *mut LeanObject = core::ptr::null_mut();
    let mut v_consumers_8742_: *mut LeanObject = core::ptr::null_mut();
    let mut v_capacity_8743_: *mut LeanObject = core::ptr::null_mut();
    let mut v_buf_8744_: *mut LeanObject = core::ptr::null_mut();
    let mut v_bufCount_8745_: *mut LeanObject = core::ptr::null_mut();
    let mut v_sendIdx_8746_: *mut LeanObject = core::ptr::null_mut();
    let mut v_recvIdx_8747_: *mut LeanObject = core::ptr::null_mut();
    let mut v_closed_8748_: u8 = 0;
    let mut v___x_8750_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_8751_: u8 = 0;
    let mut v___x_8752_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8753_: u8 = 0;
    let mut v___x_8754_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8755_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8756_: *mut LeanObject = core::ptr::null_mut();
    let mut v_st_8758_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_8759_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8760_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8761_: u8 = 0;
    let mut v___y_8763_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8764_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8765_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8767_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8768_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_8769_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_8770_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_8771_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8772_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8773_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8774_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8775_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8776_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8777_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8778_: u8 = 0;
    let mut v___x_8779_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_8780_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_8740_ = lean_st_ref_get(v_a_8738_);
                v_producers_8741_ = lean_ctor_get(v___x_8740_, 0);
                v_consumers_8742_ = lean_ctor_get(v___x_8740_, 1);
                v_capacity_8743_ = lean_ctor_get(v___x_8740_, 2);
                v_buf_8744_ = lean_ctor_get(v___x_8740_, 3);
                v_bufCount_8745_ = lean_ctor_get(v___x_8740_, 4);
                v_sendIdx_8746_ = lean_ctor_get(v___x_8740_, 5);
                v_recvIdx_8747_ = lean_ctor_get(v___x_8740_, 6);
                v_closed_8748_ = lean_ctor_get_uint8(
                    v___x_8740_,
                    (core::mem::size_of::<*mut LeanObject>() * 7) as u32,
                );
                v_isSharedCheck_8780_ = (!lean_is_exclusive(v___x_8740_)) as u8;
                if v_isSharedCheck_8780_ == 0 {
                    v___x_8750_ = v___x_8740_;
                    v_isShared_8751_ = v_isSharedCheck_8780_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_recvIdx_8747_);
                    lean_inc(v_sendIdx_8746_);
                    lean_inc(v_bufCount_8745_);
                    lean_inc(v_buf_8744_);
                    lean_inc(v_capacity_8743_);
                    lean_inc(v_consumers_8742_);
                    lean_inc(v_producers_8741_);
                    lean_dec(v___x_8740_);
                    v___x_8750_ = lean_box(0);
                    v_isShared_8751_ = v_isSharedCheck_8780_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_8752_ = lean_unsigned_to_nat(0);
                v___x_8753_ = lean_nat_dec_eq(v_bufCount_8745_, v___x_8752_);
                if v___x_8753_ == 0 {
                    v___x_8754_ = lean_array_fget_borrowed(v_buf_8744_, v_recvIdx_8747_);
                    v___x_8755_ = lean_box(0);
                    v___x_8756_ = lean_st_ref_swap(v___x_8754_, v___x_8755_);
                    v___x_8761_ = 1;
                    v___x_8776_ = lean_unsigned_to_nat(1);
                    v___x_8777_ = lean_nat_add(v_recvIdx_8747_, v___x_8776_);
                    lean_dec(v_recvIdx_8747_);
                    v___x_8778_ = lean_nat_dec_eq(v___x_8777_, v_capacity_8743_);
                    if v___x_8778_ == 0 {
                        v___y_8763_ = v___x_8777_;
                        state = 3;
                        continue;
                    } else {
                        lean_dec(v___x_8777_);
                        v___y_8763_ = v___x_8752_;
                        state = 3;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_8750_);
                    lean_dec(v_recvIdx_8747_);
                    lean_dec(v_sendIdx_8746_);
                    lean_dec(v_bufCount_8745_);
                    lean_dec_ref(v_buf_8744_);
                    lean_dec(v_capacity_8743_);
                    lean_dec_ref(v_consumers_8742_);
                    lean_dec_ref(v_producers_8741_);
                    v___x_8779_ = lean_box(0);
                    return v___x_8779_;
                }
            }
            2 => {
                v___x_8760_ = lean_st_ref_set(v___y_8759_, v_st_8758_);
                return v___x_8756_;
            }
            3 => {
                v___x_8764_ = lean_unsigned_to_nat(1);
                v___x_8765_ = lean_nat_sub(v_bufCount_8745_, v___x_8764_);
                lean_dec(v_bufCount_8745_);
                lean_inc(v___y_8763_);
                lean_inc(v_sendIdx_8746_);
                lean_inc(v___x_8765_);
                lean_inc_ref(v_buf_8744_);
                lean_inc(v_capacity_8743_);
                lean_inc_ref(v_consumers_8742_);
                lean_inc_ref(v_producers_8741_);
                if v_isShared_8751_ == 0 {
                    lean_ctor_set(v___x_8750_, 6, v___y_8763_);
                    lean_ctor_set(v___x_8750_, 4, v___x_8765_);
                    v___x_8767_ = v___x_8750_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_8775_ = lean_alloc_ctor(0, 7, (1) as u32);
                    lean_ctor_set(v_reuseFailAlloc_8775_, 0, v_producers_8741_);
                    lean_ctor_set(v_reuseFailAlloc_8775_, 1, v_consumers_8742_);
                    lean_ctor_set(v_reuseFailAlloc_8775_, 2, v_capacity_8743_);
                    lean_ctor_set(v_reuseFailAlloc_8775_, 3, v_buf_8744_);
                    lean_ctor_set(v_reuseFailAlloc_8775_, 4, v___x_8765_);
                    lean_ctor_set(v_reuseFailAlloc_8775_, 5, v_sendIdx_8746_);
                    lean_ctor_set(v_reuseFailAlloc_8775_, 6, v___y_8763_);
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_8775_,
                        (core::mem::size_of::<*mut LeanObject>() * 7) as u32,
                        v_closed_8748_,
                    );
                    v___x_8767_ = v_reuseFailAlloc_8775_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_8768_ = l_Std_Queue_dequeue_x3f___redArg(v_producers_8741_);
                if lean_obj_tag(v___x_8768_) == 1 {
                    lean_dec_ref(v___x_8767_);
                    v_val_8769_ = lean_ctor_get(v___x_8768_, 0);
                    lean_inc(v_val_8769_);
                    lean_dec_ref_known(v___x_8768_, 1);
                    v_fst_8770_ = lean_ctor_get(v_val_8769_, 0);
                    lean_inc(v_fst_8770_);
                    v_snd_8771_ = lean_ctor_get(v_val_8769_, 1);
                    lean_inc(v_snd_8771_);
                    lean_dec(v_val_8769_);
                    v___x_8772_ = lean_box((v___x_8761_) as usize);
                    v___x_8773_ = lean_io_promise_resolve(v___x_8772_, v_fst_8770_);
                    lean_dec(v_fst_8770_);
                    v___x_8774_ = lean_alloc_ctor(0, 7, (1) as u32);
                    lean_ctor_set(v___x_8774_, 0, v_snd_8771_);
                    lean_ctor_set(v___x_8774_, 1, v_consumers_8742_);
                    lean_ctor_set(v___x_8774_, 2, v_capacity_8743_);
                    lean_ctor_set(v___x_8774_, 3, v_buf_8744_);
                    lean_ctor_set(v___x_8774_, 4, v___x_8765_);
                    lean_ctor_set(v___x_8774_, 5, v_sendIdx_8746_);
                    lean_ctor_set(v___x_8774_, 6, v___y_8763_);
                    lean_ctor_set_uint8(
                        v___x_8774_,
                        (core::mem::size_of::<*mut LeanObject>() * 7) as u32,
                        v_closed_8748_,
                    );
                    v_st_8758_ = v___x_8774_;
                    v___y_8759_ = v_a_8738_;
                    state = 2;
                    continue;
                } else {
                    lean_dec(v___x_8768_);
                    lean_dec(v___x_8765_);
                    lean_dec(v___y_8763_);
                    lean_dec(v_sendIdx_8746_);
                    lean_dec_ref(v_buf_8744_);
                    lean_dec(v_capacity_8743_);
                    lean_dec_ref(v_consumers_8742_);
                    v_st_8758_ = v___x_8767_;
                    v___y_8759_ = v_a_8738_;
                    state = 2;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_spec__0___redArg___boxed(
    mut v_a_8781_: *mut LeanObject,
    mut v___y_8782_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_8783_: *mut LeanObject = core::ptr::null_mut();
    v_res_8783_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_spec__0___redArg(v_a_8781_);
    lean_dec(v_a_8781_);
    return v_res_8783_;
}
pub unsafe fn l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_spec__0(
    mut v_00_u03b1_8784_: *mut LeanObject,
    mut v_a_8785_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_8787_: *mut LeanObject = core::ptr::null_mut();
    v___x_8787_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_spec__0___redArg(v_a_8785_);
    return v___x_8787_;
}
pub unsafe fn l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_spec__0___boxed(
    mut v_00_u03b1_8788_: *mut LeanObject,
    mut v_a_8789_: *mut LeanObject,
    mut v___y_8790_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_8791_: *mut LeanObject = core::ptr::null_mut();
    v_res_8791_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_spec__0(v_00_u03b1_8788_, v_a_8789_);
    lean_dec(v_a_8789_);
    return v_res_8791_;
}
pub unsafe fn l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv___redArg(
    mut v_ch_8793_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_8795_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8796_: *mut LeanObject = core::ptr::null_mut();
    v___f_8795_ =
        l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv___redArg___closed__0;
    v___x_8796_ = l_Std_Mutex_atomically___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_trySend_spec__1___redArg(v_ch_8793_, v___f_8795_);
    return v___x_8796_;
}
pub unsafe fn l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv___redArg___boxed(
    mut v_ch_8797_: *mut LeanObject,
    mut v_a_8798_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_8799_: *mut LeanObject = core::ptr::null_mut();
    v_res_8799_ =
        l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv___redArg(v_ch_8797_);
    return v_res_8799_;
}
pub unsafe fn l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv(
    mut v_00_u03b1_8800_: *mut LeanObject,
    mut v_ch_8801_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_8803_: *mut LeanObject = core::ptr::null_mut();
    v___x_8803_ =
        l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv___redArg(v_ch_8801_);
    return v___x_8803_;
}
pub unsafe fn l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv___boxed(
    mut v_00_u03b1_8804_: *mut LeanObject,
    mut v_ch_8805_: *mut LeanObject,
    mut v_a_8806_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_8807_: *mut LeanObject = core::ptr::null_mut();
    v_res_8807_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv(
        v_00_u03b1_8804_,
        v_ch_8805_,
    );
    return v_res_8807_;
}
pub unsafe fn l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recv___redArg___lam__1(
    mut v___f_8808_: *mut LeanObject,
    mut v___y_8809_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_8811_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8812_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8813_: *mut LeanObject = core::ptr::null_mut();
    let mut v_closed_8814_: u8 = 0;
    let mut v___x_8815_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8816_: *mut LeanObject = core::ptr::null_mut();
    let mut v_producers_8817_: *mut LeanObject = core::ptr::null_mut();
    let mut v_consumers_8818_: *mut LeanObject = core::ptr::null_mut();
    let mut v_capacity_8819_: *mut LeanObject = core::ptr::null_mut();
    let mut v_buf_8820_: *mut LeanObject = core::ptr::null_mut();
    let mut v_bufCount_8821_: *mut LeanObject = core::ptr::null_mut();
    let mut v_sendIdx_8822_: *mut LeanObject = core::ptr::null_mut();
    let mut v_recvIdx_8823_: *mut LeanObject = core::ptr::null_mut();
    let mut v_closed_8824_: u8 = 0;
    let mut v___x_8826_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_8827_: u8 = 0;
    let mut v___x_8828_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8829_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8830_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8832_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8833_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8834_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8835_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8836_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8837_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_8838_: u8 = 0;
    let mut v___x_8839_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_8811_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_spec__0___redArg(v___y_8809_);
                if lean_obj_tag(v___x_8811_) == 1 {
                    lean_dec_ref(v___f_8808_);
                    v___x_8812_ = lean_task_pure(v___x_8811_);
                    return v___x_8812_;
                } else {
                    lean_dec(v___x_8811_);
                    v___x_8813_ = lean_st_ref_get(v___y_8809_);
                    v_closed_8814_ = lean_ctor_get_uint8(
                        v___x_8813_,
                        (core::mem::size_of::<*mut LeanObject>() * 7) as u32,
                    );
                    lean_dec(v___x_8813_);
                    if v_closed_8814_ == 0 {
                        v___x_8815_ = lean_io_promise_new();
                        v___x_8816_ = lean_st_ref_take(v___y_8809_);
                        v_producers_8817_ = lean_ctor_get(v___x_8816_, 0);
                        v_consumers_8818_ = lean_ctor_get(v___x_8816_, 1);
                        v_capacity_8819_ = lean_ctor_get(v___x_8816_, 2);
                        v_buf_8820_ = lean_ctor_get(v___x_8816_, 3);
                        v_bufCount_8821_ = lean_ctor_get(v___x_8816_, 4);
                        v_sendIdx_8822_ = lean_ctor_get(v___x_8816_, 5);
                        v_recvIdx_8823_ = lean_ctor_get(v___x_8816_, 6);
                        v_closed_8824_ = lean_ctor_get_uint8(
                            v___x_8816_,
                            (core::mem::size_of::<*mut LeanObject>() * 7) as u32,
                        );
                        v_isSharedCheck_8838_ = (!lean_is_exclusive(v___x_8816_)) as u8;
                        if v_isSharedCheck_8838_ == 0 {
                            v___x_8826_ = v___x_8816_;
                            v_isShared_8827_ = v_isSharedCheck_8838_;
                            state = 1;
                            continue;
                        } else {
                            lean_inc(v_recvIdx_8823_);
                            lean_inc(v_sendIdx_8822_);
                            lean_inc(v_bufCount_8821_);
                            lean_inc(v_buf_8820_);
                            lean_inc(v_capacity_8819_);
                            lean_inc(v_consumers_8818_);
                            lean_inc(v_producers_8817_);
                            lean_dec(v___x_8816_);
                            v___x_8826_ = lean_box(0);
                            v_isShared_8827_ = v_isSharedCheck_8838_;
                            state = 1;
                            continue;
                        }
                    } else {
                        lean_dec_ref(v___f_8808_);
                        v___x_8839_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recv___redArg___lam__1___closed__0), core::ptr::addr_of_mut!(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recv___redArg___lam__1___closed__0_once), _init_l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recv___redArg___lam__1___closed__0);
                        return v___x_8839_;
                    }
                }
            }
            1 => {
                v___x_8828_ = lean_box(0);
                lean_inc(v___x_8815_);
                v___x_8829_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_8829_, 0, v___x_8815_);
                lean_ctor_set(v___x_8829_, 1, v___x_8828_);
                v___x_8830_ = l_Std_Queue_enqueue___redArg(v___x_8829_, v_consumers_8818_);
                if v_isShared_8827_ == 0 {
                    lean_ctor_set(v___x_8826_, 1, v___x_8830_);
                    v___x_8832_ = v___x_8826_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_8837_ = lean_alloc_ctor(0, 7, (1) as u32);
                    lean_ctor_set(v_reuseFailAlloc_8837_, 0, v_producers_8817_);
                    lean_ctor_set(v_reuseFailAlloc_8837_, 1, v___x_8830_);
                    lean_ctor_set(v_reuseFailAlloc_8837_, 2, v_capacity_8819_);
                    lean_ctor_set(v_reuseFailAlloc_8837_, 3, v_buf_8820_);
                    lean_ctor_set(v_reuseFailAlloc_8837_, 4, v_bufCount_8821_);
                    lean_ctor_set(v_reuseFailAlloc_8837_, 5, v_sendIdx_8822_);
                    lean_ctor_set(v_reuseFailAlloc_8837_, 6, v_recvIdx_8823_);
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_8837_,
                        (core::mem::size_of::<*mut LeanObject>() * 7) as u32,
                        v_closed_8824_,
                    );
                    v___x_8832_ = v_reuseFailAlloc_8837_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_8833_ = lean_st_ref_set(v___y_8809_, v___x_8832_);
                v___x_8834_ = lean_io_promise_result_opt(v___x_8815_);
                lean_dec(v___x_8815_);
                v___x_8835_ = lean_unsigned_to_nat(0);
                v___x_8836_ =
                    lean_io_bind_task(v___x_8834_, v___f_8808_, v___x_8835_, v_closed_8814_);
                return v___x_8836_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recv___redArg___lam__1___boxed(
    mut v___f_8840_: *mut LeanObject,
    mut v___y_8841_: *mut LeanObject,
    mut v___y_8842_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_8843_: *mut LeanObject = core::ptr::null_mut();
    v_res_8843_ =
        l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recv___redArg___lam__1(
            v___f_8840_,
            v___y_8841_,
        );
    lean_dec(v___y_8841_);
    return v_res_8843_;
}
pub unsafe fn l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recv___redArg___lam__0(
    mut v_ch_8844_: *mut LeanObject,
    mut v_res_8845_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_8848_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_8849_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8850_: u8 = 0;
    let mut v___x_8851_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_res_8845_) == 0 {
                    lean_dec_ref(v_ch_8844_);
                    state = 1;
                    continue;
                } else {
                    v_val_8849_ = lean_ctor_get(v_res_8845_, 0);
                    v___x_8850_ = (lean_unbox(v_val_8849_) as u8);
                    if v___x_8850_ == 0 {
                        lean_dec_ref(v_ch_8844_);
                        state = 1;
                        continue;
                    } else {
                        v___x_8851_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recv___redArg(v_ch_8844_);
                        return v___x_8851_;
                    }
                }
            }
            1 => {
                v___x_8848_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recv___redArg___lam__1___closed__0), core::ptr::addr_of_mut!(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recv___redArg___lam__1___closed__0_once), _init_l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recv___redArg___lam__1___closed__0);
                return v___x_8848_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recv___redArg___lam__0___boxed(
    mut v_ch_8852_: *mut LeanObject,
    mut v_res_8853_: *mut LeanObject,
    mut v___y_8854_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_8855_: *mut LeanObject = core::ptr::null_mut();
    v_res_8855_ =
        l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recv___redArg___lam__0(
            v_ch_8852_,
            v_res_8853_,
        );
    lean_dec(v_res_8853_);
    return v_res_8855_;
}
pub unsafe fn l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recv___redArg(
    mut v_ch_8856_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_8858_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_8859_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8860_: *mut LeanObject = core::ptr::null_mut();
    lean_inc_ref(v_ch_8856_);
    v___f_8858_ = lean_alloc_closure(
        l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recv___redArg___lam__0___boxed
            as *mut core::ffi::c_void,
        3,
        1,
    );
    lean_closure_set(v___f_8858_, 0, v_ch_8856_);
    v___f_8859_ = lean_alloc_closure(
        l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recv___redArg___lam__1___boxed
            as *mut core::ffi::c_void,
        3,
        1,
    );
    lean_closure_set(v___f_8859_, 0, v___f_8858_);
    v___x_8860_ = l_Std_Mutex_atomically___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_trySend_spec__1___redArg(v_ch_8856_, v___f_8859_);
    return v___x_8860_;
}
pub unsafe fn l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recv___redArg___boxed(
    mut v_ch_8861_: *mut LeanObject,
    mut v_a_8862_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_8863_: *mut LeanObject = core::ptr::null_mut();
    v_res_8863_ =
        l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recv___redArg(v_ch_8861_);
    return v_res_8863_;
}
pub unsafe fn l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recv(
    mut v_00_u03b1_8864_: *mut LeanObject,
    mut v_ch_8865_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_8867_: *mut LeanObject = core::ptr::null_mut();
    v___x_8867_ =
        l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recv___redArg(v_ch_8865_);
    return v___x_8867_;
}
pub unsafe fn l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recv___boxed(
    mut v_00_u03b1_8868_: *mut LeanObject,
    mut v_ch_8869_: *mut LeanObject,
    mut v_a_8870_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_8871_: *mut LeanObject = core::ptr::null_mut();
    v_res_8871_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recv(
        v_00_u03b1_8868_,
        v_ch_8869_,
    );
    return v_res_8871_;
}
pub unsafe fn l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvReady_x27___redArg___lam__0(
    mut v_toApplicative_8872_: *mut LeanObject,
    mut v_a_8873_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___y_8875_: u8 = 0;
    let mut v_toPure_8876_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8877_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8878_: *mut LeanObject = core::ptr::null_mut();
    let mut v_bufCount_8879_: *mut LeanObject = core::ptr::null_mut();
    let mut v_closed_8880_: u8 = 0;
    let mut v___x_8881_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8882_: u8 = 0;
    let mut v___x_8883_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_bufCount_8879_ = lean_ctor_get(v_a_8873_, 4);
                v_closed_8880_ = lean_ctor_get_uint8(
                    v_a_8873_,
                    (core::mem::size_of::<*mut LeanObject>() * 7) as u32,
                );
                v___x_8881_ = lean_unsigned_to_nat(0);
                v___x_8882_ = lean_nat_dec_eq(v_bufCount_8879_, v___x_8881_);
                if v___x_8882_ == 0 {
                    v___x_8883_ = 1;
                    v___y_8875_ = v___x_8883_;
                    state = 1;
                    continue;
                } else {
                    v___y_8875_ = v_closed_8880_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_toPure_8876_ = lean_ctor_get(v_toApplicative_8872_, 1);
                lean_inc(v_toPure_8876_);
                lean_dec_ref(v_toApplicative_8872_);
                v___x_8877_ = lean_box((v___y_8875_) as usize);
                v___x_8878_ = lean_apply_2(v_toPure_8876_, lean_box(0), v___x_8877_);
                return v___x_8878_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvReady_x27___redArg___lam__0___boxed(
    mut v_toApplicative_8884_: *mut LeanObject,
    mut v_a_8885_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_8886_: *mut LeanObject = core::ptr::null_mut();
    v_res_8886_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvReady_x27___redArg___lam__0(v_toApplicative_8884_, v_a_8885_);
    lean_dec_ref(v_a_8885_);
    return v_res_8886_;
}
pub unsafe fn l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvReady_x27___redArg(
    mut v_inst_8887_: *mut LeanObject,
    mut v_inst_8888_: *mut LeanObject,
    mut v_a_8889_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toApplicative_8890_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toBind_8891_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_8892_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8893_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8894_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8895_: *mut LeanObject = core::ptr::null_mut();
    v_toApplicative_8890_ = lean_ctor_get(v_inst_8887_, 0);
    lean_inc_ref(v_toApplicative_8890_);
    v_toBind_8891_ = lean_ctor_get(v_inst_8887_, 1);
    lean_inc(v_toBind_8891_);
    lean_dec_ref(v_inst_8887_);
    v___f_8892_ = lean_alloc_closure(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvReady_x27___redArg___lam__0___boxed as *mut core::ffi::c_void, 2, 1);
    lean_closure_set(v___f_8892_, 0, v_toApplicative_8890_);
    lean_inc(v_a_8889_);
    v___x_8893_ = lean_alloc_closure(l_ST_Prim_Ref_get___boxed as *mut core::ffi::c_void, 4, 3);
    lean_closure_set(v___x_8893_, 0, lean_box(0));
    lean_closure_set(v___x_8893_, 1, lean_box(0));
    lean_closure_set(v___x_8893_, 2, v_a_8889_);
    v___x_8894_ = lean_apply_2(v_inst_8888_, lean_box(0), v___x_8893_);
    v___x_8895_ = lean_apply_4(
        v_toBind_8891_,
        lean_box(0),
        lean_box(0),
        v___x_8894_,
        v___f_8892_,
    );
    return v___x_8895_;
}
pub unsafe fn l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvReady_x27___redArg___boxed(
    mut v_inst_8896_: *mut LeanObject,
    mut v_inst_8897_: *mut LeanObject,
    mut v_a_8898_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_8899_: *mut LeanObject = core::ptr::null_mut();
    v_res_8899_ =
        l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvReady_x27___redArg(
            v_inst_8896_,
            v_inst_8897_,
            v_a_8898_,
        );
    lean_dec(v_a_8898_);
    return v_res_8899_;
}
pub unsafe fn l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvReady_x27(
    mut v_m_8900_: *mut LeanObject,
    mut v_00_u03b1_8901_: *mut LeanObject,
    mut v_inst_8902_: *mut LeanObject,
    mut v_inst_8903_: *mut LeanObject,
    mut v_a_8904_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toApplicative_8905_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toBind_8906_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_8907_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8908_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8909_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8910_: *mut LeanObject = core::ptr::null_mut();
    v_toApplicative_8905_ = lean_ctor_get(v_inst_8902_, 0);
    lean_inc_ref(v_toApplicative_8905_);
    v_toBind_8906_ = lean_ctor_get(v_inst_8902_, 1);
    lean_inc(v_toBind_8906_);
    lean_dec_ref(v_inst_8902_);
    v___f_8907_ = lean_alloc_closure(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvReady_x27___redArg___lam__0___boxed as *mut core::ffi::c_void, 2, 1);
    lean_closure_set(v___f_8907_, 0, v_toApplicative_8905_);
    lean_inc(v_a_8904_);
    v___x_8908_ = lean_alloc_closure(l_ST_Prim_Ref_get___boxed as *mut core::ffi::c_void, 4, 3);
    lean_closure_set(v___x_8908_, 0, lean_box(0));
    lean_closure_set(v___x_8908_, 1, lean_box(0));
    lean_closure_set(v___x_8908_, 2, v_a_8904_);
    v___x_8909_ = lean_apply_2(v_inst_8903_, lean_box(0), v___x_8908_);
    v___x_8910_ = lean_apply_4(
        v_toBind_8906_,
        lean_box(0),
        lean_box(0),
        v___x_8909_,
        v___f_8907_,
    );
    return v___x_8910_;
}
pub unsafe fn l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvReady_x27___boxed(
    mut v_m_8911_: *mut LeanObject,
    mut v_00_u03b1_8912_: *mut LeanObject,
    mut v_inst_8913_: *mut LeanObject,
    mut v_inst_8914_: *mut LeanObject,
    mut v_a_8915_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_8916_: *mut LeanObject = core::ptr::null_mut();
    v_res_8916_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvReady_x27(
        v_m_8911_,
        v_00_u03b1_8912_,
        v_inst_8913_,
        v_inst_8914_,
        v_a_8915_,
    );
    lean_dec(v_a_8915_);
    return v_res_8916_;
}
pub unsafe fn l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_registerAux_spec__0___redArg(
    mut v_a_8917_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_8919_: *mut LeanObject = core::ptr::null_mut();
    let mut v_producers_8920_: *mut LeanObject = core::ptr::null_mut();
    let mut v_consumers_8921_: *mut LeanObject = core::ptr::null_mut();
    let mut v_capacity_8922_: *mut LeanObject = core::ptr::null_mut();
    let mut v_buf_8923_: *mut LeanObject = core::ptr::null_mut();
    let mut v_bufCount_8924_: *mut LeanObject = core::ptr::null_mut();
    let mut v_sendIdx_8925_: *mut LeanObject = core::ptr::null_mut();
    let mut v_recvIdx_8926_: *mut LeanObject = core::ptr::null_mut();
    let mut v_closed_8927_: u8 = 0;
    let mut v___x_8929_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_8930_: u8 = 0;
    let mut v___x_8931_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8932_: u8 = 0;
    let mut v___x_8933_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8934_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8935_: *mut LeanObject = core::ptr::null_mut();
    let mut v_st_8937_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_8938_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8939_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8940_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8941_: u8 = 0;
    let mut v___y_8943_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8944_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8945_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8947_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8948_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_8949_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_8950_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_8951_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8952_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8953_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8954_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8955_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8956_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8957_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8958_: u8 = 0;
    let mut v___x_8959_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8960_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_8961_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_8919_ = lean_st_ref_get(v_a_8917_);
                v_producers_8920_ = lean_ctor_get(v___x_8919_, 0);
                v_consumers_8921_ = lean_ctor_get(v___x_8919_, 1);
                v_capacity_8922_ = lean_ctor_get(v___x_8919_, 2);
                v_buf_8923_ = lean_ctor_get(v___x_8919_, 3);
                v_bufCount_8924_ = lean_ctor_get(v___x_8919_, 4);
                v_sendIdx_8925_ = lean_ctor_get(v___x_8919_, 5);
                v_recvIdx_8926_ = lean_ctor_get(v___x_8919_, 6);
                v_closed_8927_ = lean_ctor_get_uint8(
                    v___x_8919_,
                    (core::mem::size_of::<*mut LeanObject>() * 7) as u32,
                );
                v_isSharedCheck_8961_ = (!lean_is_exclusive(v___x_8919_)) as u8;
                if v_isSharedCheck_8961_ == 0 {
                    v___x_8929_ = v___x_8919_;
                    v_isShared_8930_ = v_isSharedCheck_8961_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_recvIdx_8926_);
                    lean_inc(v_sendIdx_8925_);
                    lean_inc(v_bufCount_8924_);
                    lean_inc(v_buf_8923_);
                    lean_inc(v_capacity_8922_);
                    lean_inc(v_consumers_8921_);
                    lean_inc(v_producers_8920_);
                    lean_dec(v___x_8919_);
                    v___x_8929_ = lean_box(0);
                    v_isShared_8930_ = v_isSharedCheck_8961_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_8931_ = lean_unsigned_to_nat(0);
                v___x_8932_ = lean_nat_dec_eq(v_bufCount_8924_, v___x_8931_);
                if v___x_8932_ == 0 {
                    v___x_8933_ = lean_array_fget_borrowed(v_buf_8923_, v_recvIdx_8926_);
                    v___x_8934_ = lean_box(0);
                    v___x_8935_ = lean_st_ref_swap(v___x_8933_, v___x_8934_);
                    v___x_8941_ = 1;
                    v___x_8956_ = lean_unsigned_to_nat(1);
                    v___x_8957_ = lean_nat_add(v_recvIdx_8926_, v___x_8956_);
                    lean_dec(v_recvIdx_8926_);
                    v___x_8958_ = lean_nat_dec_eq(v___x_8957_, v_capacity_8922_);
                    if v___x_8958_ == 0 {
                        v___y_8943_ = v___x_8957_;
                        state = 3;
                        continue;
                    } else {
                        lean_dec(v___x_8957_);
                        v___y_8943_ = v___x_8931_;
                        state = 3;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_8929_);
                    lean_dec(v_recvIdx_8926_);
                    lean_dec(v_sendIdx_8925_);
                    lean_dec(v_bufCount_8924_);
                    lean_dec_ref(v_buf_8923_);
                    lean_dec(v_capacity_8922_);
                    lean_dec_ref(v_consumers_8921_);
                    lean_dec_ref(v_producers_8920_);
                    v___x_8959_ = lean_box(0);
                    v___x_8960_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_8960_, 0, v___x_8959_);
                    return v___x_8960_;
                }
            }
            2 => {
                v___x_8939_ = lean_st_ref_set(v___y_8938_, v_st_8937_);
                v___x_8940_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_8940_, 0, v___x_8935_);
                return v___x_8940_;
            }
            3 => {
                v___x_8944_ = lean_unsigned_to_nat(1);
                v___x_8945_ = lean_nat_sub(v_bufCount_8924_, v___x_8944_);
                lean_dec(v_bufCount_8924_);
                lean_inc(v___y_8943_);
                lean_inc(v_sendIdx_8925_);
                lean_inc(v___x_8945_);
                lean_inc_ref(v_buf_8923_);
                lean_inc(v_capacity_8922_);
                lean_inc_ref(v_consumers_8921_);
                lean_inc_ref(v_producers_8920_);
                if v_isShared_8930_ == 0 {
                    lean_ctor_set(v___x_8929_, 6, v___y_8943_);
                    lean_ctor_set(v___x_8929_, 4, v___x_8945_);
                    v___x_8947_ = v___x_8929_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_8955_ = lean_alloc_ctor(0, 7, (1) as u32);
                    lean_ctor_set(v_reuseFailAlloc_8955_, 0, v_producers_8920_);
                    lean_ctor_set(v_reuseFailAlloc_8955_, 1, v_consumers_8921_);
                    lean_ctor_set(v_reuseFailAlloc_8955_, 2, v_capacity_8922_);
                    lean_ctor_set(v_reuseFailAlloc_8955_, 3, v_buf_8923_);
                    lean_ctor_set(v_reuseFailAlloc_8955_, 4, v___x_8945_);
                    lean_ctor_set(v_reuseFailAlloc_8955_, 5, v_sendIdx_8925_);
                    lean_ctor_set(v_reuseFailAlloc_8955_, 6, v___y_8943_);
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_8955_,
                        (core::mem::size_of::<*mut LeanObject>() * 7) as u32,
                        v_closed_8927_,
                    );
                    v___x_8947_ = v_reuseFailAlloc_8955_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_8948_ = l_Std_Queue_dequeue_x3f___redArg(v_producers_8920_);
                if lean_obj_tag(v___x_8948_) == 1 {
                    lean_dec_ref(v___x_8947_);
                    v_val_8949_ = lean_ctor_get(v___x_8948_, 0);
                    lean_inc(v_val_8949_);
                    lean_dec_ref_known(v___x_8948_, 1);
                    v_fst_8950_ = lean_ctor_get(v_val_8949_, 0);
                    lean_inc(v_fst_8950_);
                    v_snd_8951_ = lean_ctor_get(v_val_8949_, 1);
                    lean_inc(v_snd_8951_);
                    lean_dec(v_val_8949_);
                    v___x_8952_ = lean_box((v___x_8941_) as usize);
                    v___x_8953_ = lean_io_promise_resolve(v___x_8952_, v_fst_8950_);
                    lean_dec(v_fst_8950_);
                    v___x_8954_ = lean_alloc_ctor(0, 7, (1) as u32);
                    lean_ctor_set(v___x_8954_, 0, v_snd_8951_);
                    lean_ctor_set(v___x_8954_, 1, v_consumers_8921_);
                    lean_ctor_set(v___x_8954_, 2, v_capacity_8922_);
                    lean_ctor_set(v___x_8954_, 3, v_buf_8923_);
                    lean_ctor_set(v___x_8954_, 4, v___x_8945_);
                    lean_ctor_set(v___x_8954_, 5, v_sendIdx_8925_);
                    lean_ctor_set(v___x_8954_, 6, v___y_8943_);
                    lean_ctor_set_uint8(
                        v___x_8954_,
                        (core::mem::size_of::<*mut LeanObject>() * 7) as u32,
                        v_closed_8927_,
                    );
                    v_st_8937_ = v___x_8954_;
                    v___y_8938_ = v_a_8917_;
                    state = 2;
                    continue;
                } else {
                    lean_dec(v___x_8948_);
                    lean_dec(v___x_8945_);
                    lean_dec(v___y_8943_);
                    lean_dec(v_sendIdx_8925_);
                    lean_dec_ref(v_buf_8923_);
                    lean_dec(v_capacity_8922_);
                    lean_dec_ref(v_consumers_8921_);
                    v_st_8937_ = v___x_8947_;
                    v___y_8938_ = v_a_8917_;
                    state = 2;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_registerAux_spec__0___redArg___boxed(
    mut v_a_8962_: *mut LeanObject,
    mut v___y_8963_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_8964_: *mut LeanObject = core::ptr::null_mut();
    v_res_8964_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_registerAux_spec__0___redArg(v_a_8962_);
    lean_dec(v_a_8962_);
    return v_res_8964_;
}
pub unsafe fn l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_registerAux_spec__0(
    mut v_00_u03b1_8965_: *mut LeanObject,
    mut v_a_8966_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_8968_: *mut LeanObject = core::ptr::null_mut();
    v___x_8968_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_registerAux_spec__0___redArg(v_a_8966_);
    return v___x_8968_;
}
pub unsafe fn l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_registerAux_spec__0___boxed(
    mut v_00_u03b1_8969_: *mut LeanObject,
    mut v_a_8970_: *mut LeanObject,
    mut v___y_8971_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_8972_: *mut LeanObject = core::ptr::null_mut();
    v_res_8972_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_registerAux_spec__0(v_00_u03b1_8969_, v_a_8970_);
    lean_dec(v_a_8970_);
    return v_res_8972_;
}
pub unsafe fn l_Std_Async_Waiter_race___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_registerAux_spec__1___redArg(
    mut v_w_8973_: *mut LeanObject,
    mut v_lose_8974_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_finished_8976_: *mut LeanObject = core::ptr::null_mut();
    let mut v_promise_8977_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8978_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_8980_: u8 = 0;
    let mut v___x_8981_: u8 = 0;
    let mut v___x_8982_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8983_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8984_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8985_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8986_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8987_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8988_: u8 = 0;
    let mut v___x_8989_: u8 = 0;
    let mut v___x_8990_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_finished_8976_ = lean_ctor_get(v_w_8973_, 0);
                v_promise_8977_ = lean_ctor_get(v_w_8973_, 1);
                v___x_8978_ = lean_st_ref_take(v_finished_8976_);
                v___x_8988_ = (lean_unbox(v___x_8978_) as u8);
                lean_dec(v___x_8978_);
                if v___x_8988_ == 0 {
                    v___x_8989_ = 1;
                    v___y_8980_ = v___x_8989_;
                    state = 1;
                    continue;
                } else {
                    v___x_8990_ = 0;
                    v___y_8980_ = v___x_8990_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_8981_ = 1;
                v___x_8982_ = lean_box((v___x_8981_) as usize);
                v___x_8983_ = lean_st_ref_set(v_finished_8976_, v___x_8982_);
                if v___y_8980_ == 0 {
                    v___x_8984_ = lean_apply_1(v_lose_8974_, lean_box(0));
                    return v___x_8984_;
                } else {
                    lean_dec_ref(v_lose_8974_);
                    v___x_8985_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__0___redArg___lam__1___closed__0;
                    v___x_8986_ = lean_io_promise_resolve(v___x_8985_, v_promise_8977_);
                    v___x_8987_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_8987_, 0, v___x_8986_);
                    return v___x_8987_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Async_Waiter_race___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_registerAux_spec__1___redArg___boxed(
    mut v_w_8991_: *mut LeanObject,
    mut v_lose_8992_: *mut LeanObject,
    mut v___y_8993_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_8994_: *mut LeanObject = core::ptr::null_mut();
    v_res_8994_ = l_Std_Async_Waiter_race___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_registerAux_spec__1___redArg(v_w_8991_, v_lose_8992_);
    lean_dec_ref(v_w_8991_);
    return v_res_8994_;
}
pub unsafe fn l_Std_Async_Waiter_race___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_registerAux_spec__1(
    mut v_00_u03b1_8995_: *mut LeanObject,
    mut v_w_8996_: *mut LeanObject,
    mut v_lose_8997_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_8999_: *mut LeanObject = core::ptr::null_mut();
    v___x_8999_ = l_Std_Async_Waiter_race___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_registerAux_spec__1___redArg(v_w_8996_, v_lose_8997_);
    return v___x_8999_;
}
pub unsafe fn l_Std_Async_Waiter_race___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_registerAux_spec__1___boxed(
    mut v_00_u03b1_9000_: *mut LeanObject,
    mut v_w_9001_: *mut LeanObject,
    mut v_lose_9002_: *mut LeanObject,
    mut v___y_9003_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_9004_: *mut LeanObject = core::ptr::null_mut();
    v_res_9004_ = l_Std_Async_Waiter_race___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_registerAux_spec__1(v_00_u03b1_9000_, v_w_9001_, v_lose_9002_);
    lean_dec_ref(v_w_9001_);
    return v_res_9004_;
}
pub unsafe fn l_Std_Async_Waiter_race___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_registerAux_spec__2___redArg(
    mut v_w_9005_: *mut LeanObject,
    mut v_lose_9006_: *mut LeanObject,
    mut v___y_9007_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_finished_9009_: *mut LeanObject = core::ptr::null_mut();
    let mut v_promise_9010_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9011_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_9013_: u8 = 0;
    let mut v___x_9014_: u8 = 0;
    let mut v___x_9015_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9016_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9017_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9018_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_9019_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9021_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_9022_: u8 = 0;
    let mut v___x_9023_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9024_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9026_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_9027_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_9028_: u8 = 0;
    let mut v___x_9029_: u8 = 0;
    let mut v___x_9030_: u8 = 0;
    let mut v___x_9031_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_finished_9009_ = lean_ctor_get(v_w_9005_, 0);
                v_promise_9010_ = lean_ctor_get(v_w_9005_, 1);
                v___x_9011_ = lean_st_ref_take(v_finished_9009_);
                v___x_9029_ = (lean_unbox(v___x_9011_) as u8);
                lean_dec(v___x_9011_);
                if v___x_9029_ == 0 {
                    v___x_9030_ = 1;
                    v___y_9013_ = v___x_9030_;
                    state = 1;
                    continue;
                } else {
                    v___x_9031_ = 0;
                    v___y_9013_ = v___x_9031_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_9014_ = 1;
                v___x_9015_ = lean_box((v___x_9014_) as usize);
                v___x_9016_ = lean_st_ref_set(v_finished_9009_, v___x_9015_);
                if v___y_9013_ == 0 {
                    lean_inc(v___y_9007_);
                    v___x_9017_ = lean_apply_2(v_lose_9006_, v___y_9007_, lean_box(0));
                    return v___x_9017_;
                } else {
                    lean_dec_ref(v_lose_9006_);
                    v___x_9018_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_registerAux_spec__0___redArg(v___y_9007_);
                    v_a_9019_ = lean_ctor_get(v___x_9018_, 0);
                    v_isSharedCheck_9028_ = (!lean_is_exclusive(v___x_9018_)) as u8;
                    if v_isSharedCheck_9028_ == 0 {
                        v___x_9021_ = v___x_9018_;
                        v_isShared_9022_ = v_isSharedCheck_9028_;
                        state = 2;
                        continue;
                    } else {
                        lean_inc(v_a_9019_);
                        lean_dec(v___x_9018_);
                        v___x_9021_ = lean_box(0);
                        v_isShared_9022_ = v_isSharedCheck_9028_;
                        state = 2;
                        continue;
                    }
                }
            }
            2 => {
                v___x_9023_ = lean_alloc_ctor(1, 1, (0) as u32);
                lean_ctor_set(v___x_9023_, 0, v_a_9019_);
                v___x_9024_ = lean_io_promise_resolve(v___x_9023_, v_promise_9010_);
                if v_isShared_9022_ == 0 {
                    lean_ctor_set(v___x_9021_, 0, v___x_9024_);
                    v___x_9026_ = v___x_9021_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_9027_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_9027_, 0, v___x_9024_);
                    v___x_9026_ = v_reuseFailAlloc_9027_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_9026_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Async_Waiter_race___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_registerAux_spec__2___redArg___boxed(
    mut v_w_9032_: *mut LeanObject,
    mut v_lose_9033_: *mut LeanObject,
    mut v___y_9034_: *mut LeanObject,
    mut v___y_9035_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_9036_: *mut LeanObject = core::ptr::null_mut();
    v_res_9036_ = l_Std_Async_Waiter_race___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_registerAux_spec__2___redArg(v_w_9032_, v_lose_9033_, v___y_9034_);
    lean_dec(v___y_9034_);
    lean_dec_ref(v_w_9032_);
    return v_res_9036_;
}
pub unsafe fn l_Std_Async_Waiter_race___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_registerAux_spec__2(
    mut v_00_u03b1_9037_: *mut LeanObject,
    mut v_w_9038_: *mut LeanObject,
    mut v_lose_9039_: *mut LeanObject,
    mut v___y_9040_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_9042_: *mut LeanObject = core::ptr::null_mut();
    v___x_9042_ = l_Std_Async_Waiter_race___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_registerAux_spec__2___redArg(v_w_9038_, v_lose_9039_, v___y_9040_);
    return v___x_9042_;
}
pub unsafe fn l_Std_Async_Waiter_race___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_registerAux_spec__2___boxed(
    mut v_00_u03b1_9043_: *mut LeanObject,
    mut v_w_9044_: *mut LeanObject,
    mut v_lose_9045_: *mut LeanObject,
    mut v___y_9046_: *mut LeanObject,
    mut v___y_9047_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_9048_: *mut LeanObject = core::ptr::null_mut();
    v_res_9048_ = l_Std_Async_Waiter_race___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_registerAux_spec__2(v_00_u03b1_9043_, v_w_9044_, v_lose_9045_, v___y_9046_);
    lean_dec(v___y_9046_);
    lean_dec_ref(v_w_9044_);
    return v_res_9048_;
}
pub unsafe fn l_Std_Mutex_atomically___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_registerAux_spec__3___redArg(
    mut v_mutex_9049_: *mut LeanObject,
    mut v_k_9050_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_ref_9052_: *mut LeanObject = core::ptr::null_mut();
    let mut v_mutex_9053_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9054_: *mut LeanObject = core::ptr::null_mut();
    let mut v_r_9055_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_9056_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9058_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_9059_: u8 = 0;
    let mut v___x_9060_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9062_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_9063_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_9064_: u8 = 0;
    let mut v_a_9065_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9067_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_9068_: u8 = 0;
    let mut v___x_9069_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9071_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_9072_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_9073_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ref_9052_ = lean_ctor_get(v_mutex_9049_, 0);
                lean_inc(v_ref_9052_);
                v_mutex_9053_ = lean_ctor_get(v_mutex_9049_, 1);
                lean_inc(v_mutex_9053_);
                lean_dec_ref(v_mutex_9049_);
                v___x_9054_ = lean_io_basemutex_lock(v_mutex_9053_);
                v_r_9055_ = lean_apply_2(v_k_9050_, v_ref_9052_, lean_box(0));
                if lean_obj_tag(v_r_9055_) == 0 {
                    v_a_9056_ = lean_ctor_get(v_r_9055_, 0);
                    v_isSharedCheck_9064_ = (!lean_is_exclusive(v_r_9055_)) as u8;
                    if v_isSharedCheck_9064_ == 0 {
                        v___x_9058_ = v_r_9055_;
                        v_isShared_9059_ = v_isSharedCheck_9064_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_9056_);
                        lean_dec(v_r_9055_);
                        v___x_9058_ = lean_box(0);
                        v_isShared_9059_ = v_isSharedCheck_9064_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_9065_ = lean_ctor_get(v_r_9055_, 0);
                    v_isSharedCheck_9073_ = (!lean_is_exclusive(v_r_9055_)) as u8;
                    if v_isSharedCheck_9073_ == 0 {
                        v___x_9067_ = v_r_9055_;
                        v_isShared_9068_ = v_isSharedCheck_9073_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_9065_);
                        lean_dec(v_r_9055_);
                        v___x_9067_ = lean_box(0);
                        v_isShared_9068_ = v_isSharedCheck_9073_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v___x_9060_ = lean_io_basemutex_unlock(v_mutex_9053_);
                lean_dec(v_mutex_9053_);
                if v_isShared_9059_ == 0 {
                    v___x_9062_ = v___x_9058_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_9063_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_9063_, 0, v_a_9056_);
                    v___x_9062_ = v_reuseFailAlloc_9063_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_9062_;
            }
            3 => {
                v___x_9069_ = lean_io_basemutex_unlock(v_mutex_9053_);
                lean_dec(v_mutex_9053_);
                if v_isShared_9068_ == 0 {
                    v___x_9071_ = v___x_9067_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_9072_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_9072_, 0, v_a_9065_);
                    v___x_9071_ = v_reuseFailAlloc_9072_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_9071_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Mutex_atomically___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_registerAux_spec__3___redArg___boxed(
    mut v_mutex_9074_: *mut LeanObject,
    mut v_k_9075_: *mut LeanObject,
    mut v___y_9076_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_9077_: *mut LeanObject = core::ptr::null_mut();
    v_res_9077_ = l_Std_Mutex_atomically___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_registerAux_spec__3___redArg(v_mutex_9074_, v_k_9075_);
    return v_res_9077_;
}
pub unsafe fn l_Std_Mutex_atomically___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_registerAux_spec__3(
    mut v_00_u03b1_9078_: *mut LeanObject,
    mut v_00_u03b2_9079_: *mut LeanObject,
    mut v_mutex_9080_: *mut LeanObject,
    mut v_k_9081_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_9083_: *mut LeanObject = core::ptr::null_mut();
    v___x_9083_ = l_Std_Mutex_atomically___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_registerAux_spec__3___redArg(v_mutex_9080_, v_k_9081_);
    return v___x_9083_;
}
pub unsafe fn l_Std_Mutex_atomically___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_registerAux_spec__3___boxed(
    mut v_00_u03b1_9084_: *mut LeanObject,
    mut v_00_u03b2_9085_: *mut LeanObject,
    mut v_mutex_9086_: *mut LeanObject,
    mut v_k_9087_: *mut LeanObject,
    mut v___y_9088_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_9089_: *mut LeanObject = core::ptr::null_mut();
    v_res_9089_ = l_Std_Mutex_atomically___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_registerAux_spec__3(v_00_u03b1_9084_, v_00_u03b2_9085_, v_mutex_9086_, v_k_9087_);
    return v_res_9089_;
}
pub unsafe fn l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_registerAux___redArg___lam__0(
    mut v___x_9090_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_9092_: *mut LeanObject = core::ptr::null_mut();
    v___x_9092_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_9092_, 0, v___x_9090_);
    return v___x_9092_;
}
pub unsafe fn l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_registerAux___redArg___lam__0___boxed(
    mut v___x_9093_: *mut LeanObject,
    mut v___y_9094_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_9095_: *mut LeanObject = core::ptr::null_mut();
    v_res_9095_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_registerAux___redArg___lam__0(v___x_9093_);
    return v_res_9095_;
}
pub unsafe fn l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_registerAux___redArg___lam__2(
    mut v_____do__lift_9096_: u8,
    mut v___y_9097_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_9099_: *mut LeanObject = core::ptr::null_mut();
    let mut v_producers_9100_: *mut LeanObject = core::ptr::null_mut();
    let mut v_consumers_9101_: *mut LeanObject = core::ptr::null_mut();
    let mut v_capacity_9102_: *mut LeanObject = core::ptr::null_mut();
    let mut v_buf_9103_: *mut LeanObject = core::ptr::null_mut();
    let mut v_bufCount_9104_: *mut LeanObject = core::ptr::null_mut();
    let mut v_sendIdx_9105_: *mut LeanObject = core::ptr::null_mut();
    let mut v_recvIdx_9106_: *mut LeanObject = core::ptr::null_mut();
    let mut v_closed_9107_: u8 = 0;
    let mut v___x_9109_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_9110_: u8 = 0;
    let mut v___x_9111_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_9112_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9114_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_9115_: u8 = 0;
    let mut v_fst_9116_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_9117_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9118_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9120_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9121_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9123_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_9124_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_9125_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_9126_: u8 = 0;
    let mut v___x_9127_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9128_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_9129_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_9099_ = lean_st_ref_get(v___y_9097_);
                v_producers_9100_ = lean_ctor_get(v___x_9099_, 0);
                v_consumers_9101_ = lean_ctor_get(v___x_9099_, 1);
                v_capacity_9102_ = lean_ctor_get(v___x_9099_, 2);
                v_buf_9103_ = lean_ctor_get(v___x_9099_, 3);
                v_bufCount_9104_ = lean_ctor_get(v___x_9099_, 4);
                v_sendIdx_9105_ = lean_ctor_get(v___x_9099_, 5);
                v_recvIdx_9106_ = lean_ctor_get(v___x_9099_, 6);
                v_closed_9107_ = lean_ctor_get_uint8(
                    v___x_9099_,
                    (core::mem::size_of::<*mut LeanObject>() * 7) as u32,
                );
                v_isSharedCheck_9129_ = (!lean_is_exclusive(v___x_9099_)) as u8;
                if v_isSharedCheck_9129_ == 0 {
                    v___x_9109_ = v___x_9099_;
                    v_isShared_9110_ = v_isSharedCheck_9129_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_recvIdx_9106_);
                    lean_inc(v_sendIdx_9105_);
                    lean_inc(v_bufCount_9104_);
                    lean_inc(v_buf_9103_);
                    lean_inc(v_capacity_9102_);
                    lean_inc(v_consumers_9101_);
                    lean_inc(v_producers_9100_);
                    lean_dec(v___x_9099_);
                    v___x_9109_ = lean_box(0);
                    v_isShared_9110_ = v_isSharedCheck_9129_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_9111_ = l_Std_Queue_dequeue_x3f___redArg(v_consumers_9101_);
                if lean_obj_tag(v___x_9111_) == 1 {
                    v_val_9112_ = lean_ctor_get(v___x_9111_, 0);
                    v_isSharedCheck_9126_ = (!lean_is_exclusive(v___x_9111_)) as u8;
                    if v_isSharedCheck_9126_ == 0 {
                        v___x_9114_ = v___x_9111_;
                        v_isShared_9115_ = v_isSharedCheck_9126_;
                        state = 2;
                        continue;
                    } else {
                        lean_inc(v_val_9112_);
                        lean_dec(v___x_9111_);
                        v___x_9114_ = lean_box(0);
                        v_isShared_9115_ = v_isSharedCheck_9126_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_dec(v___x_9111_);
                    lean_del_object(v___x_9109_);
                    lean_dec(v_recvIdx_9106_);
                    lean_dec(v_sendIdx_9105_);
                    lean_dec(v_bufCount_9104_);
                    lean_dec_ref(v_buf_9103_);
                    lean_dec(v_capacity_9102_);
                    lean_dec_ref(v_producers_9100_);
                    v___x_9127_ = lean_box(0);
                    v___x_9128_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_9128_, 0, v___x_9127_);
                    return v___x_9128_;
                }
            }
            2 => {
                v_fst_9116_ = lean_ctor_get(v_val_9112_, 0);
                lean_inc(v_fst_9116_);
                v_snd_9117_ = lean_ctor_get(v_val_9112_, 1);
                lean_inc(v_snd_9117_);
                lean_dec(v_val_9112_);
                v___x_9118_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_Consumer_resolve___redArg(v_fst_9116_, v_____do__lift_9096_);
                lean_dec(v_fst_9116_);
                if v_isShared_9110_ == 0 {
                    lean_ctor_set(v___x_9109_, 1, v_snd_9117_);
                    v___x_9120_ = v___x_9109_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_9125_ = lean_alloc_ctor(0, 7, (1) as u32);
                    lean_ctor_set(v_reuseFailAlloc_9125_, 0, v_producers_9100_);
                    lean_ctor_set(v_reuseFailAlloc_9125_, 1, v_snd_9117_);
                    lean_ctor_set(v_reuseFailAlloc_9125_, 2, v_capacity_9102_);
                    lean_ctor_set(v_reuseFailAlloc_9125_, 3, v_buf_9103_);
                    lean_ctor_set(v_reuseFailAlloc_9125_, 4, v_bufCount_9104_);
                    lean_ctor_set(v_reuseFailAlloc_9125_, 5, v_sendIdx_9105_);
                    lean_ctor_set(v_reuseFailAlloc_9125_, 6, v_recvIdx_9106_);
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_9125_,
                        (core::mem::size_of::<*mut LeanObject>() * 7) as u32,
                        v_closed_9107_,
                    );
                    v___x_9120_ = v_reuseFailAlloc_9125_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_9121_ = lean_st_ref_set(v___y_9097_, v___x_9120_);
                if v_isShared_9115_ == 0 {
                    lean_ctor_set_tag(v___x_9114_, 0);
                    lean_ctor_set(v___x_9114_, 0, v___x_9121_);
                    v___x_9123_ = v___x_9114_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_9124_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_9124_, 0, v___x_9121_);
                    v___x_9123_ = v_reuseFailAlloc_9124_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_9123_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_registerAux___redArg___lam__2___boxed(
    mut v_____do__lift_9130_: *mut LeanObject,
    mut v___y_9131_: *mut LeanObject,
    mut v___y_9132_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_____do__lift_3921__boxed_9133_: u8 = 0;
    let mut v_res_9134_: *mut LeanObject = core::ptr::null_mut();
    v_____do__lift_3921__boxed_9133_ = (lean_unbox(v_____do__lift_9130_) as u8);
    v_res_9134_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_registerAux___redArg___lam__2(v_____do__lift_3921__boxed_9133_, v___y_9131_);
    lean_dec(v___y_9131_);
    return v_res_9134_;
}
pub unsafe fn l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_registerAux___redArg___lam__3(
    mut v_waiter_9135_: *mut LeanObject,
    mut v___f_9136_: *mut LeanObject,
    mut v_____do__lift_9137_: u8,
    mut v___y_9138_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_9140_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9141_: *mut LeanObject = core::ptr::null_mut();
    let mut v_producers_9142_: *mut LeanObject = core::ptr::null_mut();
    let mut v_consumers_9143_: *mut LeanObject = core::ptr::null_mut();
    let mut v_capacity_9144_: *mut LeanObject = core::ptr::null_mut();
    let mut v_buf_9145_: *mut LeanObject = core::ptr::null_mut();
    let mut v_bufCount_9146_: *mut LeanObject = core::ptr::null_mut();
    let mut v_sendIdx_9147_: *mut LeanObject = core::ptr::null_mut();
    let mut v_recvIdx_9148_: *mut LeanObject = core::ptr::null_mut();
    let mut v_closed_9149_: u8 = 0;
    let mut v___x_9151_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_9152_: u8 = 0;
    let mut v___x_9153_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9154_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9155_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9157_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9158_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9159_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9160_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9161_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_9162_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_9163_: u8 = 0;
    let mut v___x_9164_: *mut LeanObject = core::ptr::null_mut();
    let mut v_lose_9165_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9166_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if v_____do__lift_9137_ == 0 {
                    v___x_9140_ = lean_io_promise_new();
                    v___x_9141_ = lean_st_ref_take(v___y_9138_);
                    v_producers_9142_ = lean_ctor_get(v___x_9141_, 0);
                    v_consumers_9143_ = lean_ctor_get(v___x_9141_, 1);
                    v_capacity_9144_ = lean_ctor_get(v___x_9141_, 2);
                    v_buf_9145_ = lean_ctor_get(v___x_9141_, 3);
                    v_bufCount_9146_ = lean_ctor_get(v___x_9141_, 4);
                    v_sendIdx_9147_ = lean_ctor_get(v___x_9141_, 5);
                    v_recvIdx_9148_ = lean_ctor_get(v___x_9141_, 6);
                    v_closed_9149_ = lean_ctor_get_uint8(
                        v___x_9141_,
                        (core::mem::size_of::<*mut LeanObject>() * 7) as u32,
                    );
                    v_isSharedCheck_9163_ = (!lean_is_exclusive(v___x_9141_)) as u8;
                    if v_isSharedCheck_9163_ == 0 {
                        v___x_9151_ = v___x_9141_;
                        v_isShared_9152_ = v_isSharedCheck_9163_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_recvIdx_9148_);
                        lean_inc(v_sendIdx_9147_);
                        lean_inc(v_bufCount_9146_);
                        lean_inc(v_buf_9145_);
                        lean_inc(v_capacity_9144_);
                        lean_inc(v_consumers_9143_);
                        lean_inc(v_producers_9142_);
                        lean_dec(v___x_9141_);
                        v___x_9151_ = lean_box(0);
                        v_isShared_9152_ = v_isSharedCheck_9163_;
                        state = 1;
                        continue;
                    }
                } else {
                    lean_dec_ref(v___f_9136_);
                    v___x_9164_ = lean_box((v_____do__lift_9137_) as usize);
                    v_lose_9165_ = lean_alloc_closure(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_registerAux___redArg___lam__2___boxed as *mut core::ffi::c_void, 3, 1);
                    lean_closure_set(v_lose_9165_, 0, v___x_9164_);
                    v___x_9166_ = l_Std_Async_Waiter_race___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_registerAux_spec__2___redArg(v_waiter_9135_, v_lose_9165_, v___y_9138_);
                    lean_dec_ref(v_waiter_9135_);
                    return v___x_9166_;
                }
            }
            1 => {
                v___x_9153_ = lean_alloc_ctor(1, 1, (0) as u32);
                lean_ctor_set(v___x_9153_, 0, v_waiter_9135_);
                lean_inc(v___x_9140_);
                v___x_9154_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_9154_, 0, v___x_9140_);
                lean_ctor_set(v___x_9154_, 1, v___x_9153_);
                v___x_9155_ = l_Std_Queue_enqueue___redArg(v___x_9154_, v_consumers_9143_);
                if v_isShared_9152_ == 0 {
                    lean_ctor_set(v___x_9151_, 1, v___x_9155_);
                    v___x_9157_ = v___x_9151_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_9162_ = lean_alloc_ctor(0, 7, (1) as u32);
                    lean_ctor_set(v_reuseFailAlloc_9162_, 0, v_producers_9142_);
                    lean_ctor_set(v_reuseFailAlloc_9162_, 1, v___x_9155_);
                    lean_ctor_set(v_reuseFailAlloc_9162_, 2, v_capacity_9144_);
                    lean_ctor_set(v_reuseFailAlloc_9162_, 3, v_buf_9145_);
                    lean_ctor_set(v_reuseFailAlloc_9162_, 4, v_bufCount_9146_);
                    lean_ctor_set(v_reuseFailAlloc_9162_, 5, v_sendIdx_9147_);
                    lean_ctor_set(v_reuseFailAlloc_9162_, 6, v_recvIdx_9148_);
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_9162_,
                        (core::mem::size_of::<*mut LeanObject>() * 7) as u32,
                        v_closed_9149_,
                    );
                    v___x_9157_ = v_reuseFailAlloc_9162_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_9158_ = lean_st_ref_set(v___y_9138_, v___x_9157_);
                v___x_9159_ = lean_io_promise_result_opt(v___x_9140_);
                lean_dec(v___x_9140_);
                v___x_9160_ = lean_unsigned_to_nat(0);
                v___x_9161_ = l_EIO_chainTask___redArg(
                    v___x_9159_,
                    v___f_9136_,
                    v___x_9160_,
                    v_____do__lift_9137_,
                );
                return v___x_9161_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_registerAux___redArg___lam__3___boxed(
    mut v_waiter_9167_: *mut LeanObject,
    mut v___f_9168_: *mut LeanObject,
    mut v_____do__lift_9169_: *mut LeanObject,
    mut v___y_9170_: *mut LeanObject,
    mut v___y_9171_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_____do__lift_3977__boxed_9172_: u8 = 0;
    let mut v_res_9173_: *mut LeanObject = core::ptr::null_mut();
    v_____do__lift_3977__boxed_9172_ = (lean_unbox(v_____do__lift_9169_) as u8);
    v_res_9173_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_registerAux___redArg___lam__3(v_waiter_9167_, v___f_9168_, v_____do__lift_3977__boxed_9172_, v___y_9170_);
    lean_dec(v___y_9170_);
    return v_res_9173_;
}
pub unsafe fn l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_registerAux___redArg___lam__4(
    mut v___f_9174_: *mut LeanObject,
    mut v___y_9175_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_9177_: *mut LeanObject = core::ptr::null_mut();
    let mut v_bufCount_9178_: *mut LeanObject = core::ptr::null_mut();
    let mut v_closed_9179_: u8 = 0;
    let mut v___x_9180_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9181_: u8 = 0;
    v___x_9177_ = lean_st_ref_get(v___y_9175_);
    v_bufCount_9178_ = lean_ctor_get(v___x_9177_, 4);
    lean_inc(v_bufCount_9178_);
    v_closed_9179_ = lean_ctor_get_uint8(
        v___x_9177_,
        (core::mem::size_of::<*mut LeanObject>() * 7) as u32,
    );
    lean_dec(v___x_9177_);
    v___x_9180_ = lean_unsigned_to_nat(0);
    v___x_9181_ = lean_nat_dec_eq(v_bufCount_9178_, v___x_9180_);
    lean_dec(v_bufCount_9178_);
    if v___x_9181_ == 0 {
        let mut v___x_9182_: u8 = 0;
        let mut v___x_9183_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_9184_: *mut LeanObject = core::ptr::null_mut();
        v___x_9182_ = 1;
        v___x_9183_ = lean_box((v___x_9182_) as usize);
        lean_inc(v___y_9175_);
        v___x_9184_ = lean_apply_3(v___f_9174_, v___x_9183_, v___y_9175_, lean_box(0));
        return v___x_9184_;
    } else {
        let mut v___x_9185_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_9186_: *mut LeanObject = core::ptr::null_mut();
        v___x_9185_ = lean_box((v_closed_9179_) as usize);
        lean_inc(v___y_9175_);
        v___x_9186_ = lean_apply_3(v___f_9174_, v___x_9185_, v___y_9175_, lean_box(0));
        return v___x_9186_;
    }
}
pub unsafe fn l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_registerAux___redArg___lam__4___boxed(
    mut v___f_9187_: *mut LeanObject,
    mut v___y_9188_: *mut LeanObject,
    mut v___y_9189_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_9190_: *mut LeanObject = core::ptr::null_mut();
    v_res_9190_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_registerAux___redArg___lam__4(v___f_9187_, v___y_9188_);
    lean_dec(v___y_9188_);
    return v_res_9190_;
}
pub unsafe fn l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_registerAux___redArg___lam__1(
    mut v_waiter_9193_: *mut LeanObject,
    mut v_ch_9194_: *mut LeanObject,
    mut v_x_9195_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_9195_) == 0 {
        let mut v___x_9197_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_9198_: *mut LeanObject = core::ptr::null_mut();
        lean_dec_ref(v_ch_9194_);
        lean_dec_ref(v_waiter_9193_);
        v___x_9197_ = lean_box(0);
        v___x_9198_ = lean_alloc_ctor(0, 1, (0) as u32);
        lean_ctor_set(v___x_9198_, 0, v___x_9197_);
        return v___x_9198_;
    } else {
        let mut v_val_9199_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_9200_: u8 = 0;
        v_val_9199_ = lean_ctor_get(v_x_9195_, 0);
        v___x_9200_ = (lean_unbox(v_val_9199_) as u8);
        if v___x_9200_ == 0 {
            let mut v___f_9201_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_9202_: *mut LeanObject = core::ptr::null_mut();
            lean_dec_ref(v_ch_9194_);
            v___f_9201_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_registerAux___redArg___lam__1___closed__0;
            v___x_9202_ = l_Std_Async_Waiter_race___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_registerAux_spec__1___redArg(v_waiter_9193_, v___f_9201_);
            lean_dec_ref(v_waiter_9193_);
            return v___x_9202_;
        } else {
            let mut v___x_9203_: *mut LeanObject = core::ptr::null_mut();
            v___x_9203_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_registerAux___redArg(v_ch_9194_, v_waiter_9193_);
            return v___x_9203_;
        }
    }
}
pub unsafe fn l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_registerAux___redArg___lam__1___boxed(
    mut v_waiter_9204_: *mut LeanObject,
    mut v_ch_9205_: *mut LeanObject,
    mut v_x_9206_: *mut LeanObject,
    mut v___y_9207_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_9208_: *mut LeanObject = core::ptr::null_mut();
    v_res_9208_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_registerAux___redArg___lam__1(v_waiter_9204_, v_ch_9205_, v_x_9206_);
    lean_dec(v_x_9206_);
    return v_res_9208_;
}
pub unsafe fn l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_registerAux___redArg(
    mut v_ch_9209_: *mut LeanObject,
    mut v_waiter_9210_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_9212_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_9213_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_9214_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9215_: *mut LeanObject = core::ptr::null_mut();
    lean_inc_ref(v_ch_9209_);
    lean_inc_ref(v_waiter_9210_);
    v___f_9212_ = lean_alloc_closure(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_registerAux___redArg___lam__1___boxed as *mut core::ffi::c_void, 4, 2);
    lean_closure_set(v___f_9212_, 0, v_waiter_9210_);
    lean_closure_set(v___f_9212_, 1, v_ch_9209_);
    v___f_9213_ = lean_alloc_closure(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_registerAux___redArg___lam__3___boxed as *mut core::ffi::c_void, 5, 2);
    lean_closure_set(v___f_9213_, 0, v_waiter_9210_);
    lean_closure_set(v___f_9213_, 1, v___f_9212_);
    v___f_9214_ = lean_alloc_closure(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_registerAux___redArg___lam__4___boxed as *mut core::ffi::c_void, 3, 1);
    lean_closure_set(v___f_9214_, 0, v___f_9213_);
    v___x_9215_ = l_Std_Mutex_atomically___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_registerAux_spec__3___redArg(v_ch_9209_, v___f_9214_);
    return v___x_9215_;
}
pub unsafe fn l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_registerAux___redArg___boxed(
    mut v_ch_9216_: *mut LeanObject,
    mut v_waiter_9217_: *mut LeanObject,
    mut v_a_9218_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_9219_: *mut LeanObject = core::ptr::null_mut();
    v_res_9219_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_registerAux___redArg(v_ch_9216_, v_waiter_9217_);
    return v_res_9219_;
}
pub unsafe fn l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_registerAux(
    mut v_00_u03b1_9220_: *mut LeanObject,
    mut v_ch_9221_: *mut LeanObject,
    mut v_waiter_9222_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_9224_: *mut LeanObject = core::ptr::null_mut();
    v___x_9224_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_registerAux___redArg(v_ch_9221_, v_waiter_9222_);
    return v___x_9224_;
}
pub unsafe fn l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_registerAux___boxed(
    mut v_00_u03b1_9225_: *mut LeanObject,
    mut v_ch_9226_: *mut LeanObject,
    mut v_waiter_9227_: *mut LeanObject,
    mut v_a_9228_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_9229_: *mut LeanObject = core::ptr::null_mut();
    v_res_9229_ =
        l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_registerAux(
            v_00_u03b1_9225_,
            v_ch_9226_,
            v_waiter_9227_,
        );
    return v_res_9229_;
}
pub unsafe fn l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_spec__0___redArg___lam__0(
    mut v_x_9230_: *mut LeanObject,
    mut v_x_9231_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_9233_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9235_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_9236_: u8 = 0;
    let mut v___x_9238_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9239_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_9240_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_9241_: u8 = 0;
    let mut v___x_9242_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_9231_) == 0 {
                    lean_dec_ref(v_x_9230_);
                    v_a_9233_ = lean_ctor_get(v_x_9231_, 0);
                    v_isSharedCheck_9241_ = (!lean_is_exclusive(v_x_9231_)) as u8;
                    if v_isSharedCheck_9241_ == 0 {
                        v___x_9235_ = v_x_9231_;
                        v_isShared_9236_ = v_isSharedCheck_9241_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_9233_);
                        lean_dec(v_x_9231_);
                        v___x_9235_ = lean_box(0);
                        v_isShared_9236_ = v_isSharedCheck_9241_;
                        state = 1;
                        continue;
                    }
                } else {
                    lean_dec_ref_known(v_x_9231_, 1);
                    v___x_9242_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_9242_, 0, v_x_9230_);
                    return v___x_9242_;
                }
            }
            1 => {
                if v_isShared_9236_ == 0 {
                    v___x_9238_ = v___x_9235_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_9240_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_9240_, 0, v_a_9233_);
                    v___x_9238_ = v_reuseFailAlloc_9240_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_9239_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_9239_, 0, v___x_9238_);
                return v___x_9239_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_spec__0___redArg___lam__0___boxed(
    mut v_x_9243_: *mut LeanObject,
    mut v_x_9244_: *mut LeanObject,
    mut v___y_9245_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_9246_: *mut LeanObject = core::ptr::null_mut();
    v_res_9246_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_spec__0___redArg___lam__0(v_x_9243_, v_x_9244_);
    return v_res_9246_;
}
pub unsafe fn l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_spec__0___redArg___lam__1(
    mut v___x_9247_: *mut LeanObject,
    mut v___x_9248_: u8,
    mut v___f_9249_: *mut LeanObject,
    mut v_____r_9250_: *mut LeanObject,
    mut v_st_9251_: *mut LeanObject,
    mut v___y_9252_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_9254_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9255_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9256_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9257_: *mut LeanObject = core::ptr::null_mut();
    v___x_9254_ = lean_st_ref_set(v___y_9252_, v_st_9251_);
    v___x_9255_ = lean_alloc_ctor(1, 1, (0) as u32);
    lean_ctor_set(v___x_9255_, 0, v___x_9254_);
    v___x_9256_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_9256_, 0, v___x_9255_);
    v___x_9257_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(
        lean_box(0),
        lean_box(0),
        v___x_9247_,
        v___x_9248_,
        v___x_9256_,
        v___f_9249_,
    );
    return v___x_9257_;
}
pub unsafe fn l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_spec__0___redArg___lam__1___boxed(
    mut v___x_9258_: *mut LeanObject,
    mut v___x_9259_: *mut LeanObject,
    mut v___f_9260_: *mut LeanObject,
    mut v_____r_9261_: *mut LeanObject,
    mut v_st_9262_: *mut LeanObject,
    mut v___y_9263_: *mut LeanObject,
    mut v___y_9264_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6388__boxed_9265_: u8 = 0;
    let mut v_res_9266_: *mut LeanObject = core::ptr::null_mut();
    v___x_6388__boxed_9265_ = (lean_unbox(v___x_9259_) as u8);
    v_res_9266_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_spec__0___redArg___lam__1(v___x_9258_, v___x_6388__boxed_9265_, v___f_9260_, v_____r_9261_, v_st_9262_, v___y_9263_);
    lean_dec(v___y_9263_);
    return v_res_9266_;
}
pub unsafe fn l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_spec__0___redArg___lam__2(
    mut v_snd_9267_: *mut LeanObject,
    mut v_consumers_9268_: *mut LeanObject,
    mut v_capacity_9269_: *mut LeanObject,
    mut v_buf_9270_: *mut LeanObject,
    mut v___x_9271_: *mut LeanObject,
    mut v_sendIdx_9272_: *mut LeanObject,
    mut v___y_9273_: *mut LeanObject,
    mut v_closed_9274_: u8,
    mut v___f_9275_: *mut LeanObject,
    mut v_a_9276_: *mut LeanObject,
    mut v_x_9277_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_9279_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9281_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_9282_: u8 = 0;
    let mut v___x_9284_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9285_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_9286_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_9287_: u8 = 0;
    let mut v___x_9288_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9289_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9290_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_9277_) == 0 {
                    lean_dec_ref(v___f_9275_);
                    lean_dec(v___y_9273_);
                    lean_dec(v_sendIdx_9272_);
                    lean_dec(v___x_9271_);
                    lean_dec_ref(v_buf_9270_);
                    lean_dec(v_capacity_9269_);
                    lean_dec_ref(v_consumers_9268_);
                    lean_dec_ref(v_snd_9267_);
                    v_a_9279_ = lean_ctor_get(v_x_9277_, 0);
                    v_isSharedCheck_9287_ = (!lean_is_exclusive(v_x_9277_)) as u8;
                    if v_isSharedCheck_9287_ == 0 {
                        v___x_9281_ = v_x_9277_;
                        v_isShared_9282_ = v_isSharedCheck_9287_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_9279_);
                        lean_dec(v_x_9277_);
                        v___x_9281_ = lean_box(0);
                        v_isShared_9282_ = v_isSharedCheck_9287_;
                        state = 1;
                        continue;
                    }
                } else {
                    lean_dec_ref_known(v_x_9277_, 1);
                    v___x_9288_ = lean_alloc_ctor(0, 7, (1) as u32);
                    lean_ctor_set(v___x_9288_, 0, v_snd_9267_);
                    lean_ctor_set(v___x_9288_, 1, v_consumers_9268_);
                    lean_ctor_set(v___x_9288_, 2, v_capacity_9269_);
                    lean_ctor_set(v___x_9288_, 3, v_buf_9270_);
                    lean_ctor_set(v___x_9288_, 4, v___x_9271_);
                    lean_ctor_set(v___x_9288_, 5, v_sendIdx_9272_);
                    lean_ctor_set(v___x_9288_, 6, v___y_9273_);
                    lean_ctor_set_uint8(
                        v___x_9288_,
                        (core::mem::size_of::<*mut LeanObject>() * 7) as u32,
                        v_closed_9274_,
                    );
                    v___x_9289_ = lean_box(0);
                    lean_inc(v_a_9276_);
                    v___x_9290_ = lean_apply_4(
                        v___f_9275_,
                        v___x_9289_,
                        v___x_9288_,
                        v_a_9276_,
                        lean_box(0),
                    );
                    return v___x_9290_;
                }
            }
            1 => {
                if v_isShared_9282_ == 0 {
                    v___x_9284_ = v___x_9281_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_9286_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_9286_, 0, v_a_9279_);
                    v___x_9284_ = v_reuseFailAlloc_9286_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_9285_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_9285_, 0, v___x_9284_);
                return v___x_9285_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_spec__0___redArg___lam__2___boxed(
    mut v_snd_9291_: *mut LeanObject,
    mut v_consumers_9292_: *mut LeanObject,
    mut v_capacity_9293_: *mut LeanObject,
    mut v_buf_9294_: *mut LeanObject,
    mut v___x_9295_: *mut LeanObject,
    mut v_sendIdx_9296_: *mut LeanObject,
    mut v___y_9297_: *mut LeanObject,
    mut v_closed_9298_: *mut LeanObject,
    mut v___f_9299_: *mut LeanObject,
    mut v_a_9300_: *mut LeanObject,
    mut v_x_9301_: *mut LeanObject,
    mut v___y_9302_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_closed_boxed_9303_: u8 = 0;
    let mut v_res_9304_: *mut LeanObject = core::ptr::null_mut();
    v_closed_boxed_9303_ = (lean_unbox(v_closed_9298_) as u8);
    v_res_9304_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_spec__0___redArg___lam__2(v_snd_9291_, v_consumers_9292_, v_capacity_9293_, v_buf_9294_, v___x_9295_, v_sendIdx_9296_, v___y_9297_, v_closed_boxed_9303_, v___f_9299_, v_a_9300_, v_x_9301_);
    lean_dec(v_a_9300_);
    return v_res_9304_;
}
pub unsafe fn l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_spec__0___redArg___lam__3(
    mut v___x_9305_: *mut LeanObject,
    mut v___x_9306_: u8,
    mut v_bufCount_9307_: *mut LeanObject,
    mut v_producers_9308_: *mut LeanObject,
    mut v_consumers_9309_: *mut LeanObject,
    mut v_capacity_9310_: *mut LeanObject,
    mut v_buf_9311_: *mut LeanObject,
    mut v_sendIdx_9312_: *mut LeanObject,
    mut v_closed_9313_: u8,
    mut v___x_9314_: u8,
    mut v_a_9315_: *mut LeanObject,
    mut v_recvIdx_9316_: *mut LeanObject,
    mut v_x_9317_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_9319_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_9320_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9321_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_9322_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_9324_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9325_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9326_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9327_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9328_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_9329_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9331_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_9332_: u8 = 0;
    let mut v_fst_9333_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_9334_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9335_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9336_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9337_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_9338_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9340_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9341_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9342_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_9343_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_9344_: u8 = 0;
    let mut v___x_9345_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9346_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9347_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9348_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9349_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_9317_) == 0 {
                    lean_dec(v_sendIdx_9312_);
                    lean_dec_ref(v_buf_9311_);
                    lean_dec(v_capacity_9310_);
                    lean_dec_ref(v_consumers_9309_);
                    lean_dec_ref(v_producers_9308_);
                    lean_dec(v___x_9305_);
                    v___x_9319_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_9319_, 0, v_x_9317_);
                    return v___x_9319_;
                } else {
                    v___f_9320_ = lean_alloc_closure(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_spec__0___redArg___lam__0___boxed as *mut core::ffi::c_void, 3, 1);
                    lean_closure_set(v___f_9320_, 0, v_x_9317_);
                    v___x_9321_ = lean_box((v___x_9306_) as usize);
                    lean_inc_ref(v___f_9320_);
                    lean_inc(v___x_9305_);
                    v___f_9322_ = lean_alloc_closure(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_spec__0___redArg___lam__1___boxed as *mut core::ffi::c_void, 7, 3);
                    lean_closure_set(v___f_9322_, 0, v___x_9305_);
                    lean_closure_set(v___f_9322_, 1, v___x_9321_);
                    lean_closure_set(v___f_9322_, 2, v___f_9320_);
                    v___x_9347_ = lean_unsigned_to_nat(1);
                    v___x_9348_ = lean_nat_add(v_recvIdx_9316_, v___x_9347_);
                    v___x_9349_ = lean_nat_dec_eq(v___x_9348_, v_capacity_9310_);
                    if v___x_9349_ == 0 {
                        v___y_9324_ = v___x_9348_;
                        state = 1;
                        continue;
                    } else {
                        lean_dec(v___x_9348_);
                        lean_inc(v___x_9305_);
                        v___y_9324_ = v___x_9305_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_9325_ = lean_unsigned_to_nat(1);
                v___x_9326_ = lean_nat_sub(v_bufCount_9307_, v___x_9325_);
                lean_inc(v___y_9324_);
                lean_inc(v_sendIdx_9312_);
                lean_inc(v___x_9326_);
                lean_inc_ref(v_buf_9311_);
                lean_inc(v_capacity_9310_);
                lean_inc_ref(v_consumers_9309_);
                lean_inc_ref(v_producers_9308_);
                v___x_9327_ = lean_alloc_ctor(0, 7, (1) as u32);
                lean_ctor_set(v___x_9327_, 0, v_producers_9308_);
                lean_ctor_set(v___x_9327_, 1, v_consumers_9309_);
                lean_ctor_set(v___x_9327_, 2, v_capacity_9310_);
                lean_ctor_set(v___x_9327_, 3, v_buf_9311_);
                lean_ctor_set(v___x_9327_, 4, v___x_9326_);
                lean_ctor_set(v___x_9327_, 5, v_sendIdx_9312_);
                lean_ctor_set(v___x_9327_, 6, v___y_9324_);
                lean_ctor_set_uint8(
                    v___x_9327_,
                    (core::mem::size_of::<*mut LeanObject>() * 7) as u32,
                    v_closed_9313_,
                );
                v___x_9328_ = l_Std_Queue_dequeue_x3f___redArg(v_producers_9308_);
                if lean_obj_tag(v___x_9328_) == 1 {
                    lean_dec_ref_known(v___x_9327_, 7);
                    lean_dec_ref(v___f_9320_);
                    v_val_9329_ = lean_ctor_get(v___x_9328_, 0);
                    v_isSharedCheck_9344_ = (!lean_is_exclusive(v___x_9328_)) as u8;
                    if v_isSharedCheck_9344_ == 0 {
                        v___x_9331_ = v___x_9328_;
                        v_isShared_9332_ = v_isSharedCheck_9344_;
                        state = 2;
                        continue;
                    } else {
                        lean_inc(v_val_9329_);
                        lean_dec(v___x_9328_);
                        v___x_9331_ = lean_box(0);
                        v_isShared_9332_ = v_isSharedCheck_9344_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_dec(v___x_9328_);
                    lean_dec(v___x_9326_);
                    lean_dec(v___y_9324_);
                    lean_dec_ref(v___f_9322_);
                    lean_dec(v_sendIdx_9312_);
                    lean_dec_ref(v_buf_9311_);
                    lean_dec(v_capacity_9310_);
                    lean_dec_ref(v_consumers_9309_);
                    v___x_9345_ = lean_box(0);
                    v___x_9346_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_spec__0___redArg___lam__1(v___x_9305_, v___x_9306_, v___f_9320_, v___x_9345_, v___x_9327_, v_a_9315_);
                    return v___x_9346_;
                }
            }
            2 => {
                v_fst_9333_ = lean_ctor_get(v_val_9329_, 0);
                lean_inc(v_fst_9333_);
                v_snd_9334_ = lean_ctor_get(v_val_9329_, 1);
                lean_inc(v_snd_9334_);
                lean_dec(v_val_9329_);
                v___x_9335_ = lean_box((v___x_9314_) as usize);
                v___x_9336_ = lean_io_promise_resolve(v___x_9335_, v_fst_9333_);
                lean_dec(v_fst_9333_);
                v___x_9337_ = lean_box((v_closed_9313_) as usize);
                lean_inc(v_a_9315_);
                v___f_9338_ = lean_alloc_closure(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_spec__0___redArg___lam__2___boxed as *mut core::ffi::c_void, 12, 10);
                lean_closure_set(v___f_9338_, 0, v_snd_9334_);
                lean_closure_set(v___f_9338_, 1, v_consumers_9309_);
                lean_closure_set(v___f_9338_, 2, v_capacity_9310_);
                lean_closure_set(v___f_9338_, 3, v_buf_9311_);
                lean_closure_set(v___f_9338_, 4, v___x_9326_);
                lean_closure_set(v___f_9338_, 5, v_sendIdx_9312_);
                lean_closure_set(v___f_9338_, 6, v___y_9324_);
                lean_closure_set(v___f_9338_, 7, v___x_9337_);
                lean_closure_set(v___f_9338_, 8, v___f_9322_);
                lean_closure_set(v___f_9338_, 9, v_a_9315_);
                if v_isShared_9332_ == 0 {
                    lean_ctor_set(v___x_9331_, 0, v___x_9336_);
                    v___x_9340_ = v___x_9331_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_9343_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_9343_, 0, v___x_9336_);
                    v___x_9340_ = v_reuseFailAlloc_9343_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_9341_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_9341_, 0, v___x_9340_);
                v___x_9342_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(
                    lean_box(0),
                    lean_box(0),
                    v___x_9305_,
                    v___x_9306_,
                    v___x_9341_,
                    v___f_9338_,
                );
                return v___x_9342_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_spec__0___redArg___lam__3___boxed(
    mut v___x_9350_: *mut LeanObject,
    mut v___x_9351_: *mut LeanObject,
    mut v_bufCount_9352_: *mut LeanObject,
    mut v_producers_9353_: *mut LeanObject,
    mut v_consumers_9354_: *mut LeanObject,
    mut v_capacity_9355_: *mut LeanObject,
    mut v_buf_9356_: *mut LeanObject,
    mut v_sendIdx_9357_: *mut LeanObject,
    mut v_closed_9358_: *mut LeanObject,
    mut v___x_9359_: *mut LeanObject,
    mut v_a_9360_: *mut LeanObject,
    mut v_recvIdx_9361_: *mut LeanObject,
    mut v_x_9362_: *mut LeanObject,
    mut v___y_9363_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6457__boxed_9364_: u8 = 0;
    let mut v_closed_boxed_9365_: u8 = 0;
    let mut v___x_6458__boxed_9366_: u8 = 0;
    let mut v_res_9367_: *mut LeanObject = core::ptr::null_mut();
    v___x_6457__boxed_9364_ = (lean_unbox(v___x_9351_) as u8);
    v_closed_boxed_9365_ = (lean_unbox(v_closed_9358_) as u8);
    v___x_6458__boxed_9366_ = (lean_unbox(v___x_9359_) as u8);
    v_res_9367_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_spec__0___redArg___lam__3(v___x_9350_, v___x_6457__boxed_9364_, v_bufCount_9352_, v_producers_9353_, v_consumers_9354_, v_capacity_9355_, v_buf_9356_, v_sendIdx_9357_, v_closed_boxed_9365_, v___x_6458__boxed_9366_, v_a_9360_, v_recvIdx_9361_, v_x_9362_);
    lean_dec(v_recvIdx_9361_);
    lean_dec(v_a_9360_);
    lean_dec(v_bufCount_9352_);
    return v_res_9367_;
}
pub unsafe fn l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_spec__0___redArg___lam__4(
    mut v_a_9368_: *mut LeanObject,
    mut v_x_9369_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_9371_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9373_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_9374_: u8 = 0;
    let mut v___x_9376_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9377_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_9378_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_9379_: u8 = 0;
    let mut v_a_9380_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9382_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_9383_: u8 = 0;
    let mut v_producers_9384_: *mut LeanObject = core::ptr::null_mut();
    let mut v_consumers_9385_: *mut LeanObject = core::ptr::null_mut();
    let mut v_capacity_9386_: *mut LeanObject = core::ptr::null_mut();
    let mut v_buf_9387_: *mut LeanObject = core::ptr::null_mut();
    let mut v_bufCount_9388_: *mut LeanObject = core::ptr::null_mut();
    let mut v_sendIdx_9389_: *mut LeanObject = core::ptr::null_mut();
    let mut v_recvIdx_9390_: *mut LeanObject = core::ptr::null_mut();
    let mut v_closed_9391_: u8 = 0;
    let mut v___x_9392_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9393_: u8 = 0;
    let mut v___x_9394_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9395_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9396_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9397_: u8 = 0;
    let mut v___x_9398_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9399_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9400_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_9401_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9403_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9404_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9405_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_9406_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9407_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_9408_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_9369_) == 0 {
                    v_a_9371_ = lean_ctor_get(v_x_9369_, 0);
                    v_isSharedCheck_9379_ = (!lean_is_exclusive(v_x_9369_)) as u8;
                    if v_isSharedCheck_9379_ == 0 {
                        v___x_9373_ = v_x_9369_;
                        v_isShared_9374_ = v_isSharedCheck_9379_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_9371_);
                        lean_dec(v_x_9369_);
                        v___x_9373_ = lean_box(0);
                        v_isShared_9374_ = v_isSharedCheck_9379_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_9380_ = lean_ctor_get(v_x_9369_, 0);
                    v_isSharedCheck_9408_ = (!lean_is_exclusive(v_x_9369_)) as u8;
                    if v_isSharedCheck_9408_ == 0 {
                        v___x_9382_ = v_x_9369_;
                        v_isShared_9383_ = v_isSharedCheck_9408_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_9380_);
                        lean_dec(v_x_9369_);
                        v___x_9382_ = lean_box(0);
                        v_isShared_9383_ = v_isSharedCheck_9408_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_9374_ == 0 {
                    v___x_9376_ = v___x_9373_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_9378_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_9378_, 0, v_a_9371_);
                    v___x_9376_ = v_reuseFailAlloc_9378_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_9377_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_9377_, 0, v___x_9376_);
                return v___x_9377_;
            }
            3 => {
                v_producers_9384_ = lean_ctor_get(v_a_9380_, 0);
                lean_inc_ref(v_producers_9384_);
                v_consumers_9385_ = lean_ctor_get(v_a_9380_, 1);
                lean_inc_ref(v_consumers_9385_);
                v_capacity_9386_ = lean_ctor_get(v_a_9380_, 2);
                lean_inc(v_capacity_9386_);
                v_buf_9387_ = lean_ctor_get(v_a_9380_, 3);
                lean_inc_ref(v_buf_9387_);
                v_bufCount_9388_ = lean_ctor_get(v_a_9380_, 4);
                lean_inc(v_bufCount_9388_);
                v_sendIdx_9389_ = lean_ctor_get(v_a_9380_, 5);
                lean_inc(v_sendIdx_9389_);
                v_recvIdx_9390_ = lean_ctor_get(v_a_9380_, 6);
                lean_inc(v_recvIdx_9390_);
                v_closed_9391_ = lean_ctor_get_uint8(
                    v_a_9380_,
                    (core::mem::size_of::<*mut LeanObject>() * 7) as u32,
                );
                lean_dec(v_a_9380_);
                v___x_9392_ = lean_unsigned_to_nat(0);
                v___x_9393_ = lean_nat_dec_eq(v_bufCount_9388_, v___x_9392_);
                if v___x_9393_ == 0 {
                    v___x_9394_ = lean_array_fget_borrowed(v_buf_9387_, v_recvIdx_9390_);
                    v___x_9395_ = lean_box(0);
                    v___x_9396_ = lean_st_ref_swap(v___x_9394_, v___x_9395_);
                    v___x_9397_ = 1;
                    v___x_9398_ = lean_box((v___x_9393_) as usize);
                    v___x_9399_ = lean_box((v_closed_9391_) as usize);
                    v___x_9400_ = lean_box((v___x_9397_) as usize);
                    lean_inc(v_a_9368_);
                    v___f_9401_ = lean_alloc_closure(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_spec__0___redArg___lam__3___boxed as *mut core::ffi::c_void, 14, 12);
                    lean_closure_set(v___f_9401_, 0, v___x_9392_);
                    lean_closure_set(v___f_9401_, 1, v___x_9398_);
                    lean_closure_set(v___f_9401_, 2, v_bufCount_9388_);
                    lean_closure_set(v___f_9401_, 3, v_producers_9384_);
                    lean_closure_set(v___f_9401_, 4, v_consumers_9385_);
                    lean_closure_set(v___f_9401_, 5, v_capacity_9386_);
                    lean_closure_set(v___f_9401_, 6, v_buf_9387_);
                    lean_closure_set(v___f_9401_, 7, v_sendIdx_9389_);
                    lean_closure_set(v___f_9401_, 8, v___x_9399_);
                    lean_closure_set(v___f_9401_, 9, v___x_9400_);
                    lean_closure_set(v___f_9401_, 10, v_a_9368_);
                    lean_closure_set(v___f_9401_, 11, v_recvIdx_9390_);
                    if v_isShared_9383_ == 0 {
                        lean_ctor_set(v___x_9382_, 0, v___x_9396_);
                        v___x_9403_ = v___x_9382_;
                        state = 4;
                        continue;
                    } else {
                        v_reuseFailAlloc_9406_ = lean_alloc_ctor(1, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_9406_, 0, v___x_9396_);
                        v___x_9403_ = v_reuseFailAlloc_9406_;
                        state = 4;
                        continue;
                    }
                } else {
                    lean_dec(v_recvIdx_9390_);
                    lean_dec(v_sendIdx_9389_);
                    lean_dec(v_bufCount_9388_);
                    lean_dec_ref(v_buf_9387_);
                    lean_dec(v_capacity_9386_);
                    lean_dec_ref(v_consumers_9385_);
                    lean_dec_ref(v_producers_9384_);
                    lean_del_object(v___x_9382_);
                    v___x_9407_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__0___redArg___lam__1___closed__1;
                    return v___x_9407_;
                }
            }
            4 => {
                v___x_9404_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_9404_, 0, v___x_9403_);
                v___x_9405_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(
                    lean_box(0),
                    lean_box(0),
                    v___x_9392_,
                    v___x_9393_,
                    v___x_9404_,
                    v___f_9401_,
                );
                return v___x_9405_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_spec__0___redArg___lam__4___boxed(
    mut v_a_9409_: *mut LeanObject,
    mut v_x_9410_: *mut LeanObject,
    mut v___y_9411_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_9412_: *mut LeanObject = core::ptr::null_mut();
    v_res_9412_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_spec__0___redArg___lam__4(v_a_9409_, v_x_9410_);
    lean_dec(v_a_9409_);
    return v_res_9412_;
}
pub unsafe fn l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_spec__0___redArg(
    mut v_a_9413_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_9415_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_9416_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9417_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9418_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9419_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9420_: u8 = 0;
    let mut v___x_9421_: *mut LeanObject = core::ptr::null_mut();
    v___x_9415_ = lean_st_ref_get(v_a_9413_);
    lean_inc(v_a_9413_);
    v___f_9416_ = lean_alloc_closure(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_spec__0___redArg___lam__4___boxed as *mut core::ffi::c_void, 3, 1);
    lean_closure_set(v___f_9416_, 0, v_a_9413_);
    v___x_9417_ = lean_alloc_ctor(1, 1, (0) as u32);
    lean_ctor_set(v___x_9417_, 0, v___x_9415_);
    v___x_9418_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_9418_, 0, v___x_9417_);
    v___x_9419_ = lean_unsigned_to_nat(0);
    v___x_9420_ = 0;
    v___x_9421_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(
        lean_box(0),
        lean_box(0),
        v___x_9419_,
        v___x_9420_,
        v___x_9418_,
        v___f_9416_,
    );
    return v___x_9421_;
}
pub unsafe fn l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_spec__0___redArg___boxed(
    mut v_a_9422_: *mut LeanObject,
    mut v___y_9423_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_9424_: *mut LeanObject = core::ptr::null_mut();
    v_res_9424_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_spec__0___redArg(v_a_9422_);
    lean_dec(v_a_9422_);
    return v_res_9424_;
}
pub unsafe fn l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_spec__0(
    mut v_00_u03b1_9425_: *mut LeanObject,
    mut v_a_9426_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_9428_: *mut LeanObject = core::ptr::null_mut();
    v___x_9428_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_spec__0___redArg(v_a_9426_);
    return v___x_9428_;
}
pub unsafe fn l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_spec__0___boxed(
    mut v_00_u03b1_9429_: *mut LeanObject,
    mut v_a_9430_: *mut LeanObject,
    mut v___y_9431_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_9432_: *mut LeanObject = core::ptr::null_mut();
    v_res_9432_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_spec__0(v_00_u03b1_9429_, v_a_9430_);
    lean_dec(v_a_9430_);
    return v_res_9432_;
}
pub unsafe fn l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector___redArg___lam__1(
    mut v_ch_9433_: *mut LeanObject,
    mut v_x_9434_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_val_9437_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9438_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9439_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_9440_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9442_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_9443_: u8 = 0;
    let mut v___x_9445_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_9446_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_9447_: u8 = 0;
    let mut v_a_9448_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9450_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_9451_: u8 = 0;
    let mut v___x_9453_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_9454_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_9455_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_9439_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_registerAux___redArg(v_ch_9433_, v_x_9434_);
                if lean_obj_tag(v___x_9439_) == 0 {
                    v_a_9440_ = lean_ctor_get(v___x_9439_, 0);
                    v_isSharedCheck_9447_ = (!lean_is_exclusive(v___x_9439_)) as u8;
                    if v_isSharedCheck_9447_ == 0 {
                        v___x_9442_ = v___x_9439_;
                        v_isShared_9443_ = v_isSharedCheck_9447_;
                        state = 2;
                        continue;
                    } else {
                        lean_inc(v_a_9440_);
                        lean_dec(v___x_9439_);
                        v___x_9442_ = lean_box(0);
                        v_isShared_9443_ = v_isSharedCheck_9447_;
                        state = 2;
                        continue;
                    }
                } else {
                    v_a_9448_ = lean_ctor_get(v___x_9439_, 0);
                    v_isSharedCheck_9455_ = (!lean_is_exclusive(v___x_9439_)) as u8;
                    if v_isSharedCheck_9455_ == 0 {
                        v___x_9450_ = v___x_9439_;
                        v_isShared_9451_ = v_isSharedCheck_9455_;
                        state = 4;
                        continue;
                    } else {
                        lean_inc(v_a_9448_);
                        lean_dec(v___x_9439_);
                        v___x_9450_ = lean_box(0);
                        v_isShared_9451_ = v_isSharedCheck_9455_;
                        state = 4;
                        continue;
                    }
                }
            }
            1 => {
                v___x_9438_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_9438_, 0, v_val_9437_);
                return v___x_9438_;
            }
            2 => {
                if v_isShared_9443_ == 0 {
                    lean_ctor_set_tag(v___x_9442_, 1);
                    v___x_9445_ = v___x_9442_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_9446_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_9446_, 0, v_a_9440_);
                    v___x_9445_ = v_reuseFailAlloc_9446_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v_val_9437_ = v___x_9445_;
                state = 1;
                continue;
            }
            4 => {
                if v_isShared_9451_ == 0 {
                    lean_ctor_set_tag(v___x_9450_, 0);
                    v___x_9453_ = v___x_9450_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_9454_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_9454_, 0, v_a_9448_);
                    v___x_9453_ = v_reuseFailAlloc_9454_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v_val_9437_ = v___x_9453_;
                state = 1;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector___redArg___lam__1___boxed(
    mut v_ch_9456_: *mut LeanObject,
    mut v_x_9457_: *mut LeanObject,
    mut v___y_9458_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_9459_: *mut LeanObject = core::ptr::null_mut();
    v_res_9459_ =
        l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector___redArg___lam__1(
            v_ch_9456_, v_x_9457_,
        );
    return v_res_9459_;
}
pub unsafe fn l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector___redArg___lam__0(
    mut v_x_9460_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___y_9463_: u8 = 0;
    let mut v___x_9464_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9465_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9466_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_9467_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9469_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_9470_: u8 = 0;
    let mut v___x_9472_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9473_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_9474_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_9475_: u8 = 0;
    let mut v_a_9476_: *mut LeanObject = core::ptr::null_mut();
    let mut v_bufCount_9477_: *mut LeanObject = core::ptr::null_mut();
    let mut v_closed_9478_: u8 = 0;
    let mut v___x_9479_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9480_: u8 = 0;
    let mut v___x_9481_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_9460_) == 0 {
                    v_a_9467_ = lean_ctor_get(v_x_9460_, 0);
                    v_isSharedCheck_9475_ = (!lean_is_exclusive(v_x_9460_)) as u8;
                    if v_isSharedCheck_9475_ == 0 {
                        v___x_9469_ = v_x_9460_;
                        v_isShared_9470_ = v_isSharedCheck_9475_;
                        state = 2;
                        continue;
                    } else {
                        lean_inc(v_a_9467_);
                        lean_dec(v_x_9460_);
                        v___x_9469_ = lean_box(0);
                        v_isShared_9470_ = v_isSharedCheck_9475_;
                        state = 2;
                        continue;
                    }
                } else {
                    v_a_9476_ = lean_ctor_get(v_x_9460_, 0);
                    lean_inc(v_a_9476_);
                    lean_dec_ref_known(v_x_9460_, 1);
                    v_bufCount_9477_ = lean_ctor_get(v_a_9476_, 4);
                    lean_inc(v_bufCount_9477_);
                    v_closed_9478_ = lean_ctor_get_uint8(
                        v_a_9476_,
                        (core::mem::size_of::<*mut LeanObject>() * 7) as u32,
                    );
                    lean_dec(v_a_9476_);
                    v___x_9479_ = lean_unsigned_to_nat(0);
                    v___x_9480_ = lean_nat_dec_eq(v_bufCount_9477_, v___x_9479_);
                    lean_dec(v_bufCount_9477_);
                    if v___x_9480_ == 0 {
                        v___x_9481_ = 1;
                        v___y_9463_ = v___x_9481_;
                        state = 1;
                        continue;
                    } else {
                        v___y_9463_ = v_closed_9478_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_9464_ = lean_box((v___y_9463_) as usize);
                v___x_9465_ = lean_alloc_ctor(1, 1, (0) as u32);
                lean_ctor_set(v___x_9465_, 0, v___x_9464_);
                v___x_9466_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_9466_, 0, v___x_9465_);
                return v___x_9466_;
            }
            2 => {
                if v_isShared_9470_ == 0 {
                    v___x_9472_ = v___x_9469_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_9474_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_9474_, 0, v_a_9467_);
                    v___x_9472_ = v_reuseFailAlloc_9474_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_9473_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_9473_, 0, v___x_9472_);
                return v___x_9473_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector___redArg___lam__0___boxed(
    mut v_x_9482_: *mut LeanObject,
    mut v___y_9483_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_9484_: *mut LeanObject = core::ptr::null_mut();
    v_res_9484_ =
        l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector___redArg___lam__0(
            v_x_9482_,
        );
    return v_res_9484_;
}
pub unsafe fn l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector___redArg___lam__2(
    mut v___y_9485_: *mut LeanObject,
    mut v___f_9486_: *mut LeanObject,
    mut v_x_9487_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_9489_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9491_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_9492_: u8 = 0;
    let mut v___x_9494_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9495_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_9496_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_9497_: u8 = 0;
    let mut v_a_9498_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9499_: u8 = 0;
    let mut v___x_9500_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9501_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9502_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9503_: u8 = 0;
    let mut v___x_9504_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_9487_) == 0 {
                    lean_dec_ref(v___f_9486_);
                    v_a_9489_ = lean_ctor_get(v_x_9487_, 0);
                    v_isSharedCheck_9497_ = (!lean_is_exclusive(v_x_9487_)) as u8;
                    if v_isSharedCheck_9497_ == 0 {
                        v___x_9491_ = v_x_9487_;
                        v_isShared_9492_ = v_isSharedCheck_9497_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_9489_);
                        lean_dec(v_x_9487_);
                        v___x_9491_ = lean_box(0);
                        v_isShared_9492_ = v_isSharedCheck_9497_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_9498_ = lean_ctor_get(v_x_9487_, 0);
                    lean_inc(v_a_9498_);
                    lean_dec_ref_known(v_x_9487_, 1);
                    v___x_9499_ = (lean_unbox(v_a_9498_) as u8);
                    lean_dec(v_a_9498_);
                    if v___x_9499_ == 0 {
                        lean_dec_ref(v___f_9486_);
                        v___x_9500_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector___redArg___lam__7___closed__1;
                        return v___x_9500_;
                    } else {
                        v___x_9501_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv_x27___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_spec__0___redArg(v___y_9485_);
                        v___x_9502_ = lean_unsigned_to_nat(0);
                        v___x_9503_ = 0;
                        v___x_9504_ =
                            l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(
                                lean_box(0),
                                lean_box(0),
                                v___x_9502_,
                                v___x_9503_,
                                v___x_9501_,
                                v___f_9486_,
                            );
                        return v___x_9504_;
                    }
                }
            }
            1 => {
                if v_isShared_9492_ == 0 {
                    v___x_9494_ = v___x_9491_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_9496_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_9496_, 0, v_a_9489_);
                    v___x_9494_ = v_reuseFailAlloc_9496_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_9495_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_9495_, 0, v___x_9494_);
                return v___x_9495_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector___redArg___lam__2___boxed(
    mut v___y_9505_: *mut LeanObject,
    mut v___f_9506_: *mut LeanObject,
    mut v_x_9507_: *mut LeanObject,
    mut v___y_9508_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_9509_: *mut LeanObject = core::ptr::null_mut();
    v_res_9509_ =
        l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector___redArg___lam__2(
            v___y_9505_,
            v___f_9506_,
            v_x_9507_,
        );
    lean_dec(v___y_9505_);
    return v_res_9509_;
}
pub unsafe fn l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector___redArg___lam__3(
    mut v___f_9510_: *mut LeanObject,
    mut v___f_9511_: *mut LeanObject,
    mut v___y_9512_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_9514_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9515_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9516_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9517_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9518_: u8 = 0;
    let mut v___x_9519_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_9520_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9521_: *mut LeanObject = core::ptr::null_mut();
    v___x_9514_ = lean_st_ref_get(v___y_9512_);
    v___x_9515_ = lean_alloc_ctor(1, 1, (0) as u32);
    lean_ctor_set(v___x_9515_, 0, v___x_9514_);
    v___x_9516_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_9516_, 0, v___x_9515_);
    v___x_9517_ = lean_unsigned_to_nat(0);
    v___x_9518_ = 0;
    v___x_9519_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(
        lean_box(0),
        lean_box(0),
        v___x_9517_,
        v___x_9518_,
        v___x_9516_,
        v___f_9510_,
    );
    lean_inc(v___y_9512_);
    v___f_9520_ = lean_alloc_closure(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector___redArg___lam__2___boxed as *mut core::ffi::c_void, 4, 2);
    lean_closure_set(v___f_9520_, 0, v___y_9512_);
    lean_closure_set(v___f_9520_, 1, v___f_9511_);
    v___x_9521_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(
        lean_box(0),
        lean_box(0),
        v___x_9517_,
        v___x_9518_,
        v___x_9519_,
        v___f_9520_,
    );
    return v___x_9521_;
}
pub unsafe fn l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector___redArg___lam__3___boxed(
    mut v___f_9522_: *mut LeanObject,
    mut v___f_9523_: *mut LeanObject,
    mut v___y_9524_: *mut LeanObject,
    mut v___y_9525_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_9526_: *mut LeanObject = core::ptr::null_mut();
    v_res_9526_ =
        l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector___redArg___lam__3(
            v___f_9522_,
            v___f_9523_,
            v___y_9524_,
        );
    lean_dec(v___y_9524_);
    return v_res_9526_;
}
pub unsafe fn l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector___redArg___lam__4(
    mut v_producers_9527_: *mut LeanObject,
    mut v_capacity_9528_: *mut LeanObject,
    mut v_buf_9529_: *mut LeanObject,
    mut v_bufCount_9530_: *mut LeanObject,
    mut v_sendIdx_9531_: *mut LeanObject,
    mut v_recvIdx_9532_: *mut LeanObject,
    mut v_closed_9533_: u8,
    mut v___y_9534_: *mut LeanObject,
    mut v_x_9535_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_9537_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9539_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_9540_: u8 = 0;
    let mut v___x_9542_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9543_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_9544_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_9545_: u8 = 0;
    let mut v_a_9546_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9548_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_9549_: u8 = 0;
    let mut v___x_9550_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9551_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9553_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9554_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_9555_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_9556_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_9535_) == 0 {
                    lean_dec(v_recvIdx_9532_);
                    lean_dec(v_sendIdx_9531_);
                    lean_dec(v_bufCount_9530_);
                    lean_dec_ref(v_buf_9529_);
                    lean_dec(v_capacity_9528_);
                    lean_dec_ref(v_producers_9527_);
                    v_a_9537_ = lean_ctor_get(v_x_9535_, 0);
                    v_isSharedCheck_9545_ = (!lean_is_exclusive(v_x_9535_)) as u8;
                    if v_isSharedCheck_9545_ == 0 {
                        v___x_9539_ = v_x_9535_;
                        v_isShared_9540_ = v_isSharedCheck_9545_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_9537_);
                        lean_dec(v_x_9535_);
                        v___x_9539_ = lean_box(0);
                        v_isShared_9540_ = v_isSharedCheck_9545_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_9546_ = lean_ctor_get(v_x_9535_, 0);
                    v_isSharedCheck_9556_ = (!lean_is_exclusive(v_x_9535_)) as u8;
                    if v_isSharedCheck_9556_ == 0 {
                        v___x_9548_ = v_x_9535_;
                        v_isShared_9549_ = v_isSharedCheck_9556_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_9546_);
                        lean_dec(v_x_9535_);
                        v___x_9548_ = lean_box(0);
                        v_isShared_9549_ = v_isSharedCheck_9556_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_9540_ == 0 {
                    v___x_9542_ = v___x_9539_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_9544_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_9544_, 0, v_a_9537_);
                    v___x_9542_ = v_reuseFailAlloc_9544_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_9543_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_9543_, 0, v___x_9542_);
                return v___x_9543_;
            }
            3 => {
                v___x_9550_ = lean_alloc_ctor(0, 7, (1) as u32);
                lean_ctor_set(v___x_9550_, 0, v_producers_9527_);
                lean_ctor_set(v___x_9550_, 1, v_a_9546_);
                lean_ctor_set(v___x_9550_, 2, v_capacity_9528_);
                lean_ctor_set(v___x_9550_, 3, v_buf_9529_);
                lean_ctor_set(v___x_9550_, 4, v_bufCount_9530_);
                lean_ctor_set(v___x_9550_, 5, v_sendIdx_9531_);
                lean_ctor_set(v___x_9550_, 6, v_recvIdx_9532_);
                lean_ctor_set_uint8(
                    v___x_9550_,
                    (core::mem::size_of::<*mut LeanObject>() * 7) as u32,
                    v_closed_9533_,
                );
                v___x_9551_ = lean_st_ref_set(v___y_9534_, v___x_9550_);
                if v_isShared_9549_ == 0 {
                    lean_ctor_set(v___x_9548_, 0, v___x_9551_);
                    v___x_9553_ = v___x_9548_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_9555_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_9555_, 0, v___x_9551_);
                    v___x_9553_ = v_reuseFailAlloc_9555_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_9554_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_9554_, 0, v___x_9553_);
                return v___x_9554_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector___redArg___lam__4___boxed(
    mut v_producers_9557_: *mut LeanObject,
    mut v_capacity_9558_: *mut LeanObject,
    mut v_buf_9559_: *mut LeanObject,
    mut v_bufCount_9560_: *mut LeanObject,
    mut v_sendIdx_9561_: *mut LeanObject,
    mut v_recvIdx_9562_: *mut LeanObject,
    mut v_closed_9563_: *mut LeanObject,
    mut v___y_9564_: *mut LeanObject,
    mut v_x_9565_: *mut LeanObject,
    mut v___y_9566_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_closed_boxed_9567_: u8 = 0;
    let mut v_res_9568_: *mut LeanObject = core::ptr::null_mut();
    v_closed_boxed_9567_ = (lean_unbox(v_closed_9563_) as u8);
    v_res_9568_ =
        l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector___redArg___lam__4(
            v_producers_9557_,
            v_capacity_9558_,
            v_buf_9559_,
            v_bufCount_9560_,
            v_sendIdx_9561_,
            v_recvIdx_9562_,
            v_closed_boxed_9567_,
            v___y_9564_,
            v_x_9565_,
        );
    lean_dec(v___y_9564_);
    return v_res_9568_;
}
pub unsafe fn l_List_filterAuxM___at___00Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_spec__1_spec__1___redArg___lam__0___boxed(
    mut v_tail_9569_: *mut LeanObject,
    mut v_x_9570_: *mut LeanObject,
    mut v_head_9571_: *mut LeanObject,
    mut v_x_9572_: *mut LeanObject,
    mut v___y_9573_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_9574_: *mut LeanObject = core::ptr::null_mut();
    v_res_9574_ = l_List_filterAuxM___at___00Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_spec__1_spec__1___redArg___lam__0(v_tail_9569_, v_x_9570_, v_head_9571_, v_x_9572_);
    return v_res_9574_;
}
pub unsafe fn l_List_filterAuxM___at___00Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_spec__1_spec__1___redArg(
    mut v_x_9575_: *mut LeanObject,
    mut v_x_9576_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_9578_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9579_: *mut LeanObject = core::ptr::null_mut();
    let mut v_head_9580_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_9581_: *mut LeanObject = core::ptr::null_mut();
    let mut v_waiter_9582_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_9583_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_9585_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9586_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9587_: u8 = 0;
    let mut v___x_9588_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9589_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_9590_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9592_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_9593_: u8 = 0;
    let mut v_finished_9594_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9595_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_9596_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9598_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9599_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9600_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9601_: u8 = 0;
    let mut v___x_9602_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_9603_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_9604_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_9575_) == 0 {
                    v___x_9578_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v___x_9578_, 0, v_x_9576_);
                    v___x_9579_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_9579_, 0, v___x_9578_);
                    return v___x_9579_;
                } else {
                    v_head_9580_ = lean_ctor_get(v_x_9575_, 0);
                    lean_inc(v_head_9580_);
                    v_tail_9581_ = lean_ctor_get(v_x_9575_, 1);
                    lean_inc(v_tail_9581_);
                    lean_dec_ref_known(v_x_9575_, 2);
                    v_waiter_9582_ = lean_ctor_get(v_head_9580_, 1);
                    lean_inc(v_waiter_9582_);
                    v___f_9583_ = lean_alloc_closure(l_List_filterAuxM___at___00Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_spec__1_spec__1___redArg___lam__0___boxed as *mut core::ffi::c_void, 5, 3);
                    lean_closure_set(v___f_9583_, 0, v_tail_9581_);
                    lean_closure_set(v___f_9583_, 1, v_x_9576_);
                    lean_closure_set(v___f_9583_, 2, v_head_9580_);
                    if lean_obj_tag(v_waiter_9582_) == 0 {
                        v___x_9589_ = l_List_filterAuxM___at___00Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__3_spec__3___redArg___closed__1;
                        v_val_9585_ = v___x_9589_;
                        state = 1;
                        continue;
                    } else {
                        v_val_9590_ = lean_ctor_get(v_waiter_9582_, 0);
                        v_isSharedCheck_9604_ = (!lean_is_exclusive(v_waiter_9582_)) as u8;
                        if v_isSharedCheck_9604_ == 0 {
                            v___x_9592_ = v_waiter_9582_;
                            v_isShared_9593_ = v_isSharedCheck_9604_;
                            state = 2;
                            continue;
                        } else {
                            lean_inc(v_val_9590_);
                            lean_dec(v_waiter_9582_);
                            v___x_9592_ = lean_box(0);
                            v_isShared_9593_ = v_isSharedCheck_9604_;
                            state = 2;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v___x_9586_ = lean_unsigned_to_nat(0);
                v___x_9587_ = 0;
                v___x_9588_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(
                    lean_box(0),
                    lean_box(0),
                    v___x_9586_,
                    v___x_9587_,
                    v_val_9585_,
                    v___f_9583_,
                );
                return v___x_9588_;
            }
            2 => {
                v_finished_9594_ = lean_ctor_get(v_val_9590_, 0);
                lean_inc(v_finished_9594_);
                lean_dec(v_val_9590_);
                v___x_9595_ = lean_st_ref_get(v_finished_9594_);
                lean_dec(v_finished_9594_);
                v___f_9596_ = l_List_filterAuxM___at___00Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__3_spec__3___redArg___closed__2;
                if v_isShared_9593_ == 0 {
                    lean_ctor_set(v___x_9592_, 0, v___x_9595_);
                    v___x_9598_ = v___x_9592_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_9603_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_9603_, 0, v___x_9595_);
                    v___x_9598_ = v_reuseFailAlloc_9603_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_9599_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_9599_, 0, v___x_9598_);
                v___x_9600_ = lean_unsigned_to_nat(0);
                v___x_9601_ = 0;
                v___x_9602_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(
                    lean_box(0),
                    lean_box(0),
                    v___x_9600_,
                    v___x_9601_,
                    v___x_9599_,
                    v___f_9596_,
                );
                v_val_9585_ = v___x_9602_;
                state = 1;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_filterAuxM___at___00Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_spec__1_spec__1___redArg___lam__0(
    mut v_tail_9605_: *mut LeanObject,
    mut v_x_9606_: *mut LeanObject,
    mut v_head_9607_: *mut LeanObject,
    mut v_x_9608_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_9610_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9612_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_9613_: u8 = 0;
    let mut v___x_9615_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9616_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_9617_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_9618_: u8 = 0;
    let mut v_a_9619_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9620_: u8 = 0;
    let mut v___x_9621_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9622_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9623_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_9608_) == 0 {
                    lean_dec_ref(v_head_9607_);
                    lean_dec(v_x_9606_);
                    lean_dec(v_tail_9605_);
                    v_a_9610_ = lean_ctor_get(v_x_9608_, 0);
                    v_isSharedCheck_9618_ = (!lean_is_exclusive(v_x_9608_)) as u8;
                    if v_isSharedCheck_9618_ == 0 {
                        v___x_9612_ = v_x_9608_;
                        v_isShared_9613_ = v_isSharedCheck_9618_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_9610_);
                        lean_dec(v_x_9608_);
                        v___x_9612_ = lean_box(0);
                        v_isShared_9613_ = v_isSharedCheck_9618_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_9619_ = lean_ctor_get(v_x_9608_, 0);
                    lean_inc(v_a_9619_);
                    lean_dec_ref_known(v_x_9608_, 1);
                    v___x_9620_ = (lean_unbox(v_a_9619_) as u8);
                    lean_dec(v_a_9619_);
                    if v___x_9620_ == 0 {
                        lean_dec_ref(v_head_9607_);
                        v___x_9621_ = l_List_filterAuxM___at___00Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_spec__1_spec__1___redArg(v_tail_9605_, v_x_9606_);
                        return v___x_9621_;
                    } else {
                        v___x_9622_ = lean_alloc_ctor(1, 2, (0) as u32);
                        lean_ctor_set(v___x_9622_, 0, v_head_9607_);
                        lean_ctor_set(v___x_9622_, 1, v_x_9606_);
                        v___x_9623_ = l_List_filterAuxM___at___00Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_spec__1_spec__1___redArg(v_tail_9605_, v___x_9622_);
                        return v___x_9623_;
                    }
                }
            }
            1 => {
                if v_isShared_9613_ == 0 {
                    v___x_9615_ = v___x_9612_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_9617_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_9617_, 0, v_a_9610_);
                    v___x_9615_ = v_reuseFailAlloc_9617_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_9616_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_9616_, 0, v___x_9615_);
                return v___x_9616_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_filterAuxM___at___00Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_spec__1_spec__1___redArg___boxed(
    mut v_x_9624_: *mut LeanObject,
    mut v_x_9625_: *mut LeanObject,
    mut v___y_9626_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_9627_: *mut LeanObject = core::ptr::null_mut();
    v_res_9627_ = l_List_filterAuxM___at___00Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_spec__1_spec__1___redArg(v_x_9624_, v_x_9625_);
    return v_res_9627_;
}
pub unsafe fn l_Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_spec__1___redArg___lam__0(
    mut v_x_9628_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_9630_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_9631_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9633_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_9634_: u8 = 0;
    let mut v___x_9635_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9637_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9638_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_9639_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_9640_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_9628_) == 0 {
                    v___x_9630_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_9630_, 0, v_x_9628_);
                    return v___x_9630_;
                } else {
                    v_a_9631_ = lean_ctor_get(v_x_9628_, 0);
                    v_isSharedCheck_9640_ = (!lean_is_exclusive(v_x_9628_)) as u8;
                    if v_isSharedCheck_9640_ == 0 {
                        v___x_9633_ = v_x_9628_;
                        v_isShared_9634_ = v_isSharedCheck_9640_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_9631_);
                        lean_dec(v_x_9628_);
                        v___x_9633_ = lean_box(0);
                        v_isShared_9634_ = v_isSharedCheck_9640_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_9635_ = l_List_reverse___redArg(v_a_9631_);
                if v_isShared_9634_ == 0 {
                    lean_ctor_set(v___x_9633_, 0, v___x_9635_);
                    v___x_9637_ = v___x_9633_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_9639_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_9639_, 0, v___x_9635_);
                    v___x_9637_ = v_reuseFailAlloc_9639_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_9638_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_9638_, 0, v___x_9637_);
                return v___x_9638_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_spec__1___redArg___lam__0___boxed(
    mut v_x_9641_: *mut LeanObject,
    mut v___y_9642_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_9643_: *mut LeanObject = core::ptr::null_mut();
    v_res_9643_ = l_Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_spec__1___redArg___lam__0(v_x_9641_);
    return v_res_9643_;
}
pub unsafe fn l_Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_spec__1___redArg___lam__2(
    mut v_a_9644_: *mut LeanObject,
    mut v___x_9645_: *mut LeanObject,
    mut v_x_9646_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_9648_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9650_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_9651_: u8 = 0;
    let mut v___x_9653_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9654_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_9655_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_9656_: u8 = 0;
    let mut v_a_9657_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9659_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_9660_: u8 = 0;
    let mut v___x_9661_: u8 = 0;
    let mut v___x_9662_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9664_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9665_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_9666_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9667_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9668_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9670_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9671_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_9672_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_9673_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_9646_) == 0 {
                    lean_dec(v___x_9645_);
                    lean_dec(v_a_9644_);
                    v_a_9648_ = lean_ctor_get(v_x_9646_, 0);
                    v_isSharedCheck_9656_ = (!lean_is_exclusive(v_x_9646_)) as u8;
                    if v_isSharedCheck_9656_ == 0 {
                        v___x_9650_ = v_x_9646_;
                        v_isShared_9651_ = v_isSharedCheck_9656_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_9648_);
                        lean_dec(v_x_9646_);
                        v___x_9650_ = lean_box(0);
                        v_isShared_9651_ = v_isSharedCheck_9656_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_9657_ = lean_ctor_get(v_x_9646_, 0);
                    v_isSharedCheck_9673_ = (!lean_is_exclusive(v_x_9646_)) as u8;
                    if v_isSharedCheck_9673_ == 0 {
                        v___x_9659_ = v_x_9646_;
                        v_isShared_9660_ = v_isSharedCheck_9673_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_9657_);
                        lean_dec(v_x_9646_);
                        v___x_9659_ = lean_box(0);
                        v_isShared_9660_ = v_isSharedCheck_9673_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_9651_ == 0 {
                    v___x_9653_ = v___x_9650_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_9655_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_9655_, 0, v_a_9648_);
                    v___x_9653_ = v_reuseFailAlloc_9655_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_9654_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_9654_, 0, v___x_9653_);
                return v___x_9654_;
            }
            3 => {
                v___x_9661_ = l_List_isEmpty___redArg(v_a_9644_);
                if v___x_9661_ == 0 {
                    lean_dec(v___x_9645_);
                    v___x_9662_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v___x_9662_, 0, v_a_9657_);
                    lean_ctor_set(v___x_9662_, 1, v_a_9644_);
                    if v_isShared_9660_ == 0 {
                        lean_ctor_set(v___x_9659_, 0, v___x_9662_);
                        v___x_9664_ = v___x_9659_;
                        state = 4;
                        continue;
                    } else {
                        v_reuseFailAlloc_9666_ = lean_alloc_ctor(1, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_9666_, 0, v___x_9662_);
                        v___x_9664_ = v_reuseFailAlloc_9666_;
                        state = 4;
                        continue;
                    }
                } else {
                    lean_dec(v_a_9644_);
                    v___x_9667_ = l_List_reverse___redArg(v_a_9657_);
                    v___x_9668_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v___x_9668_, 0, v___x_9645_);
                    lean_ctor_set(v___x_9668_, 1, v___x_9667_);
                    if v_isShared_9660_ == 0 {
                        lean_ctor_set(v___x_9659_, 0, v___x_9668_);
                        v___x_9670_ = v___x_9659_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_9672_ = lean_alloc_ctor(1, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_9672_, 0, v___x_9668_);
                        v___x_9670_ = v_reuseFailAlloc_9672_;
                        state = 5;
                        continue;
                    }
                }
            }
            4 => {
                v___x_9665_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_9665_, 0, v___x_9664_);
                return v___x_9665_;
            }
            5 => {
                v___x_9671_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_9671_, 0, v___x_9670_);
                return v___x_9671_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_spec__1___redArg___lam__2___boxed(
    mut v_a_9674_: *mut LeanObject,
    mut v___x_9675_: *mut LeanObject,
    mut v_x_9676_: *mut LeanObject,
    mut v___y_9677_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_9678_: *mut LeanObject = core::ptr::null_mut();
    v_res_9678_ = l_Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_spec__1___redArg___lam__2(v_a_9674_, v___x_9675_, v_x_9676_);
    return v_res_9678_;
}
pub unsafe fn l_Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_spec__1___redArg___lam__1(
    mut v_eList_9679_: *mut LeanObject,
    mut v___x_9680_: *mut LeanObject,
    mut v___f_9681_: *mut LeanObject,
    mut v_x_9682_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_9684_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9686_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_9687_: u8 = 0;
    let mut v___x_9689_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9690_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_9691_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_9692_: u8 = 0;
    let mut v_a_9693_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9694_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9695_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9696_: u8 = 0;
    let mut v___x_9697_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_9698_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9699_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_9682_) == 0 {
                    lean_dec_ref(v___f_9681_);
                    lean_dec(v___x_9680_);
                    lean_dec(v_eList_9679_);
                    v_a_9684_ = lean_ctor_get(v_x_9682_, 0);
                    v_isSharedCheck_9692_ = (!lean_is_exclusive(v_x_9682_)) as u8;
                    if v_isSharedCheck_9692_ == 0 {
                        v___x_9686_ = v_x_9682_;
                        v_isShared_9687_ = v_isSharedCheck_9692_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_9684_);
                        lean_dec(v_x_9682_);
                        v___x_9686_ = lean_box(0);
                        v_isShared_9687_ = v_isSharedCheck_9692_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_9693_ = lean_ctor_get(v_x_9682_, 0);
                    lean_inc(v_a_9693_);
                    lean_dec_ref_known(v_x_9682_, 1);
                    lean_inc(v___x_9680_);
                    v___x_9694_ = l_List_filterAuxM___at___00Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_spec__1_spec__1___redArg(v_eList_9679_, v___x_9680_);
                    v___x_9695_ = lean_unsigned_to_nat(0);
                    v___x_9696_ = 0;
                    v___x_9697_ =
                        l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(
                            lean_box(0),
                            lean_box(0),
                            v___x_9695_,
                            v___x_9696_,
                            v___x_9694_,
                            v___f_9681_,
                        );
                    v___f_9698_ = lean_alloc_closure(l_Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_spec__1___redArg___lam__2___boxed as *mut core::ffi::c_void, 4, 2);
                    lean_closure_set(v___f_9698_, 0, v_a_9693_);
                    lean_closure_set(v___f_9698_, 1, v___x_9680_);
                    v___x_9699_ =
                        l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(
                            lean_box(0),
                            lean_box(0),
                            v___x_9695_,
                            v___x_9696_,
                            v___x_9697_,
                            v___f_9698_,
                        );
                    return v___x_9699_;
                }
            }
            1 => {
                if v_isShared_9687_ == 0 {
                    v___x_9689_ = v___x_9686_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_9691_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_9691_, 0, v_a_9684_);
                    v___x_9689_ = v_reuseFailAlloc_9691_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_9690_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_9690_, 0, v___x_9689_);
                return v___x_9690_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_spec__1___redArg___lam__1___boxed(
    mut v_eList_9700_: *mut LeanObject,
    mut v___x_9701_: *mut LeanObject,
    mut v___f_9702_: *mut LeanObject,
    mut v_x_9703_: *mut LeanObject,
    mut v___y_9704_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_9705_: *mut LeanObject = core::ptr::null_mut();
    v_res_9705_ = l_Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_spec__1___redArg___lam__1(v_eList_9700_, v___x_9701_, v___f_9702_, v_x_9703_);
    return v_res_9705_;
}
pub unsafe fn l_Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_spec__1___redArg(
    mut v_q_9707_: *mut LeanObject,
    mut v___y_9708_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_eList_9710_: *mut LeanObject = core::ptr::null_mut();
    let mut v_dList_9711_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9712_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9713_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_9714_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9715_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9716_: u8 = 0;
    let mut v___x_9717_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_9718_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9719_: *mut LeanObject = core::ptr::null_mut();
    v_eList_9710_ = lean_ctor_get(v_q_9707_, 0);
    lean_inc(v_eList_9710_);
    v_dList_9711_ = lean_ctor_get(v_q_9707_, 1);
    lean_inc(v_dList_9711_);
    lean_dec_ref(v_q_9707_);
    v___x_9712_ = lean_box(0);
    v___x_9713_ = l_List_filterAuxM___at___00Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_spec__1_spec__1___redArg(v_dList_9711_, v___x_9712_);
    v___f_9714_ = l_Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_spec__1___redArg___closed__0;
    v___x_9715_ = lean_unsigned_to_nat(0);
    v___x_9716_ = 0;
    v___x_9717_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(
        lean_box(0),
        lean_box(0),
        v___x_9715_,
        v___x_9716_,
        v___x_9713_,
        v___f_9714_,
    );
    v___f_9718_ = lean_alloc_closure(l_Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_spec__1___redArg___lam__1___boxed as *mut core::ffi::c_void, 5, 3);
    lean_closure_set(v___f_9718_, 0, v_eList_9710_);
    lean_closure_set(v___f_9718_, 1, v___x_9712_);
    lean_closure_set(v___f_9718_, 2, v___f_9714_);
    v___x_9719_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(
        lean_box(0),
        lean_box(0),
        v___x_9715_,
        v___x_9716_,
        v___x_9717_,
        v___f_9718_,
    );
    return v___x_9719_;
}
pub unsafe fn l_Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_spec__1___redArg___boxed(
    mut v_q_9720_: *mut LeanObject,
    mut v___y_9721_: *mut LeanObject,
    mut v___y_9722_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_9723_: *mut LeanObject = core::ptr::null_mut();
    v_res_9723_ = l_Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_spec__1___redArg(v_q_9720_, v___y_9721_);
    lean_dec(v___y_9721_);
    return v_res_9723_;
}
pub unsafe fn l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector___redArg___lam__5(
    mut v___y_9724_: *mut LeanObject,
    mut v_x_9725_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_9727_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9729_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_9730_: u8 = 0;
    let mut v___x_9732_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9733_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_9734_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_9735_: u8 = 0;
    let mut v_a_9736_: *mut LeanObject = core::ptr::null_mut();
    let mut v_producers_9737_: *mut LeanObject = core::ptr::null_mut();
    let mut v_consumers_9738_: *mut LeanObject = core::ptr::null_mut();
    let mut v_capacity_9739_: *mut LeanObject = core::ptr::null_mut();
    let mut v_buf_9740_: *mut LeanObject = core::ptr::null_mut();
    let mut v_bufCount_9741_: *mut LeanObject = core::ptr::null_mut();
    let mut v_sendIdx_9742_: *mut LeanObject = core::ptr::null_mut();
    let mut v_recvIdx_9743_: *mut LeanObject = core::ptr::null_mut();
    let mut v_closed_9744_: u8 = 0;
    let mut v___x_9745_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9746_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_9747_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9748_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9749_: u8 = 0;
    let mut v___x_9750_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_9725_) == 0 {
                    v_a_9727_ = lean_ctor_get(v_x_9725_, 0);
                    v_isSharedCheck_9735_ = (!lean_is_exclusive(v_x_9725_)) as u8;
                    if v_isSharedCheck_9735_ == 0 {
                        v___x_9729_ = v_x_9725_;
                        v_isShared_9730_ = v_isSharedCheck_9735_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_9727_);
                        lean_dec(v_x_9725_);
                        v___x_9729_ = lean_box(0);
                        v_isShared_9730_ = v_isSharedCheck_9735_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_9736_ = lean_ctor_get(v_x_9725_, 0);
                    lean_inc(v_a_9736_);
                    lean_dec_ref_known(v_x_9725_, 1);
                    v_producers_9737_ = lean_ctor_get(v_a_9736_, 0);
                    lean_inc_ref(v_producers_9737_);
                    v_consumers_9738_ = lean_ctor_get(v_a_9736_, 1);
                    lean_inc_ref(v_consumers_9738_);
                    v_capacity_9739_ = lean_ctor_get(v_a_9736_, 2);
                    lean_inc(v_capacity_9739_);
                    v_buf_9740_ = lean_ctor_get(v_a_9736_, 3);
                    lean_inc_ref(v_buf_9740_);
                    v_bufCount_9741_ = lean_ctor_get(v_a_9736_, 4);
                    lean_inc(v_bufCount_9741_);
                    v_sendIdx_9742_ = lean_ctor_get(v_a_9736_, 5);
                    lean_inc(v_sendIdx_9742_);
                    v_recvIdx_9743_ = lean_ctor_get(v_a_9736_, 6);
                    lean_inc(v_recvIdx_9743_);
                    v_closed_9744_ = lean_ctor_get_uint8(
                        v_a_9736_,
                        (core::mem::size_of::<*mut LeanObject>() * 7) as u32,
                    );
                    lean_dec(v_a_9736_);
                    v___x_9745_ = l_Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_spec__1___redArg(v_consumers_9738_, v___y_9724_);
                    v___x_9746_ = lean_box((v_closed_9744_) as usize);
                    lean_inc(v___y_9724_);
                    v___f_9747_ = lean_alloc_closure(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector___redArg___lam__4___boxed as *mut core::ffi::c_void, 10, 8);
                    lean_closure_set(v___f_9747_, 0, v_producers_9737_);
                    lean_closure_set(v___f_9747_, 1, v_capacity_9739_);
                    lean_closure_set(v___f_9747_, 2, v_buf_9740_);
                    lean_closure_set(v___f_9747_, 3, v_bufCount_9741_);
                    lean_closure_set(v___f_9747_, 4, v_sendIdx_9742_);
                    lean_closure_set(v___f_9747_, 5, v_recvIdx_9743_);
                    lean_closure_set(v___f_9747_, 6, v___x_9746_);
                    lean_closure_set(v___f_9747_, 7, v___y_9724_);
                    v___x_9748_ = lean_unsigned_to_nat(0);
                    v___x_9749_ = 0;
                    v___x_9750_ =
                        l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(
                            lean_box(0),
                            lean_box(0),
                            v___x_9748_,
                            v___x_9749_,
                            v___x_9745_,
                            v___f_9747_,
                        );
                    return v___x_9750_;
                }
            }
            1 => {
                if v_isShared_9730_ == 0 {
                    v___x_9732_ = v___x_9729_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_9734_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_9734_, 0, v_a_9727_);
                    v___x_9732_ = v_reuseFailAlloc_9734_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_9733_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_9733_, 0, v___x_9732_);
                return v___x_9733_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector___redArg___lam__5___boxed(
    mut v___y_9751_: *mut LeanObject,
    mut v_x_9752_: *mut LeanObject,
    mut v___y_9753_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_9754_: *mut LeanObject = core::ptr::null_mut();
    v_res_9754_ =
        l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector___redArg___lam__5(
            v___y_9751_,
            v_x_9752_,
        );
    lean_dec(v___y_9751_);
    return v_res_9754_;
}
pub unsafe fn l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector___redArg___lam__6(
    mut v___y_9755_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_9757_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_9758_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9759_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9760_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9761_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9762_: u8 = 0;
    let mut v___x_9763_: *mut LeanObject = core::ptr::null_mut();
    v___x_9757_ = lean_st_ref_get(v___y_9755_);
    lean_inc(v___y_9755_);
    v___f_9758_ = lean_alloc_closure(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector___redArg___lam__5___boxed as *mut core::ffi::c_void, 3, 1);
    lean_closure_set(v___f_9758_, 0, v___y_9755_);
    v___x_9759_ = lean_alloc_ctor(1, 1, (0) as u32);
    lean_ctor_set(v___x_9759_, 0, v___x_9757_);
    v___x_9760_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_9760_, 0, v___x_9759_);
    v___x_9761_ = lean_unsigned_to_nat(0);
    v___x_9762_ = 0;
    v___x_9763_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(
        lean_box(0),
        lean_box(0),
        v___x_9761_,
        v___x_9762_,
        v___x_9760_,
        v___f_9758_,
    );
    return v___x_9763_;
}
pub unsafe fn l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector___redArg___lam__6___boxed(
    mut v___y_9764_: *mut LeanObject,
    mut v___y_9765_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_9766_: *mut LeanObject = core::ptr::null_mut();
    v_res_9766_ =
        l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector___redArg___lam__6(
            v___y_9764_,
        );
    lean_dec(v___y_9764_);
    return v_res_9766_;
}
pub unsafe fn l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector___redArg(
    mut v_ch_9772_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_9773_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_9774_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_9775_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9776_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9777_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9778_: *mut LeanObject = core::ptr::null_mut();
    lean_inc_ref_n(v_ch_9772_, 2);
    v___f_9773_ = lean_alloc_closure(l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector___redArg___lam__1___boxed as *mut core::ffi::c_void, 3, 1);
    lean_closure_set(v___f_9773_, 0, v_ch_9772_);
    v___f_9774_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector___redArg___closed__1;
    v___f_9775_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector___redArg___closed__2;
    v___x_9776_ = lean_alloc_closure(l_Std_Mutex_atomically___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__2___boxed as *mut core::ffi::c_void, 5, 4);
    lean_closure_set(v___x_9776_, 0, lean_box(0));
    lean_closure_set(v___x_9776_, 1, lean_box(0));
    lean_closure_set(v___x_9776_, 2, v_ch_9772_);
    lean_closure_set(v___x_9776_, 3, v___f_9774_);
    v___x_9777_ = lean_alloc_closure(l_Std_Mutex_atomically___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector_spec__2___boxed as *mut core::ffi::c_void, 5, 4);
    lean_closure_set(v___x_9777_, 0, lean_box(0));
    lean_closure_set(v___x_9777_, 1, lean_box(0));
    lean_closure_set(v___x_9777_, 2, v_ch_9772_);
    lean_closure_set(v___x_9777_, 3, v___f_9775_);
    v___x_9778_ = lean_alloc_ctor(0, 3, (0) as u32);
    lean_ctor_set(v___x_9778_, 0, v___x_9776_);
    lean_ctor_set(v___x_9778_, 1, v___f_9773_);
    lean_ctor_set(v___x_9778_, 2, v___x_9777_);
    return v___x_9778_;
}
pub unsafe fn l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector(
    mut v_00_u03b1_9779_: *mut LeanObject,
    mut v_ch_9780_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_9781_: *mut LeanObject = core::ptr::null_mut();
    v___x_9781_ =
        l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector___redArg(
            v_ch_9780_,
        );
    return v___x_9781_;
}
pub unsafe fn l_Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_spec__1(
    mut v_00_u03b1_9782_: *mut LeanObject,
    mut v_q_9783_: *mut LeanObject,
    mut v___y_9784_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_9786_: *mut LeanObject = core::ptr::null_mut();
    v___x_9786_ = l_Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_spec__1___redArg(v_q_9783_, v___y_9784_);
    return v___x_9786_;
}
pub unsafe fn l_Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_spec__1___boxed(
    mut v_00_u03b1_9787_: *mut LeanObject,
    mut v_q_9788_: *mut LeanObject,
    mut v___y_9789_: *mut LeanObject,
    mut v___y_9790_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_9791_: *mut LeanObject = core::ptr::null_mut();
    v_res_9791_ = l_Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_spec__1(v_00_u03b1_9787_, v_q_9788_, v___y_9789_);
    lean_dec(v___y_9789_);
    return v_res_9791_;
}
pub unsafe fn l_List_filterAuxM___at___00Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_spec__1_spec__1(
    mut v_00_u03b1_9792_: *mut LeanObject,
    mut v_x_9793_: *mut LeanObject,
    mut v_x_9794_: *mut LeanObject,
    mut v___y_9795_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_9797_: *mut LeanObject = core::ptr::null_mut();
    v___x_9797_ = l_List_filterAuxM___at___00Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_spec__1_spec__1___redArg(v_x_9793_, v_x_9794_);
    return v___x_9797_;
}
pub unsafe fn l_List_filterAuxM___at___00Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_spec__1_spec__1___boxed(
    mut v_00_u03b1_9798_: *mut LeanObject,
    mut v_x_9799_: *mut LeanObject,
    mut v_x_9800_: *mut LeanObject,
    mut v___y_9801_: *mut LeanObject,
    mut v___y_9802_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_9803_: *mut LeanObject = core::ptr::null_mut();
    v_res_9803_ = l_List_filterAuxM___at___00Std_Queue_filterM___at___00__private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector_spec__1_spec__1(v_00_u03b1_9798_, v_x_9799_, v_x_9800_, v___y_9801_);
    lean_dec(v___y_9801_);
    return v_res_9803_;
}
pub unsafe fn l_Std_CloseableChannel_Flavors_ctorIdx___redArg(
    mut v_x_9804_: *mut LeanObject,
) -> *mut LeanObject {
    match lean_obj_tag(v_x_9804_) {
        0 => {
            let mut v___x_9805_: *mut LeanObject = core::ptr::null_mut();
            v___x_9805_ = lean_unsigned_to_nat(0);
            return v___x_9805_;
        }
        1 => {
            let mut v___x_9806_: *mut LeanObject = core::ptr::null_mut();
            v___x_9806_ = lean_unsigned_to_nat(1);
            return v___x_9806_;
        }
        _ => {
            let mut v___x_9807_: *mut LeanObject = core::ptr::null_mut();
            v___x_9807_ = lean_unsigned_to_nat(2);
            return v___x_9807_;
        }
    }
}
pub unsafe fn l_Std_CloseableChannel_Flavors_ctorIdx___redArg___boxed(
    mut v_x_9808_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_9809_: *mut LeanObject = core::ptr::null_mut();
    v_res_9809_ = l_Std_CloseableChannel_Flavors_ctorIdx___redArg(v_x_9808_);
    lean_dec_ref(v_x_9808_);
    return v_res_9809_;
}
pub unsafe fn l_Std_CloseableChannel_Flavors_ctorIdx(
    mut v_00_u03b1_9810_: *mut LeanObject,
    mut v_x_9811_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_9812_: *mut LeanObject = core::ptr::null_mut();
    v___x_9812_ = l_Std_CloseableChannel_Flavors_ctorIdx___redArg(v_x_9811_);
    return v___x_9812_;
}
pub unsafe fn l_Std_CloseableChannel_Flavors_ctorIdx___boxed(
    mut v_00_u03b1_9813_: *mut LeanObject,
    mut v_x_9814_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_9815_: *mut LeanObject = core::ptr::null_mut();
    v_res_9815_ = l_Std_CloseableChannel_Flavors_ctorIdx(v_00_u03b1_9813_, v_x_9814_);
    lean_dec_ref(v_x_9814_);
    return v_res_9815_;
}
pub unsafe fn l_Std_CloseableChannel_Flavors_ctorElim___redArg(
    mut v_t_9816_: *mut LeanObject,
    mut v_k_9817_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_ch_9818_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9819_: *mut LeanObject = core::ptr::null_mut();
    v_ch_9818_ = lean_ctor_get(v_t_9816_, 0);
    lean_inc_ref(v_ch_9818_);
    lean_dec_ref(v_t_9816_);
    v___x_9819_ = lean_apply_1(v_k_9817_, v_ch_9818_);
    return v___x_9819_;
}
pub unsafe fn l_Std_CloseableChannel_Flavors_ctorElim(
    mut v_00_u03b1_9820_: *mut LeanObject,
    mut v_motive_9821_: *mut LeanObject,
    mut v_ctorIdx_9822_: *mut LeanObject,
    mut v_t_9823_: *mut LeanObject,
    mut v_h_9824_: *mut LeanObject,
    mut v_k_9825_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_9826_: *mut LeanObject = core::ptr::null_mut();
    v___x_9826_ = l_Std_CloseableChannel_Flavors_ctorElim___redArg(v_t_9823_, v_k_9825_);
    return v___x_9826_;
}
pub unsafe fn l_Std_CloseableChannel_Flavors_ctorElim___boxed(
    mut v_00_u03b1_9827_: *mut LeanObject,
    mut v_motive_9828_: *mut LeanObject,
    mut v_ctorIdx_9829_: *mut LeanObject,
    mut v_t_9830_: *mut LeanObject,
    mut v_h_9831_: *mut LeanObject,
    mut v_k_9832_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_9833_: *mut LeanObject = core::ptr::null_mut();
    v_res_9833_ = l_Std_CloseableChannel_Flavors_ctorElim(
        v_00_u03b1_9827_,
        v_motive_9828_,
        v_ctorIdx_9829_,
        v_t_9830_,
        v_h_9831_,
        v_k_9832_,
    );
    lean_dec(v_ctorIdx_9829_);
    return v_res_9833_;
}
pub unsafe fn l_Std_CloseableChannel_Flavors_unbounded_elim___redArg(
    mut v_t_9834_: *mut LeanObject,
    mut v___private_Std_Sync_Channel_0__Std_CloseableChannel_Flavors_unbounded_9835_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_9836_: *mut LeanObject = core::ptr::null_mut();
    v___x_9836_ = l_Std_CloseableChannel_Flavors_ctorElim___redArg(
        v_t_9834_,
        v___private_Std_Sync_Channel_0__Std_CloseableChannel_Flavors_unbounded_9835_,
    );
    return v___x_9836_;
}
pub unsafe fn l_Std_CloseableChannel_Flavors_unbounded_elim(
    mut v_00_u03b1_9837_: *mut LeanObject,
    mut v_motive_9838_: *mut LeanObject,
    mut v_t_9839_: *mut LeanObject,
    mut v_h_9840_: *mut LeanObject,
    mut v___private_Std_Sync_Channel_0__Std_CloseableChannel_Flavors_unbounded_9841_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_9842_: *mut LeanObject = core::ptr::null_mut();
    v___x_9842_ = l_Std_CloseableChannel_Flavors_ctorElim___redArg(
        v_t_9839_,
        v___private_Std_Sync_Channel_0__Std_CloseableChannel_Flavors_unbounded_9841_,
    );
    return v___x_9842_;
}
pub unsafe fn l_Std_CloseableChannel_Flavors_zero_elim___redArg(
    mut v_t_9843_: *mut LeanObject,
    mut v___private_Std_Sync_Channel_0__Std_CloseableChannel_Flavors_zero_9844_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_9845_: *mut LeanObject = core::ptr::null_mut();
    v___x_9845_ = l_Std_CloseableChannel_Flavors_ctorElim___redArg(
        v_t_9843_,
        v___private_Std_Sync_Channel_0__Std_CloseableChannel_Flavors_zero_9844_,
    );
    return v___x_9845_;
}
pub unsafe fn l_Std_CloseableChannel_Flavors_zero_elim(
    mut v_00_u03b1_9846_: *mut LeanObject,
    mut v_motive_9847_: *mut LeanObject,
    mut v_t_9848_: *mut LeanObject,
    mut v_h_9849_: *mut LeanObject,
    mut v___private_Std_Sync_Channel_0__Std_CloseableChannel_Flavors_zero_9850_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_9851_: *mut LeanObject = core::ptr::null_mut();
    v___x_9851_ = l_Std_CloseableChannel_Flavors_ctorElim___redArg(
        v_t_9848_,
        v___private_Std_Sync_Channel_0__Std_CloseableChannel_Flavors_zero_9850_,
    );
    return v___x_9851_;
}
pub unsafe fn l_Std_CloseableChannel_Flavors_bounded_elim___redArg(
    mut v_t_9852_: *mut LeanObject,
    mut v___private_Std_Sync_Channel_0__Std_CloseableChannel_Flavors_bounded_9853_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_9854_: *mut LeanObject = core::ptr::null_mut();
    v___x_9854_ = l_Std_CloseableChannel_Flavors_ctorElim___redArg(
        v_t_9852_,
        v___private_Std_Sync_Channel_0__Std_CloseableChannel_Flavors_bounded_9853_,
    );
    return v___x_9854_;
}
pub unsafe fn l_Std_CloseableChannel_Flavors_bounded_elim(
    mut v_00_u03b1_9855_: *mut LeanObject,
    mut v_motive_9856_: *mut LeanObject,
    mut v_t_9857_: *mut LeanObject,
    mut v_h_9858_: *mut LeanObject,
    mut v___private_Std_Sync_Channel_0__Std_CloseableChannel_Flavors_bounded_9859_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_9860_: *mut LeanObject = core::ptr::null_mut();
    v___x_9860_ = l_Std_CloseableChannel_Flavors_ctorElim___redArg(
        v_t_9857_,
        v___private_Std_Sync_Channel_0__Std_CloseableChannel_Flavors_bounded_9859_,
    );
    return v___x_9860_;
}
pub unsafe fn l_Std_CloseableChannel_new___redArg(
    mut v_capacity_9861_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_9863_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9864_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_9865_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9867_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_9868_: u8 = 0;
    let mut v_zero_9869_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isZero_9870_: u8 = 0;
    let mut v___x_9871_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9873_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_9874_: *mut LeanObject = core::ptr::null_mut();
    let mut v_one_9875_: *mut LeanObject = core::ptr::null_mut();
    let mut v_n_9876_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9877_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9878_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_9880_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_9881_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_9882_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_capacity_9861_) == 0 {
                    v___x_9863_ =
                        l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_new___redArg(
                        );
                    v___x_9864_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_9864_, 0, v___x_9863_);
                    return v___x_9864_;
                } else {
                    v_val_9865_ = lean_ctor_get(v_capacity_9861_, 0);
                    v_isSharedCheck_9882_ = (!lean_is_exclusive(v_capacity_9861_)) as u8;
                    if v_isSharedCheck_9882_ == 0 {
                        v___x_9867_ = v_capacity_9861_;
                        v_isShared_9868_ = v_isSharedCheck_9882_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_val_9865_);
                        lean_dec(v_capacity_9861_);
                        v___x_9867_ = lean_box(0);
                        v_isShared_9868_ = v_isSharedCheck_9882_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_zero_9869_ = lean_unsigned_to_nat(0);
                v_isZero_9870_ = lean_nat_dec_eq(v_val_9865_, v_zero_9869_);
                if v_isZero_9870_ == 1 {
                    lean_dec(v_val_9865_);
                    v___x_9871_ =
                        l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_new___redArg();
                    if v_isShared_9868_ == 0 {
                        lean_ctor_set(v___x_9867_, 0, v___x_9871_);
                        v___x_9873_ = v___x_9867_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_9874_ = lean_alloc_ctor(1, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_9874_, 0, v___x_9871_);
                        v___x_9873_ = v_reuseFailAlloc_9874_;
                        state = 2;
                        continue;
                    }
                } else {
                    v_one_9875_ = lean_unsigned_to_nat(1);
                    v_n_9876_ = lean_nat_sub(v_val_9865_, v_one_9875_);
                    lean_dec(v_val_9865_);
                    v___x_9877_ = lean_nat_add(v_n_9876_, v_one_9875_);
                    lean_dec(v_n_9876_);
                    v___x_9878_ =
                        l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_new___redArg(
                            v___x_9877_,
                        );
                    if v_isShared_9868_ == 0 {
                        lean_ctor_set_tag(v___x_9867_, 2);
                        lean_ctor_set(v___x_9867_, 0, v___x_9878_);
                        v___x_9880_ = v___x_9867_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_9881_ = lean_alloc_ctor(2, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_9881_, 0, v___x_9878_);
                        v___x_9880_ = v_reuseFailAlloc_9881_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_9873_;
            }
            3 => {
                return v___x_9880_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_CloseableChannel_new___redArg___boxed(
    mut v_capacity_9883_: *mut LeanObject,
    mut v_a_9884_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_9885_: *mut LeanObject = core::ptr::null_mut();
    v_res_9885_ = l_Std_CloseableChannel_new___redArg(v_capacity_9883_);
    return v_res_9885_;
}
pub unsafe fn l_Std_CloseableChannel_new(
    mut v_00_u03b1_9886_: *mut LeanObject,
    mut v_capacity_9887_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_9889_: *mut LeanObject = core::ptr::null_mut();
    v___x_9889_ = l_Std_CloseableChannel_new___redArg(v_capacity_9887_);
    return v___x_9889_;
}
pub unsafe fn l_Std_CloseableChannel_new___boxed(
    mut v_00_u03b1_9890_: *mut LeanObject,
    mut v_capacity_9891_: *mut LeanObject,
    mut v_a_9892_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_9893_: *mut LeanObject = core::ptr::null_mut();
    v_res_9893_ = l_Std_CloseableChannel_new(v_00_u03b1_9890_, v_capacity_9891_);
    return v_res_9893_;
}
pub unsafe fn l_Std_CloseableChannel_trySend___redArg(
    mut v_ch_9894_: *mut LeanObject,
    mut v_v_9895_: *mut LeanObject,
) -> u8 {
    match lean_obj_tag(v_ch_9894_) {
        0 => {
            let mut v_ch_9897_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_9898_: u8 = 0;
            v_ch_9897_ = lean_ctor_get(v_ch_9894_, 0);
            lean_inc_ref(v_ch_9897_);
            lean_dec_ref_known(v_ch_9894_, 1);
            v___x_9898_ =
                l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_trySend___redArg(
                    v_ch_9897_, v_v_9895_,
                );
            return v___x_9898_;
        }
        1 => {
            let mut v_ch_9899_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_9900_: u8 = 0;
            v_ch_9899_ = lean_ctor_get(v_ch_9894_, 0);
            lean_inc_ref(v_ch_9899_);
            lean_dec_ref_known(v_ch_9894_, 1);
            v___x_9900_ =
                l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_trySend___redArg(
                    v_ch_9899_, v_v_9895_,
                );
            return v___x_9900_;
        }
        _ => {
            let mut v_ch_9901_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_9902_: u8 = 0;
            v_ch_9901_ = lean_ctor_get(v_ch_9894_, 0);
            lean_inc_ref(v_ch_9901_);
            lean_dec_ref_known(v_ch_9894_, 1);
            v___x_9902_ =
                l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_trySend___redArg(
                    v_ch_9901_, v_v_9895_,
                );
            return v___x_9902_;
        }
    }
}
pub unsafe fn l_Std_CloseableChannel_trySend___redArg___boxed(
    mut v_ch_9903_: *mut LeanObject,
    mut v_v_9904_: *mut LeanObject,
    mut v_a_9905_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_9906_: u8 = 0;
    let mut v_r_9907_: *mut LeanObject = core::ptr::null_mut();
    v_res_9906_ = l_Std_CloseableChannel_trySend___redArg(v_ch_9903_, v_v_9904_);
    v_r_9907_ = lean_box((v_res_9906_) as usize);
    return v_r_9907_;
}
pub unsafe fn l_Std_CloseableChannel_trySend(
    mut v_00_u03b1_9908_: *mut LeanObject,
    mut v_ch_9909_: *mut LeanObject,
    mut v_v_9910_: *mut LeanObject,
) -> u8 {
    let mut v___x_9912_: u8 = 0;
    v___x_9912_ = l_Std_CloseableChannel_trySend___redArg(v_ch_9909_, v_v_9910_);
    return v___x_9912_;
}
pub unsafe fn l_Std_CloseableChannel_trySend___boxed(
    mut v_00_u03b1_9913_: *mut LeanObject,
    mut v_ch_9914_: *mut LeanObject,
    mut v_v_9915_: *mut LeanObject,
    mut v_a_9916_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_9917_: u8 = 0;
    let mut v_r_9918_: *mut LeanObject = core::ptr::null_mut();
    v_res_9917_ = l_Std_CloseableChannel_trySend(v_00_u03b1_9913_, v_ch_9914_, v_v_9915_);
    v_r_9918_ = lean_box((v_res_9917_) as usize);
    return v_r_9918_;
}
pub unsafe fn l_Std_CloseableChannel_send___redArg(
    mut v_ch_9919_: *mut LeanObject,
    mut v_v_9920_: *mut LeanObject,
) -> *mut LeanObject {
    match lean_obj_tag(v_ch_9919_) {
        0 => {
            let mut v_ch_9922_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_9923_: *mut LeanObject = core::ptr::null_mut();
            v_ch_9922_ = lean_ctor_get(v_ch_9919_, 0);
            lean_inc_ref(v_ch_9922_);
            lean_dec_ref_known(v_ch_9919_, 1);
            v___x_9923_ =
                l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_send___redArg(
                    v_ch_9922_, v_v_9920_,
                );
            return v___x_9923_;
        }
        1 => {
            let mut v_ch_9924_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_9925_: *mut LeanObject = core::ptr::null_mut();
            v_ch_9924_ = lean_ctor_get(v_ch_9919_, 0);
            lean_inc_ref(v_ch_9924_);
            lean_dec_ref_known(v_ch_9919_, 1);
            v___x_9925_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_send___redArg(
                v_ch_9924_, v_v_9920_,
            );
            return v___x_9925_;
        }
        _ => {
            let mut v_ch_9926_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_9927_: *mut LeanObject = core::ptr::null_mut();
            v_ch_9926_ = lean_ctor_get(v_ch_9919_, 0);
            lean_inc_ref(v_ch_9926_);
            lean_dec_ref_known(v_ch_9919_, 1);
            v___x_9927_ =
                l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_send___redArg(
                    v_ch_9926_, v_v_9920_,
                );
            return v___x_9927_;
        }
    }
}
pub unsafe fn l_Std_CloseableChannel_send___redArg___boxed(
    mut v_ch_9928_: *mut LeanObject,
    mut v_v_9929_: *mut LeanObject,
    mut v_a_9930_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_9931_: *mut LeanObject = core::ptr::null_mut();
    v_res_9931_ = l_Std_CloseableChannel_send___redArg(v_ch_9928_, v_v_9929_);
    return v_res_9931_;
}
pub unsafe fn l_Std_CloseableChannel_send(
    mut v_00_u03b1_9932_: *mut LeanObject,
    mut v_ch_9933_: *mut LeanObject,
    mut v_v_9934_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_9936_: *mut LeanObject = core::ptr::null_mut();
    v___x_9936_ = l_Std_CloseableChannel_send___redArg(v_ch_9933_, v_v_9934_);
    return v___x_9936_;
}
pub unsafe fn l_Std_CloseableChannel_send___boxed(
    mut v_00_u03b1_9937_: *mut LeanObject,
    mut v_ch_9938_: *mut LeanObject,
    mut v_v_9939_: *mut LeanObject,
    mut v_a_9940_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_9941_: *mut LeanObject = core::ptr::null_mut();
    v_res_9941_ = l_Std_CloseableChannel_send(v_00_u03b1_9937_, v_ch_9938_, v_v_9939_);
    return v_res_9941_;
}
pub unsafe fn l_Std_CloseableChannel_close___redArg(
    mut v_ch_9942_: *mut LeanObject,
) -> *mut LeanObject {
    match lean_obj_tag(v_ch_9942_) {
        0 => {
            let mut v_ch_9944_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_9945_: *mut LeanObject = core::ptr::null_mut();
            v_ch_9944_ = lean_ctor_get(v_ch_9942_, 0);
            lean_inc_ref(v_ch_9944_);
            lean_dec_ref_known(v_ch_9942_, 1);
            v___x_9945_ =
                l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_close___redArg(
                    v_ch_9944_,
                );
            return v___x_9945_;
        }
        1 => {
            let mut v_ch_9946_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_9947_: *mut LeanObject = core::ptr::null_mut();
            v_ch_9946_ = lean_ctor_get(v_ch_9942_, 0);
            lean_inc_ref(v_ch_9946_);
            lean_dec_ref_known(v_ch_9942_, 1);
            v___x_9947_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_close___redArg(
                v_ch_9946_,
            );
            return v___x_9947_;
        }
        _ => {
            let mut v_ch_9948_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_9949_: *mut LeanObject = core::ptr::null_mut();
            v_ch_9948_ = lean_ctor_get(v_ch_9942_, 0);
            lean_inc_ref(v_ch_9948_);
            lean_dec_ref_known(v_ch_9942_, 1);
            v___x_9949_ =
                l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_close___redArg(
                    v_ch_9948_,
                );
            return v___x_9949_;
        }
    }
}
pub unsafe fn l_Std_CloseableChannel_close___redArg___boxed(
    mut v_ch_9950_: *mut LeanObject,
    mut v_a_9951_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_9952_: *mut LeanObject = core::ptr::null_mut();
    v_res_9952_ = l_Std_CloseableChannel_close___redArg(v_ch_9950_);
    return v_res_9952_;
}
pub unsafe fn l_Std_CloseableChannel_close(
    mut v_00_u03b1_9953_: *mut LeanObject,
    mut v_ch_9954_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_9956_: *mut LeanObject = core::ptr::null_mut();
    v___x_9956_ = l_Std_CloseableChannel_close___redArg(v_ch_9954_);
    return v___x_9956_;
}
pub unsafe fn l_Std_CloseableChannel_close___boxed(
    mut v_00_u03b1_9957_: *mut LeanObject,
    mut v_ch_9958_: *mut LeanObject,
    mut v_a_9959_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_9960_: *mut LeanObject = core::ptr::null_mut();
    v_res_9960_ = l_Std_CloseableChannel_close(v_00_u03b1_9957_, v_ch_9958_);
    return v_res_9960_;
}
pub unsafe fn l_Std_CloseableChannel_isClosed___redArg(mut v_ch_9961_: *mut LeanObject) -> u8 {
    match lean_obj_tag(v_ch_9961_) {
        0 => {
            let mut v_ch_9963_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_9964_: u8 = 0;
            v_ch_9963_ = lean_ctor_get(v_ch_9961_, 0);
            lean_inc_ref(v_ch_9963_);
            lean_dec_ref_known(v_ch_9961_, 1);
            v___x_9964_ =
                l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_isClosed___redArg(
                    v_ch_9963_,
                );
            return v___x_9964_;
        }
        1 => {
            let mut v_ch_9965_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_9966_: u8 = 0;
            v_ch_9965_ = lean_ctor_get(v_ch_9961_, 0);
            lean_inc_ref(v_ch_9965_);
            lean_dec_ref_known(v_ch_9961_, 1);
            v___x_9966_ =
                l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_isClosed___redArg(
                    v_ch_9965_,
                );
            return v___x_9966_;
        }
        _ => {
            let mut v_ch_9967_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_9968_: u8 = 0;
            v_ch_9967_ = lean_ctor_get(v_ch_9961_, 0);
            lean_inc_ref(v_ch_9967_);
            lean_dec_ref_known(v_ch_9961_, 1);
            v___x_9968_ =
                l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_isClosed___redArg(
                    v_ch_9967_,
                );
            return v___x_9968_;
        }
    }
}
pub unsafe fn l_Std_CloseableChannel_isClosed___redArg___boxed(
    mut v_ch_9969_: *mut LeanObject,
    mut v_a_9970_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_9971_: u8 = 0;
    let mut v_r_9972_: *mut LeanObject = core::ptr::null_mut();
    v_res_9971_ = l_Std_CloseableChannel_isClosed___redArg(v_ch_9969_);
    v_r_9972_ = lean_box((v_res_9971_) as usize);
    return v_r_9972_;
}
pub unsafe fn l_Std_CloseableChannel_isClosed(
    mut v_00_u03b1_9973_: *mut LeanObject,
    mut v_ch_9974_: *mut LeanObject,
) -> u8 {
    let mut v___x_9976_: u8 = 0;
    v___x_9976_ = l_Std_CloseableChannel_isClosed___redArg(v_ch_9974_);
    return v___x_9976_;
}
pub unsafe fn l_Std_CloseableChannel_isClosed___boxed(
    mut v_00_u03b1_9977_: *mut LeanObject,
    mut v_ch_9978_: *mut LeanObject,
    mut v_a_9979_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_9980_: u8 = 0;
    let mut v_r_9981_: *mut LeanObject = core::ptr::null_mut();
    v_res_9980_ = l_Std_CloseableChannel_isClosed(v_00_u03b1_9977_, v_ch_9978_);
    v_r_9981_ = lean_box((v_res_9980_) as usize);
    return v_r_9981_;
}
pub unsafe fn l_Std_CloseableChannel_tryRecv___redArg(
    mut v_ch_9982_: *mut LeanObject,
) -> *mut LeanObject {
    match lean_obj_tag(v_ch_9982_) {
        0 => {
            let mut v_ch_9984_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_9985_: *mut LeanObject = core::ptr::null_mut();
            v_ch_9984_ = lean_ctor_get(v_ch_9982_, 0);
            lean_inc_ref(v_ch_9984_);
            lean_dec_ref_known(v_ch_9982_, 1);
            v___x_9985_ =
                l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_tryRecv___redArg(
                    v_ch_9984_,
                );
            return v___x_9985_;
        }
        1 => {
            let mut v_ch_9986_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_9987_: *mut LeanObject = core::ptr::null_mut();
            v_ch_9986_ = lean_ctor_get(v_ch_9982_, 0);
            lean_inc_ref(v_ch_9986_);
            lean_dec_ref_known(v_ch_9982_, 1);
            v___x_9987_ =
                l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_tryRecv___redArg(
                    v_ch_9986_,
                );
            return v___x_9987_;
        }
        _ => {
            let mut v_ch_9988_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_9989_: *mut LeanObject = core::ptr::null_mut();
            v_ch_9988_ = lean_ctor_get(v_ch_9982_, 0);
            lean_inc_ref(v_ch_9988_);
            lean_dec_ref_known(v_ch_9982_, 1);
            v___x_9989_ =
                l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_tryRecv___redArg(
                    v_ch_9988_,
                );
            return v___x_9989_;
        }
    }
}
pub unsafe fn l_Std_CloseableChannel_tryRecv___redArg___boxed(
    mut v_ch_9990_: *mut LeanObject,
    mut v_a_9991_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_9992_: *mut LeanObject = core::ptr::null_mut();
    v_res_9992_ = l_Std_CloseableChannel_tryRecv___redArg(v_ch_9990_);
    return v_res_9992_;
}
pub unsafe fn l_Std_CloseableChannel_tryRecv(
    mut v_00_u03b1_9993_: *mut LeanObject,
    mut v_ch_9994_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_9996_: *mut LeanObject = core::ptr::null_mut();
    v___x_9996_ = l_Std_CloseableChannel_tryRecv___redArg(v_ch_9994_);
    return v___x_9996_;
}
pub unsafe fn l_Std_CloseableChannel_tryRecv___boxed(
    mut v_00_u03b1_9997_: *mut LeanObject,
    mut v_ch_9998_: *mut LeanObject,
    mut v_a_9999_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_10000_: *mut LeanObject = core::ptr::null_mut();
    v_res_10000_ = l_Std_CloseableChannel_tryRecv(v_00_u03b1_9997_, v_ch_9998_);
    return v_res_10000_;
}
pub unsafe fn l_Std_CloseableChannel_recv___redArg(
    mut v_ch_10001_: *mut LeanObject,
) -> *mut LeanObject {
    match lean_obj_tag(v_ch_10001_) {
        0 => {
            let mut v_ch_10003_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_10004_: *mut LeanObject = core::ptr::null_mut();
            v_ch_10003_ = lean_ctor_get(v_ch_10001_, 0);
            lean_inc_ref(v_ch_10003_);
            lean_dec_ref_known(v_ch_10001_, 1);
            v___x_10004_ =
                l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recv___redArg(
                    v_ch_10003_,
                );
            return v___x_10004_;
        }
        1 => {
            let mut v_ch_10005_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_10006_: *mut LeanObject = core::ptr::null_mut();
            v_ch_10005_ = lean_ctor_get(v_ch_10001_, 0);
            lean_inc_ref(v_ch_10005_);
            lean_dec_ref_known(v_ch_10001_, 1);
            v___x_10006_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recv___redArg(
                v_ch_10005_,
            );
            return v___x_10006_;
        }
        _ => {
            let mut v_ch_10007_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_10008_: *mut LeanObject = core::ptr::null_mut();
            v_ch_10007_ = lean_ctor_get(v_ch_10001_, 0);
            lean_inc_ref(v_ch_10007_);
            lean_dec_ref_known(v_ch_10001_, 1);
            v___x_10008_ =
                l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recv___redArg(
                    v_ch_10007_,
                );
            return v___x_10008_;
        }
    }
}
pub unsafe fn l_Std_CloseableChannel_recv___redArg___boxed(
    mut v_ch_10009_: *mut LeanObject,
    mut v_a_10010_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_10011_: *mut LeanObject = core::ptr::null_mut();
    v_res_10011_ = l_Std_CloseableChannel_recv___redArg(v_ch_10009_);
    return v_res_10011_;
}
pub unsafe fn l_Std_CloseableChannel_recv(
    mut v_00_u03b1_10012_: *mut LeanObject,
    mut v_ch_10013_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_10015_: *mut LeanObject = core::ptr::null_mut();
    v___x_10015_ = l_Std_CloseableChannel_recv___redArg(v_ch_10013_);
    return v___x_10015_;
}
pub unsafe fn l_Std_CloseableChannel_recv___boxed(
    mut v_00_u03b1_10016_: *mut LeanObject,
    mut v_ch_10017_: *mut LeanObject,
    mut v_a_10018_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_10019_: *mut LeanObject = core::ptr::null_mut();
    v_res_10019_ = l_Std_CloseableChannel_recv(v_00_u03b1_10016_, v_ch_10017_);
    return v_res_10019_;
}
pub unsafe fn l_Std_CloseableChannel_recvSelector___redArg(
    mut v_ch_10020_: *mut LeanObject,
) -> *mut LeanObject {
    match lean_obj_tag(v_ch_10020_) {
        0 => {
            let mut v_ch_10021_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_10022_: *mut LeanObject = core::ptr::null_mut();
            v_ch_10021_ = lean_ctor_get(v_ch_10020_, 0);
            lean_inc_ref(v_ch_10021_);
            lean_dec_ref_known(v_ch_10020_, 1);
            v___x_10022_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector___redArg(v_ch_10021_);
            return v___x_10022_;
        }
        1 => {
            let mut v_ch_10023_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_10024_: *mut LeanObject = core::ptr::null_mut();
            v_ch_10023_ = lean_ctor_get(v_ch_10020_, 0);
            lean_inc_ref(v_ch_10023_);
            lean_dec_ref_known(v_ch_10020_, 1);
            v___x_10024_ =
                l___private_Std_Sync_Channel_0__Std_CloseableChannel_Zero_recvSelector___redArg(
                    v_ch_10023_,
                );
            return v___x_10024_;
        }
        _ => {
            let mut v_ch_10025_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_10026_: *mut LeanObject = core::ptr::null_mut();
            v_ch_10025_ = lean_ctor_get(v_ch_10020_, 0);
            lean_inc_ref(v_ch_10025_);
            lean_dec_ref_known(v_ch_10020_, 1);
            v___x_10026_ =
                l___private_Std_Sync_Channel_0__Std_CloseableChannel_Bounded_recvSelector___redArg(
                    v_ch_10025_,
                );
            return v___x_10026_;
        }
    }
}
pub unsafe fn l_Std_CloseableChannel_recvSelector(
    mut v_00_u03b1_10027_: *mut LeanObject,
    mut v_ch_10028_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_10029_: *mut LeanObject = core::ptr::null_mut();
    v___x_10029_ = l_Std_CloseableChannel_recvSelector___redArg(v_ch_10028_);
    return v___x_10029_;
}
pub unsafe fn _init_l_Std_CloseableChannel_forAsync___redArg___lam__0___closed__0()
-> *mut LeanObject {
    let mut v___x_10030_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_10031_: *mut LeanObject = core::ptr::null_mut();
    v___x_10030_ = lean_box(0);
    v___x_10031_ = lean_task_pure(v___x_10030_);
    return v___x_10031_;
}
pub unsafe fn l_Std_CloseableChannel_forAsync___redArg___lam__0(
    mut v_f_10032_: *mut LeanObject,
    mut v_ch_10033_: *mut LeanObject,
    mut v_prio_10034_: *mut LeanObject,
    mut v_x_10035_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_10035_) == 0 {
        let mut v___x_10037_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_prio_10034_);
        lean_dec_ref(v_ch_10033_);
        lean_dec_ref(v_f_10032_);
        v___x_10037_ = lean_obj_once(
            core::ptr::addr_of_mut!(l_Std_CloseableChannel_forAsync___redArg___lam__0___closed__0),
            core::ptr::addr_of_mut!(
                l_Std_CloseableChannel_forAsync___redArg___lam__0___closed__0_once
            ),
            _init_l_Std_CloseableChannel_forAsync___redArg___lam__0___closed__0,
        );
        return v___x_10037_;
    } else {
        let mut v_val_10038_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_10039_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_10040_: *mut LeanObject = core::ptr::null_mut();
        v_val_10038_ = lean_ctor_get(v_x_10035_, 0);
        lean_inc(v_val_10038_);
        lean_dec_ref_known(v_x_10035_, 1);
        lean_inc_ref(v_f_10032_);
        v___x_10039_ = lean_apply_2(v_f_10032_, v_val_10038_, lean_box(0));
        v___x_10040_ =
            l_Std_CloseableChannel_forAsync___redArg(v_f_10032_, v_ch_10033_, v_prio_10034_);
        return v___x_10040_;
    }
}
pub unsafe fn l_Std_CloseableChannel_forAsync___redArg___lam__0___boxed(
    mut v_f_10041_: *mut LeanObject,
    mut v_ch_10042_: *mut LeanObject,
    mut v_prio_10043_: *mut LeanObject,
    mut v_x_10044_: *mut LeanObject,
    mut v___y_10045_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_10046_: *mut LeanObject = core::ptr::null_mut();
    v_res_10046_ = l_Std_CloseableChannel_forAsync___redArg___lam__0(
        v_f_10041_,
        v_ch_10042_,
        v_prio_10043_,
        v_x_10044_,
    );
    return v_res_10046_;
}
pub unsafe fn l_Std_CloseableChannel_forAsync___redArg(
    mut v_f_10047_: *mut LeanObject,
    mut v_ch_10048_: *mut LeanObject,
    mut v_prio_10049_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_10051_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_10052_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_10053_: u8 = 0;
    let mut v___x_10054_: *mut LeanObject = core::ptr::null_mut();
    lean_inc_ref(v_ch_10048_);
    v___x_10051_ = l_Std_CloseableChannel_recv___redArg(v_ch_10048_);
    lean_inc(v_prio_10049_);
    v___f_10052_ = lean_alloc_closure(
        l_Std_CloseableChannel_forAsync___redArg___lam__0___boxed as *mut core::ffi::c_void,
        5,
        3,
    );
    lean_closure_set(v___f_10052_, 0, v_f_10047_);
    lean_closure_set(v___f_10052_, 1, v_ch_10048_);
    lean_closure_set(v___f_10052_, 2, v_prio_10049_);
    v___x_10053_ = 0;
    v___x_10054_ = lean_io_bind_task(v___x_10051_, v___f_10052_, v_prio_10049_, v___x_10053_);
    return v___x_10054_;
}
pub unsafe fn l_Std_CloseableChannel_forAsync___redArg___boxed(
    mut v_f_10055_: *mut LeanObject,
    mut v_ch_10056_: *mut LeanObject,
    mut v_prio_10057_: *mut LeanObject,
    mut v_a_10058_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_10059_: *mut LeanObject = core::ptr::null_mut();
    v_res_10059_ = l_Std_CloseableChannel_forAsync___redArg(v_f_10055_, v_ch_10056_, v_prio_10057_);
    return v_res_10059_;
}
pub unsafe fn l_Std_CloseableChannel_forAsync(
    mut v_00_u03b1_10060_: *mut LeanObject,
    mut v_f_10061_: *mut LeanObject,
    mut v_ch_10062_: *mut LeanObject,
    mut v_prio_10063_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_10065_: *mut LeanObject = core::ptr::null_mut();
    v___x_10065_ = l_Std_CloseableChannel_forAsync___redArg(v_f_10061_, v_ch_10062_, v_prio_10063_);
    return v___x_10065_;
}
pub unsafe fn l_Std_CloseableChannel_forAsync___boxed(
    mut v_00_u03b1_10066_: *mut LeanObject,
    mut v_f_10067_: *mut LeanObject,
    mut v_ch_10068_: *mut LeanObject,
    mut v_prio_10069_: *mut LeanObject,
    mut v_a_10070_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_10071_: *mut LeanObject = core::ptr::null_mut();
    v_res_10071_ =
        l_Std_CloseableChannel_forAsync(v_00_u03b1_10066_, v_f_10067_, v_ch_10068_, v_prio_10069_);
    return v_res_10071_;
}
pub unsafe fn l_Std_CloseableChannel_instAsyncStreamOptionOfInhabited___lam__0(
    mut v_x_10072_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_10074_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_10075_: *mut LeanObject = core::ptr::null_mut();
    v___x_10074_ = lean_box(0);
    v___x_10075_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_10075_, 0, v___x_10074_);
    return v___x_10075_;
}
pub unsafe fn l_Std_CloseableChannel_instAsyncStreamOptionOfInhabited___lam__0___boxed(
    mut v_x_10076_: *mut LeanObject,
    mut v___y_10077_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_10078_: *mut LeanObject = core::ptr::null_mut();
    v_res_10078_ = l_Std_CloseableChannel_instAsyncStreamOptionOfInhabited___lam__0(v_x_10076_);
    lean_dec_ref(v_x_10076_);
    return v_res_10078_;
}
pub unsafe fn l_Std_CloseableChannel_instAsyncStreamOptionOfInhabited(
    mut v_00_u03b1_10084_: *mut LeanObject,
    mut v_inst_10085_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_10086_: *mut LeanObject = core::ptr::null_mut();
    v___x_10086_ = l_Std_CloseableChannel_instAsyncStreamOptionOfInhabited___closed__2;
    return v___x_10086_;
}
pub unsafe fn l_Std_CloseableChannel_instAsyncStreamOptionOfInhabited___boxed(
    mut v_00_u03b1_10087_: *mut LeanObject,
    mut v_inst_10088_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_10089_: *mut LeanObject = core::ptr::null_mut();
    v_res_10089_ =
        l_Std_CloseableChannel_instAsyncStreamOptionOfInhabited(v_00_u03b1_10087_, v_inst_10088_);
    lean_dec(v_inst_10088_);
    return v_res_10089_;
}
pub unsafe fn l_Std_CloseableChannel_instAsyncReadOptionOfInhabited___lam__0(
    mut v_a_10090_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_10091_: *mut LeanObject = core::ptr::null_mut();
    v___x_10091_ = lean_alloc_ctor(1, 1, (0) as u32);
    lean_ctor_set(v___x_10091_, 0, v_a_10090_);
    return v___x_10091_;
}
pub unsafe fn l_Std_CloseableChannel_instAsyncReadOptionOfInhabited___lam__1(
    mut v___f_10092_: *mut LeanObject,
    mut v_x_10093_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_10095_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_10097_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_10098_: u8 = 0;
    let mut v___x_10100_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_10101_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_10102_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_10103_: u8 = 0;
    let mut v_a_10104_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_10105_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_10107_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_10108_: u8 = 0;
    let mut v___x_10110_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_10111_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_10112_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_10113_: u8 = 0;
    let mut v_a_10114_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_10115_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_10116_: u8 = 0;
    let mut v___x_10117_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_10118_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_10093_) == 0 {
                    lean_dec_ref(v___f_10092_);
                    v_a_10095_ = lean_ctor_get(v_x_10093_, 0);
                    v_isSharedCheck_10103_ = (!lean_is_exclusive(v_x_10093_)) as u8;
                    if v_isSharedCheck_10103_ == 0 {
                        v___x_10097_ = v_x_10093_;
                        v_isShared_10098_ = v_isSharedCheck_10103_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_10095_);
                        lean_dec(v_x_10093_);
                        v___x_10097_ = lean_box(0);
                        v_isShared_10098_ = v_isSharedCheck_10103_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_10104_ = lean_ctor_get(v_x_10093_, 0);
                    lean_inc(v_a_10104_);
                    lean_dec_ref_known(v_x_10093_, 1);
                    if lean_obj_tag(v_a_10104_) == 0 {
                        lean_dec_ref(v___f_10092_);
                        v_a_10105_ = lean_ctor_get(v_a_10104_, 0);
                        v_isSharedCheck_10113_ = (!lean_is_exclusive(v_a_10104_)) as u8;
                        if v_isSharedCheck_10113_ == 0 {
                            v___x_10107_ = v_a_10104_;
                            v_isShared_10108_ = v_isSharedCheck_10113_;
                            state = 3;
                            continue;
                        } else {
                            lean_inc(v_a_10105_);
                            lean_dec(v_a_10104_);
                            v___x_10107_ = lean_box(0);
                            v_isShared_10108_ = v_isSharedCheck_10113_;
                            state = 3;
                            continue;
                        }
                    } else {
                        v_a_10114_ = lean_ctor_get(v_a_10104_, 0);
                        lean_inc(v_a_10114_);
                        lean_dec_ref_known(v_a_10104_, 1);
                        v___x_10115_ = lean_unsigned_to_nat(0);
                        v___x_10116_ = 0;
                        v___x_10117_ =
                            lean_task_map(v___f_10092_, v_a_10114_, v___x_10115_, v___x_10116_);
                        v___x_10118_ = lean_alloc_ctor(1, 1, (0) as u32);
                        lean_ctor_set(v___x_10118_, 0, v___x_10117_);
                        return v___x_10118_;
                    }
                }
            }
            1 => {
                if v_isShared_10098_ == 0 {
                    v___x_10100_ = v___x_10097_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_10102_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_10102_, 0, v_a_10095_);
                    v___x_10100_ = v_reuseFailAlloc_10102_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_10101_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_10101_, 0, v___x_10100_);
                return v___x_10101_;
            }
            3 => {
                if v_isShared_10108_ == 0 {
                    v___x_10110_ = v___x_10107_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_10112_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_10112_, 0, v_a_10105_);
                    v___x_10110_ = v_reuseFailAlloc_10112_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_10111_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_10111_, 0, v___x_10110_);
                return v___x_10111_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_CloseableChannel_instAsyncReadOptionOfInhabited___lam__1___boxed(
    mut v___f_10119_: *mut LeanObject,
    mut v_x_10120_: *mut LeanObject,
    mut v___y_10121_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_10122_: *mut LeanObject = core::ptr::null_mut();
    v_res_10122_ =
        l_Std_CloseableChannel_instAsyncReadOptionOfInhabited___lam__1(v___f_10119_, v_x_10120_);
    return v_res_10122_;
}
pub unsafe fn l_Std_CloseableChannel_instAsyncReadOptionOfInhabited___lam__2(
    mut v___f_10123_: *mut LeanObject,
    mut v_receiver_10124_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_10126_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_10127_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_10128_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_10129_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_10130_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_10131_: u8 = 0;
    let mut v___x_10132_: *mut LeanObject = core::ptr::null_mut();
    v___x_10126_ = l_Std_CloseableChannel_recv___redArg(v_receiver_10124_);
    v___x_10127_ = lean_alloc_ctor(1, 1, (0) as u32);
    lean_ctor_set(v___x_10127_, 0, v___x_10126_);
    v___x_10128_ = lean_alloc_ctor(1, 1, (0) as u32);
    lean_ctor_set(v___x_10128_, 0, v___x_10127_);
    v___x_10129_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_10129_, 0, v___x_10128_);
    v___x_10130_ = lean_unsigned_to_nat(0);
    v___x_10131_ = 0;
    v___x_10132_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(
        lean_box(0),
        lean_box(0),
        v___x_10130_,
        v___x_10131_,
        v___x_10129_,
        v___f_10123_,
    );
    return v___x_10132_;
}
pub unsafe fn l_Std_CloseableChannel_instAsyncReadOptionOfInhabited___lam__2___boxed(
    mut v___f_10133_: *mut LeanObject,
    mut v_receiver_10134_: *mut LeanObject,
    mut v___y_10135_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_10136_: *mut LeanObject = core::ptr::null_mut();
    v_res_10136_ = l_Std_CloseableChannel_instAsyncReadOptionOfInhabited___lam__2(
        v___f_10133_,
        v_receiver_10134_,
    );
    return v_res_10136_;
}
pub unsafe fn l_Std_CloseableChannel_instAsyncReadOptionOfInhabited(
    mut v_00_u03b1_10142_: *mut LeanObject,
    mut v_inst_10143_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_10144_: *mut LeanObject = core::ptr::null_mut();
    v___f_10144_ = l_Std_CloseableChannel_instAsyncReadOptionOfInhabited___closed__2;
    return v___f_10144_;
}
pub unsafe fn l_Std_CloseableChannel_instAsyncReadOptionOfInhabited___boxed(
    mut v_00_u03b1_10145_: *mut LeanObject,
    mut v_inst_10146_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_10147_: *mut LeanObject = core::ptr::null_mut();
    v_res_10147_ =
        l_Std_CloseableChannel_instAsyncReadOptionOfInhabited(v_00_u03b1_10145_, v_inst_10146_);
    lean_dec(v_inst_10146_);
    return v_res_10147_;
}
pub unsafe fn l_Std_CloseableChannel_instAsyncWriteOfInhabited___lam__1(
    mut v___f_10149_: *mut LeanObject,
    mut v_x_10150_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_10152_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_10154_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_10155_: u8 = 0;
    let mut v___x_10157_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_10158_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_10159_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_10160_: u8 = 0;
    let mut v_a_10161_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_10162_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_10163_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_10164_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_10165_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_10166_: u8 = 0;
    let mut v___x_10167_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_10168_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_10150_) == 0 {
                    lean_dec_ref(v___f_10149_);
                    v_a_10152_ = lean_ctor_get(v_x_10150_, 0);
                    v_isSharedCheck_10160_ = (!lean_is_exclusive(v_x_10150_)) as u8;
                    if v_isSharedCheck_10160_ == 0 {
                        v___x_10154_ = v_x_10150_;
                        v_isShared_10155_ = v_isSharedCheck_10160_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_10152_);
                        lean_dec(v_x_10150_);
                        v___x_10154_ = lean_box(0);
                        v_isShared_10155_ = v_isSharedCheck_10160_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_10161_ = lean_ctor_get(v_x_10150_, 0);
                    lean_inc(v_a_10161_);
                    lean_dec_ref_known(v_x_10150_, 1);
                    v___x_10162_ =
                        l_Std_CloseableChannel_instAsyncWriteOfInhabited___lam__1___closed__0;
                    v___x_10163_ =
                        lean_alloc_closure(l_Function_comp as *mut core::ffi::c_void, 6, 5);
                    lean_closure_set(v___x_10163_, 0, lean_box(0));
                    lean_closure_set(v___x_10163_, 1, lean_box(0));
                    lean_closure_set(v___x_10163_, 2, lean_box(0));
                    lean_closure_set(v___x_10163_, 3, v___x_10162_);
                    lean_closure_set(v___x_10163_, 4, v___f_10149_);
                    v___x_10164_ =
                        lean_alloc_closure(l_Except_mapError as *mut core::ffi::c_void, 5, 4);
                    lean_closure_set(v___x_10164_, 0, lean_box(0));
                    lean_closure_set(v___x_10164_, 1, lean_box(0));
                    lean_closure_set(v___x_10164_, 2, lean_box(0));
                    lean_closure_set(v___x_10164_, 3, v___x_10163_);
                    v___x_10165_ = lean_unsigned_to_nat(0);
                    v___x_10166_ = 0;
                    v___x_10167_ =
                        lean_task_map(v___x_10164_, v_a_10161_, v___x_10165_, v___x_10166_);
                    v___x_10168_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v___x_10168_, 0, v___x_10167_);
                    return v___x_10168_;
                }
            }
            1 => {
                if v_isShared_10155_ == 0 {
                    v___x_10157_ = v___x_10154_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_10159_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_10159_, 0, v_a_10152_);
                    v___x_10157_ = v_reuseFailAlloc_10159_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_10158_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_10158_, 0, v___x_10157_);
                return v___x_10158_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_CloseableChannel_instAsyncWriteOfInhabited___lam__1___boxed(
    mut v___f_10169_: *mut LeanObject,
    mut v_x_10170_: *mut LeanObject,
    mut v___y_10171_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_10172_: *mut LeanObject = core::ptr::null_mut();
    v_res_10172_ =
        l_Std_CloseableChannel_instAsyncWriteOfInhabited___lam__1(v___f_10169_, v_x_10170_);
    return v_res_10172_;
}
pub unsafe fn l_Std_CloseableChannel_instAsyncWriteOfInhabited___lam__0(
    mut v___f_10173_: *mut LeanObject,
    mut v_receiver_10174_: *mut LeanObject,
    mut v_x_10175_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_10177_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_10178_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_10179_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_10180_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_10181_: u8 = 0;
    let mut v___x_10182_: *mut LeanObject = core::ptr::null_mut();
    v___x_10177_ = l_Std_CloseableChannel_send___redArg(v_receiver_10174_, v_x_10175_);
    v___x_10178_ = lean_alloc_ctor(1, 1, (0) as u32);
    lean_ctor_set(v___x_10178_, 0, v___x_10177_);
    v___x_10179_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_10179_, 0, v___x_10178_);
    v___x_10180_ = lean_unsigned_to_nat(0);
    v___x_10181_ = 0;
    v___x_10182_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(
        lean_box(0),
        lean_box(0),
        v___x_10180_,
        v___x_10181_,
        v___x_10179_,
        v___f_10173_,
    );
    return v___x_10182_;
}
pub unsafe fn l_Std_CloseableChannel_instAsyncWriteOfInhabited___lam__0___boxed(
    mut v___f_10183_: *mut LeanObject,
    mut v_receiver_10184_: *mut LeanObject,
    mut v_x_10185_: *mut LeanObject,
    mut v___y_10186_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_10187_: *mut LeanObject = core::ptr::null_mut();
    v_res_10187_ = l_Std_CloseableChannel_instAsyncWriteOfInhabited___lam__0(
        v___f_10183_,
        v_receiver_10184_,
        v_x_10185_,
    );
    return v_res_10187_;
}
pub unsafe fn l_Std_CloseableChannel_instAsyncWriteOfInhabited___lam__2(
    mut v_x_10188_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_10190_: *mut LeanObject = core::ptr::null_mut();
    v___x_10190_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector___redArg___lam__3___closed__1;
    return v___x_10190_;
}
pub unsafe fn l_Std_CloseableChannel_instAsyncWriteOfInhabited___lam__2___boxed(
    mut v_x_10191_: *mut LeanObject,
    mut v___y_10192_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_10193_: *mut LeanObject = core::ptr::null_mut();
    v_res_10193_ = l_Std_CloseableChannel_instAsyncWriteOfInhabited___lam__2(v_x_10191_);
    lean_dec_ref(v_x_10191_);
    return v_res_10193_;
}
pub unsafe fn l_Std_CloseableChannel_instAsyncWriteOfInhabited___lam__3(
    mut v___f_10194_: *mut LeanObject,
    mut v_socket_10195_: *mut LeanObject,
    mut v_x_10196_: *mut LeanObject,
    mut v___y_10197_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_10199_: *mut LeanObject = core::ptr::null_mut();
    v___x_10199_ = lean_apply_3(v___f_10194_, v_socket_10195_, v___y_10197_, lean_box(0));
    return v___x_10199_;
}
pub unsafe fn l_Std_CloseableChannel_instAsyncWriteOfInhabited___lam__3___boxed(
    mut v___f_10200_: *mut LeanObject,
    mut v_socket_10201_: *mut LeanObject,
    mut v_x_10202_: *mut LeanObject,
    mut v___y_10203_: *mut LeanObject,
    mut v___y_10204_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_10205_: *mut LeanObject = core::ptr::null_mut();
    v_res_10205_ = l_Std_CloseableChannel_instAsyncWriteOfInhabited___lam__3(
        v___f_10200_,
        v_socket_10201_,
        v_x_10202_,
        v___y_10203_,
    );
    return v_res_10205_;
}
pub unsafe fn l_Std_CloseableChannel_instAsyncWriteOfInhabited___lam__4(
    mut v___f_10206_: *mut LeanObject,
    mut v___x_10207_: *mut LeanObject,
    mut v_socket_10208_: *mut LeanObject,
    mut v_data_10209_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_10211_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_10212_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_10213_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_10214_: u8 = 0;
    v___x_10211_ = lean_unsigned_to_nat(0);
    v___x_10212_ = lean_array_get_size(v_data_10209_);
    v___x_10213_ = lean_box(0);
    v___x_10214_ = lean_nat_dec_lt(v___x_10211_, v___x_10212_);
    if v___x_10214_ == 0 {
        let mut v___x_10215_: *mut LeanObject = core::ptr::null_mut();
        lean_dec_ref(v_data_10209_);
        lean_dec_ref(v_socket_10208_);
        lean_dec_ref(v___x_10207_);
        lean_dec_ref(v___f_10206_);
        v___x_10215_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector___redArg___lam__3___closed__1;
        return v___x_10215_;
    } else {
        let mut v___f_10216_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_10217_: u8 = 0;
        v___f_10216_ = lean_alloc_closure(
            l_Std_CloseableChannel_instAsyncWriteOfInhabited___lam__3___boxed
                as *mut core::ffi::c_void,
            5,
            2,
        );
        lean_closure_set(v___f_10216_, 0, v___f_10206_);
        lean_closure_set(v___f_10216_, 1, v_socket_10208_);
        v___x_10217_ = lean_nat_dec_le(v___x_10212_, v___x_10212_);
        if v___x_10217_ == 0 {
            if v___x_10214_ == 0 {
                let mut v___x_10218_: *mut LeanObject = core::ptr::null_mut();
                lean_dec_ref(v___f_10216_);
                lean_dec_ref(v_data_10209_);
                lean_dec_ref(v___x_10207_);
                v___x_10218_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Unbounded_recvSelector___redArg___lam__3___closed__1;
                return v___x_10218_;
            } else {
                let mut v___x_10219_: usize = 0;
                let mut v___x_10220_: usize = 0;
                let mut v___x_753__overap_10221_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_10222_: *mut LeanObject = core::ptr::null_mut();
                v___x_10219_ = 0usize;
                v___x_10220_ = lean_usize_of_nat(v___x_10212_);
                v___x_753__overap_10221_ =
                    l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                        lean_box(0),
                        lean_box(0),
                        lean_box(0),
                        v___x_10207_,
                        v___f_10216_,
                        v_data_10209_,
                        v___x_10219_,
                        v___x_10220_,
                        v___x_10213_,
                    );
                v___x_10222_ = lean_apply_1(v___x_753__overap_10221_, lean_box(0));
                return v___x_10222_;
            }
        } else {
            let mut v___x_10223_: usize = 0;
            let mut v___x_10224_: usize = 0;
            let mut v___x_756__overap_10225_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_10226_: *mut LeanObject = core::ptr::null_mut();
            v___x_10223_ = 0usize;
            v___x_10224_ = lean_usize_of_nat(v___x_10212_);
            v___x_756__overap_10225_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                lean_box(0),
                lean_box(0),
                lean_box(0),
                v___x_10207_,
                v___f_10216_,
                v_data_10209_,
                v___x_10223_,
                v___x_10224_,
                v___x_10213_,
            );
            v___x_10226_ = lean_apply_1(v___x_756__overap_10225_, lean_box(0));
            return v___x_10226_;
        }
    }
}
pub unsafe fn l_Std_CloseableChannel_instAsyncWriteOfInhabited___lam__4___boxed(
    mut v___f_10227_: *mut LeanObject,
    mut v___x_10228_: *mut LeanObject,
    mut v_socket_10229_: *mut LeanObject,
    mut v_data_10230_: *mut LeanObject,
    mut v___y_10231_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_10232_: *mut LeanObject = core::ptr::null_mut();
    v_res_10232_ = l_Std_CloseableChannel_instAsyncWriteOfInhabited___lam__4(
        v___f_10227_,
        v___x_10228_,
        v_socket_10229_,
        v_data_10230_,
    );
    return v_res_10232_;
}
pub unsafe fn _init_l_Std_CloseableChannel_instAsyncWriteOfInhabited___closed__3() -> *mut LeanObject
{
    let mut v___x_10238_: *mut LeanObject = core::ptr::null_mut();
    v___x_10238_ = l_Std_Async_EAsync_instMonad(lean_box(0));
    return v___x_10238_;
}
pub unsafe fn _init_l_Std_CloseableChannel_instAsyncWriteOfInhabited___closed__4() -> *mut LeanObject
{
    let mut v___x_10239_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_10240_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_10241_: *mut LeanObject = core::ptr::null_mut();
    v___x_10239_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_CloseableChannel_instAsyncWriteOfInhabited___closed__3),
        core::ptr::addr_of_mut!(l_Std_CloseableChannel_instAsyncWriteOfInhabited___closed__3_once),
        _init_l_Std_CloseableChannel_instAsyncWriteOfInhabited___closed__3,
    );
    v___f_10240_ = l_Std_CloseableChannel_instAsyncWriteOfInhabited___closed__1;
    v___f_10241_ = lean_alloc_closure(
        l_Std_CloseableChannel_instAsyncWriteOfInhabited___lam__4___boxed as *mut core::ffi::c_void,
        5,
        2,
    );
    lean_closure_set(v___f_10241_, 0, v___f_10240_);
    lean_closure_set(v___f_10241_, 1, v___x_10239_);
    return v___f_10241_;
}
pub unsafe fn _init_l_Std_CloseableChannel_instAsyncWriteOfInhabited___closed__5() -> *mut LeanObject
{
    let mut v___f_10242_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_10243_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_10244_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_10245_: *mut LeanObject = core::ptr::null_mut();
    v___f_10242_ = l_Std_CloseableChannel_instAsyncWriteOfInhabited___closed__2;
    v___f_10243_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_CloseableChannel_instAsyncWriteOfInhabited___closed__4),
        core::ptr::addr_of_mut!(l_Std_CloseableChannel_instAsyncWriteOfInhabited___closed__4_once),
        _init_l_Std_CloseableChannel_instAsyncWriteOfInhabited___closed__4,
    );
    v___f_10244_ = l_Std_CloseableChannel_instAsyncWriteOfInhabited___closed__1;
    v___x_10245_ = lean_alloc_ctor(0, 3, (0) as u32);
    lean_ctor_set(v___x_10245_, 0, v___f_10244_);
    lean_ctor_set(v___x_10245_, 1, v___f_10243_);
    lean_ctor_set(v___x_10245_, 2, v___f_10242_);
    return v___x_10245_;
}
pub unsafe fn l_Std_CloseableChannel_instAsyncWriteOfInhabited(
    mut v_00_u03b1_10246_: *mut LeanObject,
    mut v_inst_10247_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_10248_: *mut LeanObject = core::ptr::null_mut();
    v___x_10248_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_CloseableChannel_instAsyncWriteOfInhabited___closed__5),
        core::ptr::addr_of_mut!(l_Std_CloseableChannel_instAsyncWriteOfInhabited___closed__5_once),
        _init_l_Std_CloseableChannel_instAsyncWriteOfInhabited___closed__5,
    );
    return v___x_10248_;
}
pub unsafe fn l_Std_CloseableChannel_instAsyncWriteOfInhabited___boxed(
    mut v_00_u03b1_10249_: *mut LeanObject,
    mut v_inst_10250_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_10251_: *mut LeanObject = core::ptr::null_mut();
    v_res_10251_ =
        l_Std_CloseableChannel_instAsyncWriteOfInhabited(v_00_u03b1_10249_, v_inst_10250_);
    lean_dec(v_inst_10250_);
    return v_res_10251_;
}
pub unsafe fn l_Std_CloseableChannel_sync___redArg(
    mut v_ch_10252_: *mut LeanObject,
) -> *mut LeanObject {
    lean_inc_ref(v_ch_10252_);
    return v_ch_10252_;
}
pub unsafe fn l_Std_CloseableChannel_sync___redArg___boxed(
    mut v_ch_10253_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_10254_: *mut LeanObject = core::ptr::null_mut();
    v_res_10254_ = l_Std_CloseableChannel_sync___redArg(v_ch_10253_);
    lean_dec_ref(v_ch_10253_);
    return v_res_10254_;
}
pub unsafe fn l_Std_CloseableChannel_sync(
    mut v_00_u03b1_10255_: *mut LeanObject,
    mut v_ch_10256_: *mut LeanObject,
) -> *mut LeanObject {
    lean_inc_ref(v_ch_10256_);
    return v_ch_10256_;
}
pub unsafe fn l_Std_CloseableChannel_sync___boxed(
    mut v_00_u03b1_10257_: *mut LeanObject,
    mut v_ch_10258_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_10259_: *mut LeanObject = core::ptr::null_mut();
    v_res_10259_ = l_Std_CloseableChannel_sync(v_00_u03b1_10257_, v_ch_10258_);
    lean_dec_ref(v_ch_10258_);
    return v_res_10259_;
}
pub unsafe fn l_Std_CloseableChannel_Sync_new___redArg(
    mut v_capacity_10260_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_10262_: *mut LeanObject = core::ptr::null_mut();
    v___x_10262_ = l_Std_CloseableChannel_new___redArg(v_capacity_10260_);
    return v___x_10262_;
}
pub unsafe fn l_Std_CloseableChannel_Sync_new___redArg___boxed(
    mut v_capacity_10263_: *mut LeanObject,
    mut v_a_10264_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_10265_: *mut LeanObject = core::ptr::null_mut();
    v_res_10265_ = l_Std_CloseableChannel_Sync_new___redArg(v_capacity_10263_);
    return v_res_10265_;
}
pub unsafe fn l_Std_CloseableChannel_Sync_new(
    mut v_00_u03b1_10266_: *mut LeanObject,
    mut v_capacity_10267_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_10269_: *mut LeanObject = core::ptr::null_mut();
    v___x_10269_ = l_Std_CloseableChannel_new___redArg(v_capacity_10267_);
    return v___x_10269_;
}
pub unsafe fn l_Std_CloseableChannel_Sync_new___boxed(
    mut v_00_u03b1_10270_: *mut LeanObject,
    mut v_capacity_10271_: *mut LeanObject,
    mut v_a_10272_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_10273_: *mut LeanObject = core::ptr::null_mut();
    v_res_10273_ = l_Std_CloseableChannel_Sync_new(v_00_u03b1_10270_, v_capacity_10271_);
    return v_res_10273_;
}
pub unsafe fn l_Std_CloseableChannel_Sync_trySend___redArg(
    mut v_ch_10274_: *mut LeanObject,
    mut v_v_10275_: *mut LeanObject,
) -> u8 {
    let mut v___x_10277_: u8 = 0;
    v___x_10277_ = l_Std_CloseableChannel_trySend___redArg(v_ch_10274_, v_v_10275_);
    return v___x_10277_;
}
pub unsafe fn l_Std_CloseableChannel_Sync_trySend___redArg___boxed(
    mut v_ch_10278_: *mut LeanObject,
    mut v_v_10279_: *mut LeanObject,
    mut v_a_10280_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_10281_: u8 = 0;
    let mut v_r_10282_: *mut LeanObject = core::ptr::null_mut();
    v_res_10281_ = l_Std_CloseableChannel_Sync_trySend___redArg(v_ch_10278_, v_v_10279_);
    v_r_10282_ = lean_box((v_res_10281_) as usize);
    return v_r_10282_;
}
pub unsafe fn l_Std_CloseableChannel_Sync_trySend(
    mut v_00_u03b1_10283_: *mut LeanObject,
    mut v_ch_10284_: *mut LeanObject,
    mut v_v_10285_: *mut LeanObject,
) -> u8 {
    let mut v___x_10287_: u8 = 0;
    v___x_10287_ = l_Std_CloseableChannel_trySend___redArg(v_ch_10284_, v_v_10285_);
    return v___x_10287_;
}
pub unsafe fn l_Std_CloseableChannel_Sync_trySend___boxed(
    mut v_00_u03b1_10288_: *mut LeanObject,
    mut v_ch_10289_: *mut LeanObject,
    mut v_v_10290_: *mut LeanObject,
    mut v_a_10291_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_10292_: u8 = 0;
    let mut v_r_10293_: *mut LeanObject = core::ptr::null_mut();
    v_res_10292_ = l_Std_CloseableChannel_Sync_trySend(v_00_u03b1_10288_, v_ch_10289_, v_v_10290_);
    v_r_10293_ = lean_box((v_res_10292_) as usize);
    return v_r_10293_;
}
pub unsafe fn l_Std_CloseableChannel_Sync_send___redArg(
    mut v_ch_10294_: *mut LeanObject,
    mut v_v_10295_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_10297_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_10298_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_10299_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_10301_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_10302_: u8 = 0;
    let mut v___x_10304_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_10305_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_10306_: u8 = 0;
    let mut v_a_10307_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_10309_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_10310_: u8 = 0;
    let mut v___x_10312_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_10313_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_10314_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_10297_ = l_Std_CloseableChannel_send___redArg(v_ch_10294_, v_v_10295_);
                v___x_10298_ = lean_io_wait(v___x_10297_);
                if lean_obj_tag(v___x_10298_) == 0 {
                    v_a_10299_ = lean_ctor_get(v___x_10298_, 0);
                    v_isSharedCheck_10306_ = (!lean_is_exclusive(v___x_10298_)) as u8;
                    if v_isSharedCheck_10306_ == 0 {
                        v___x_10301_ = v___x_10298_;
                        v_isShared_10302_ = v_isSharedCheck_10306_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_10299_);
                        lean_dec(v___x_10298_);
                        v___x_10301_ = lean_box(0);
                        v_isShared_10302_ = v_isSharedCheck_10306_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_10307_ = lean_ctor_get(v___x_10298_, 0);
                    v_isSharedCheck_10314_ = (!lean_is_exclusive(v___x_10298_)) as u8;
                    if v_isSharedCheck_10314_ == 0 {
                        v___x_10309_ = v___x_10298_;
                        v_isShared_10310_ = v_isSharedCheck_10314_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_10307_);
                        lean_dec(v___x_10298_);
                        v___x_10309_ = lean_box(0);
                        v_isShared_10310_ = v_isSharedCheck_10314_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_10302_ == 0 {
                    lean_ctor_set_tag(v___x_10301_, 1);
                    v___x_10304_ = v___x_10301_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_10305_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_10305_, 0, v_a_10299_);
                    v___x_10304_ = v_reuseFailAlloc_10305_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_10304_;
            }
            3 => {
                if v_isShared_10310_ == 0 {
                    lean_ctor_set_tag(v___x_10309_, 0);
                    v___x_10312_ = v___x_10309_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_10313_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_10313_, 0, v_a_10307_);
                    v___x_10312_ = v_reuseFailAlloc_10313_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_10312_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_CloseableChannel_Sync_send___redArg___boxed(
    mut v_ch_10315_: *mut LeanObject,
    mut v_v_10316_: *mut LeanObject,
    mut v_a_10317_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_10318_: *mut LeanObject = core::ptr::null_mut();
    v_res_10318_ = l_Std_CloseableChannel_Sync_send___redArg(v_ch_10315_, v_v_10316_);
    return v_res_10318_;
}
pub unsafe fn l_Std_CloseableChannel_Sync_send(
    mut v_00_u03b1_10319_: *mut LeanObject,
    mut v_ch_10320_: *mut LeanObject,
    mut v_v_10321_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_10323_: *mut LeanObject = core::ptr::null_mut();
    v___x_10323_ = l_Std_CloseableChannel_Sync_send___redArg(v_ch_10320_, v_v_10321_);
    return v___x_10323_;
}
pub unsafe fn l_Std_CloseableChannel_Sync_send___boxed(
    mut v_00_u03b1_10324_: *mut LeanObject,
    mut v_ch_10325_: *mut LeanObject,
    mut v_v_10326_: *mut LeanObject,
    mut v_a_10327_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_10328_: *mut LeanObject = core::ptr::null_mut();
    v_res_10328_ = l_Std_CloseableChannel_Sync_send(v_00_u03b1_10324_, v_ch_10325_, v_v_10326_);
    return v_res_10328_;
}
pub unsafe fn l_Std_CloseableChannel_Sync_close___redArg(
    mut v_ch_10329_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_10331_: *mut LeanObject = core::ptr::null_mut();
    v___x_10331_ = l_Std_CloseableChannel_close___redArg(v_ch_10329_);
    return v___x_10331_;
}
pub unsafe fn l_Std_CloseableChannel_Sync_close___redArg___boxed(
    mut v_ch_10332_: *mut LeanObject,
    mut v_a_10333_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_10334_: *mut LeanObject = core::ptr::null_mut();
    v_res_10334_ = l_Std_CloseableChannel_Sync_close___redArg(v_ch_10332_);
    return v_res_10334_;
}
pub unsafe fn l_Std_CloseableChannel_Sync_close(
    mut v_00_u03b1_10335_: *mut LeanObject,
    mut v_ch_10336_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_10338_: *mut LeanObject = core::ptr::null_mut();
    v___x_10338_ = l_Std_CloseableChannel_close___redArg(v_ch_10336_);
    return v___x_10338_;
}
pub unsafe fn l_Std_CloseableChannel_Sync_close___boxed(
    mut v_00_u03b1_10339_: *mut LeanObject,
    mut v_ch_10340_: *mut LeanObject,
    mut v_a_10341_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_10342_: *mut LeanObject = core::ptr::null_mut();
    v_res_10342_ = l_Std_CloseableChannel_Sync_close(v_00_u03b1_10339_, v_ch_10340_);
    return v_res_10342_;
}
pub unsafe fn l_Std_CloseableChannel_Sync_isClosed___redArg(
    mut v_ch_10343_: *mut LeanObject,
) -> u8 {
    let mut v___x_10345_: u8 = 0;
    v___x_10345_ = l_Std_CloseableChannel_isClosed___redArg(v_ch_10343_);
    return v___x_10345_;
}
pub unsafe fn l_Std_CloseableChannel_Sync_isClosed___redArg___boxed(
    mut v_ch_10346_: *mut LeanObject,
    mut v_a_10347_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_10348_: u8 = 0;
    let mut v_r_10349_: *mut LeanObject = core::ptr::null_mut();
    v_res_10348_ = l_Std_CloseableChannel_Sync_isClosed___redArg(v_ch_10346_);
    v_r_10349_ = lean_box((v_res_10348_) as usize);
    return v_r_10349_;
}
pub unsafe fn l_Std_CloseableChannel_Sync_isClosed(
    mut v_00_u03b1_10350_: *mut LeanObject,
    mut v_ch_10351_: *mut LeanObject,
) -> u8 {
    let mut v___x_10353_: u8 = 0;
    v___x_10353_ = l_Std_CloseableChannel_isClosed___redArg(v_ch_10351_);
    return v___x_10353_;
}
pub unsafe fn l_Std_CloseableChannel_Sync_isClosed___boxed(
    mut v_00_u03b1_10354_: *mut LeanObject,
    mut v_ch_10355_: *mut LeanObject,
    mut v_a_10356_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_10357_: u8 = 0;
    let mut v_r_10358_: *mut LeanObject = core::ptr::null_mut();
    v_res_10357_ = l_Std_CloseableChannel_Sync_isClosed(v_00_u03b1_10354_, v_ch_10355_);
    v_r_10358_ = lean_box((v_res_10357_) as usize);
    return v_r_10358_;
}
pub unsafe fn l_Std_CloseableChannel_Sync_tryRecv___redArg(
    mut v_ch_10359_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_10361_: *mut LeanObject = core::ptr::null_mut();
    v___x_10361_ = l_Std_CloseableChannel_tryRecv___redArg(v_ch_10359_);
    return v___x_10361_;
}
pub unsafe fn l_Std_CloseableChannel_Sync_tryRecv___redArg___boxed(
    mut v_ch_10362_: *mut LeanObject,
    mut v_a_10363_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_10364_: *mut LeanObject = core::ptr::null_mut();
    v_res_10364_ = l_Std_CloseableChannel_Sync_tryRecv___redArg(v_ch_10362_);
    return v_res_10364_;
}
pub unsafe fn l_Std_CloseableChannel_Sync_tryRecv(
    mut v_00_u03b1_10365_: *mut LeanObject,
    mut v_ch_10366_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_10368_: *mut LeanObject = core::ptr::null_mut();
    v___x_10368_ = l_Std_CloseableChannel_tryRecv___redArg(v_ch_10366_);
    return v___x_10368_;
}
pub unsafe fn l_Std_CloseableChannel_Sync_tryRecv___boxed(
    mut v_00_u03b1_10369_: *mut LeanObject,
    mut v_ch_10370_: *mut LeanObject,
    mut v_a_10371_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_10372_: *mut LeanObject = core::ptr::null_mut();
    v_res_10372_ = l_Std_CloseableChannel_Sync_tryRecv(v_00_u03b1_10369_, v_ch_10370_);
    return v_res_10372_;
}
pub unsafe fn l_Std_CloseableChannel_Sync_recv___redArg(
    mut v_ch_10373_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_10375_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_10376_: *mut LeanObject = core::ptr::null_mut();
    v___x_10375_ = l_Std_CloseableChannel_recv___redArg(v_ch_10373_);
    v___x_10376_ = lean_io_wait(v___x_10375_);
    return v___x_10376_;
}
pub unsafe fn l_Std_CloseableChannel_Sync_recv___redArg___boxed(
    mut v_ch_10377_: *mut LeanObject,
    mut v_a_10378_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_10379_: *mut LeanObject = core::ptr::null_mut();
    v_res_10379_ = l_Std_CloseableChannel_Sync_recv___redArg(v_ch_10377_);
    return v_res_10379_;
}
pub unsafe fn l_Std_CloseableChannel_Sync_recv(
    mut v_00_u03b1_10380_: *mut LeanObject,
    mut v_ch_10381_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_10383_: *mut LeanObject = core::ptr::null_mut();
    v___x_10383_ = l_Std_CloseableChannel_Sync_recv___redArg(v_ch_10381_);
    return v___x_10383_;
}
pub unsafe fn l_Std_CloseableChannel_Sync_recv___boxed(
    mut v_00_u03b1_10384_: *mut LeanObject,
    mut v_ch_10385_: *mut LeanObject,
    mut v_a_10386_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_10387_: *mut LeanObject = core::ptr::null_mut();
    v_res_10387_ = l_Std_CloseableChannel_Sync_recv(v_00_u03b1_10384_, v_ch_10385_);
    return v_res_10387_;
}
pub unsafe fn l___private_Std_Sync_Channel_0__Std_CloseableChannel_Sync_forIn___redArg___lam__1(
    mut v_toPure_10388_: *mut LeanObject,
    mut v_b_10389_: *mut LeanObject,
    mut v_f_10390_: *mut LeanObject,
    mut v_toBind_10391_: *mut LeanObject,
    mut v___f_10392_: *mut LeanObject,
    mut v_____do__lift_10393_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_____do__lift_10393_) == 0 {
        let mut v___x_10394_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v___f_10392_);
        lean_dec(v_toBind_10391_);
        lean_dec(v_f_10390_);
        v___x_10394_ = lean_apply_2(v_toPure_10388_, lean_box(0), v_b_10389_);
        return v___x_10394_;
    } else {
        let mut v_val_10395_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_10396_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_10397_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_toPure_10388_);
        v_val_10395_ = lean_ctor_get(v_____do__lift_10393_, 0);
        lean_inc(v_val_10395_);
        lean_dec_ref_known(v_____do__lift_10393_, 1);
        v___x_10396_ = lean_apply_2(v_f_10390_, v_val_10395_, v_b_10389_);
        v___x_10397_ = lean_apply_4(
            v_toBind_10391_,
            lean_box(0),
            lean_box(0),
            v___x_10396_,
            v___f_10392_,
        );
        return v___x_10397_;
    }
}
pub unsafe fn l___private_Std_Sync_Channel_0__Std_CloseableChannel_Sync_forIn___redArg(
    mut v_inst_10398_: *mut LeanObject,
    mut v_inst_10399_: *mut LeanObject,
    mut v_ch_10400_: *mut LeanObject,
    mut v_f_10401_: *mut LeanObject,
    mut v_b_10402_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toApplicative_10403_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toBind_10404_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toPure_10405_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_10406_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_10407_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_10408_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_10409_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_10410_: *mut LeanObject = core::ptr::null_mut();
    v_toApplicative_10403_ = lean_ctor_get(v_inst_10398_, 0);
    v_toBind_10404_ = lean_ctor_get(v_inst_10398_, 1);
    lean_inc_n(v_toBind_10404_, 2);
    v_toPure_10405_ = lean_ctor_get(v_toApplicative_10403_, 1);
    lean_inc_n(v_toPure_10405_, 2);
    lean_inc_ref(v_ch_10400_);
    v___x_10406_ = lean_alloc_closure(
        l_Std_CloseableChannel_Sync_recv___boxed as *mut core::ffi::c_void,
        3,
        2,
    );
    lean_closure_set(v___x_10406_, 0, lean_box(0));
    lean_closure_set(v___x_10406_, 1, v_ch_10400_);
    lean_inc(v_inst_10399_);
    v___x_10407_ = lean_apply_2(v_inst_10399_, lean_box(0), v___x_10406_);
    lean_inc(v_f_10401_);
    v___f_10408_ = lean_alloc_closure(
        l___private_Std_Sync_Channel_0__Std_CloseableChannel_Sync_forIn___redArg___lam__0
            as *mut core::ffi::c_void,
        6,
        5,
    );
    lean_closure_set(v___f_10408_, 0, v_toPure_10405_);
    lean_closure_set(v___f_10408_, 1, v_inst_10398_);
    lean_closure_set(v___f_10408_, 2, v_inst_10399_);
    lean_closure_set(v___f_10408_, 3, v_ch_10400_);
    lean_closure_set(v___f_10408_, 4, v_f_10401_);
    v___f_10409_ = lean_alloc_closure(
        l___private_Std_Sync_Channel_0__Std_CloseableChannel_Sync_forIn___redArg___lam__1
            as *mut core::ffi::c_void,
        6,
        5,
    );
    lean_closure_set(v___f_10409_, 0, v_toPure_10405_);
    lean_closure_set(v___f_10409_, 1, v_b_10402_);
    lean_closure_set(v___f_10409_, 2, v_f_10401_);
    lean_closure_set(v___f_10409_, 3, v_toBind_10404_);
    lean_closure_set(v___f_10409_, 4, v___f_10408_);
    v___x_10410_ = lean_apply_4(
        v_toBind_10404_,
        lean_box(0),
        lean_box(0),
        v___x_10407_,
        v___f_10409_,
    );
    return v___x_10410_;
}
pub unsafe fn l___private_Std_Sync_Channel_0__Std_CloseableChannel_Sync_forIn___redArg___lam__0(
    mut v_toPure_10411_: *mut LeanObject,
    mut v_inst_10412_: *mut LeanObject,
    mut v_inst_10413_: *mut LeanObject,
    mut v_ch_10414_: *mut LeanObject,
    mut v_f_10415_: *mut LeanObject,
    mut v_____do__lift_10416_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_____do__lift_10416_) == 0 {
        let mut v_a_10417_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_10418_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_f_10415_);
        lean_dec_ref(v_ch_10414_);
        lean_dec(v_inst_10413_);
        lean_dec_ref(v_inst_10412_);
        v_a_10417_ = lean_ctor_get(v_____do__lift_10416_, 0);
        lean_inc(v_a_10417_);
        lean_dec_ref_known(v_____do__lift_10416_, 1);
        v___x_10418_ = lean_apply_2(v_toPure_10411_, lean_box(0), v_a_10417_);
        return v___x_10418_;
    } else {
        let mut v_a_10419_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_10420_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_toPure_10411_);
        v_a_10419_ = lean_ctor_get(v_____do__lift_10416_, 0);
        lean_inc(v_a_10419_);
        lean_dec_ref_known(v_____do__lift_10416_, 1);
        v___x_10420_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Sync_forIn___redArg(
            v_inst_10412_,
            v_inst_10413_,
            v_ch_10414_,
            v_f_10415_,
            v_a_10419_,
        );
        return v___x_10420_;
    }
}
pub unsafe fn l___private_Std_Sync_Channel_0__Std_CloseableChannel_Sync_forIn(
    mut v_m_10421_: *mut LeanObject,
    mut v_00_u03b1_10422_: *mut LeanObject,
    mut v_00_u03b2_10423_: *mut LeanObject,
    mut v_inst_10424_: *mut LeanObject,
    mut v_inst_10425_: *mut LeanObject,
    mut v_ch_10426_: *mut LeanObject,
    mut v_f_10427_: *mut LeanObject,
    mut v_b_10428_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_10429_: *mut LeanObject = core::ptr::null_mut();
    v___x_10429_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Sync_forIn___redArg(
        v_inst_10424_,
        v_inst_10425_,
        v_ch_10426_,
        v_f_10427_,
        v_b_10428_,
    );
    return v___x_10429_;
}
pub unsafe fn l_Std_CloseableChannel_Sync_instForInOfMonadOfMonadLiftTBaseIO___private__1___redArg(
    mut v_inst_10430_: *mut LeanObject,
    mut v_inst_10431_: *mut LeanObject,
    mut v_ch_10432_: *mut LeanObject,
    mut v_b_10433_: *mut LeanObject,
    mut v_f_10434_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_10435_: *mut LeanObject = core::ptr::null_mut();
    v___x_10435_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Sync_forIn___redArg(
        v_inst_10430_,
        v_inst_10431_,
        v_ch_10432_,
        v_f_10434_,
        v_b_10433_,
    );
    return v___x_10435_;
}
pub unsafe fn l_Std_CloseableChannel_Sync_instForInOfMonadOfMonadLiftTBaseIO___private__1(
    mut v_m_10436_: *mut LeanObject,
    mut v_00_u03b1_10437_: *mut LeanObject,
    mut v_inst_10438_: *mut LeanObject,
    mut v_inst_10439_: *mut LeanObject,
    mut v_00_u03b2_10440_: *mut LeanObject,
    mut v_ch_10441_: *mut LeanObject,
    mut v_b_10442_: *mut LeanObject,
    mut v_f_10443_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_10444_: *mut LeanObject = core::ptr::null_mut();
    v___x_10444_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Sync_forIn___redArg(
        v_inst_10438_,
        v_inst_10439_,
        v_ch_10441_,
        v_f_10443_,
        v_b_10442_,
    );
    return v___x_10444_;
}
pub unsafe fn l_Std_CloseableChannel_Sync_instForInOfMonadOfMonadLiftTBaseIO___redArg___lam__0(
    mut v_inst_10445_: *mut LeanObject,
    mut v_inst_10446_: *mut LeanObject,
    mut v_00_u03b2_10447_: *mut LeanObject,
    mut v_ch_10448_: *mut LeanObject,
    mut v_b_10449_: *mut LeanObject,
    mut v_f_10450_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_10451_: *mut LeanObject = core::ptr::null_mut();
    v___x_10451_ = l___private_Std_Sync_Channel_0__Std_CloseableChannel_Sync_forIn___redArg(
        v_inst_10445_,
        v_inst_10446_,
        v_ch_10448_,
        v_f_10450_,
        v_b_10449_,
    );
    return v___x_10451_;
}
pub unsafe fn l_Std_CloseableChannel_Sync_instForInOfMonadOfMonadLiftTBaseIO___redArg(
    mut v_inst_10452_: *mut LeanObject,
    mut v_inst_10453_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_10454_: *mut LeanObject = core::ptr::null_mut();
    v___f_10454_ = lean_alloc_closure(
        l_Std_CloseableChannel_Sync_instForInOfMonadOfMonadLiftTBaseIO___redArg___lam__0
            as *mut core::ffi::c_void,
        6,
        2,
    );
    lean_closure_set(v___f_10454_, 0, v_inst_10452_);
    lean_closure_set(v___f_10454_, 1, v_inst_10453_);
    return v___f_10454_;
}
pub unsafe fn l_Std_CloseableChannel_Sync_instForInOfMonadOfMonadLiftTBaseIO(
    mut v_m_10455_: *mut LeanObject,
    mut v_00_u03b1_10456_: *mut LeanObject,
    mut v_inst_10457_: *mut LeanObject,
    mut v_inst_10458_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_10459_: *mut LeanObject = core::ptr::null_mut();
    v___f_10459_ = lean_alloc_closure(
        l_Std_CloseableChannel_Sync_instForInOfMonadOfMonadLiftTBaseIO___redArg___lam__0
            as *mut core::ffi::c_void,
        6,
        2,
    );
    lean_closure_set(v___f_10459_, 0, v_inst_10457_);
    lean_closure_set(v___f_10459_, 1, v_inst_10458_);
    return v___f_10459_;
}
pub unsafe fn l_Std_Channel_new___redArg(
    mut v_capacity_10460_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_10462_: *mut LeanObject = core::ptr::null_mut();
    v___x_10462_ = l_Std_CloseableChannel_new___redArg(v_capacity_10460_);
    return v___x_10462_;
}
pub unsafe fn l_Std_Channel_new___redArg___boxed(
    mut v_capacity_10463_: *mut LeanObject,
    mut v_a_10464_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_10465_: *mut LeanObject = core::ptr::null_mut();
    v_res_10465_ = l_Std_Channel_new___redArg(v_capacity_10463_);
    return v_res_10465_;
}
pub unsafe fn l_Std_Channel_new(
    mut v_00_u03b1_10466_: *mut LeanObject,
    mut v_capacity_10467_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_10469_: *mut LeanObject = core::ptr::null_mut();
    v___x_10469_ = l_Std_CloseableChannel_new___redArg(v_capacity_10467_);
    return v___x_10469_;
}
pub unsafe fn l_Std_Channel_new___boxed(
    mut v_00_u03b1_10470_: *mut LeanObject,
    mut v_capacity_10471_: *mut LeanObject,
    mut v_a_10472_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_10473_: *mut LeanObject = core::ptr::null_mut();
    v_res_10473_ = l_Std_Channel_new(v_00_u03b1_10470_, v_capacity_10471_);
    return v_res_10473_;
}
pub unsafe fn l_Std_Channel_trySend___redArg(
    mut v_ch_10474_: *mut LeanObject,
    mut v_v_10475_: *mut LeanObject,
) -> u8 {
    let mut v___x_10477_: u8 = 0;
    v___x_10477_ = l_Std_CloseableChannel_trySend___redArg(v_ch_10474_, v_v_10475_);
    return v___x_10477_;
}
pub unsafe fn l_Std_Channel_trySend___redArg___boxed(
    mut v_ch_10478_: *mut LeanObject,
    mut v_v_10479_: *mut LeanObject,
    mut v_a_10480_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_10481_: u8 = 0;
    let mut v_r_10482_: *mut LeanObject = core::ptr::null_mut();
    v_res_10481_ = l_Std_Channel_trySend___redArg(v_ch_10478_, v_v_10479_);
    v_r_10482_ = lean_box((v_res_10481_) as usize);
    return v_r_10482_;
}
pub unsafe fn l_Std_Channel_trySend(
    mut v_00_u03b1_10483_: *mut LeanObject,
    mut v_ch_10484_: *mut LeanObject,
    mut v_v_10485_: *mut LeanObject,
) -> u8 {
    let mut v___x_10487_: u8 = 0;
    v___x_10487_ = l_Std_CloseableChannel_trySend___redArg(v_ch_10484_, v_v_10485_);
    return v___x_10487_;
}
pub unsafe fn l_Std_Channel_trySend___boxed(
    mut v_00_u03b1_10488_: *mut LeanObject,
    mut v_ch_10489_: *mut LeanObject,
    mut v_v_10490_: *mut LeanObject,
    mut v_a_10491_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_10492_: u8 = 0;
    let mut v_r_10493_: *mut LeanObject = core::ptr::null_mut();
    v_res_10492_ = l_Std_Channel_trySend(v_00_u03b1_10488_, v_ch_10489_, v_v_10490_);
    v_r_10493_ = lean_box((v_res_10492_) as usize);
    return v_r_10493_;
}
pub unsafe fn _init_l_panic___at___00Std_Channel_send_spec__0___closed__0() -> *mut LeanObject {
    let mut v___x_10494_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_10495_: *mut LeanObject = core::ptr::null_mut();
    v___x_10494_ = lean_box(0);
    v___x_10495_ = lean_task_pure(v___x_10494_);
    return v___x_10495_;
}
pub unsafe fn l_panic___at___00Std_Channel_send_spec__0(
    mut v_msg_10496_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_10498_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_10499_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_10500_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_142__overap_10501_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_10502_: *mut LeanObject = core::ptr::null_mut();
    v___x_10498_ = l_instMonadBaseIO;
    v___x_10499_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_panic___at___00Std_Channel_send_spec__0___closed__0),
        core::ptr::addr_of_mut!(l_panic___at___00Std_Channel_send_spec__0___closed__0_once),
        _init_l_panic___at___00Std_Channel_send_spec__0___closed__0,
    );
    v___x_10500_ = l_instInhabitedOfMonad___redArg(v___x_10498_, v___x_10499_);
    v___x_142__overap_10501_ = lean_panic_fn_borrowed(v___x_10500_, v_msg_10496_);
    lean_dec(v___x_10500_);
    v___x_10502_ = lean_apply_1(v___x_142__overap_10501_, lean_box(0));
    return v___x_10502_;
}
pub unsafe fn l_panic___at___00Std_Channel_send_spec__0___boxed(
    mut v_msg_10503_: *mut LeanObject,
    mut v___y_10504_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_10505_: *mut LeanObject = core::ptr::null_mut();
    v_res_10505_ = l_panic___at___00Std_Channel_send_spec__0(v_msg_10503_);
    return v_res_10505_;
}
pub unsafe fn _init_l_Std_Channel_send___redArg___lam__0___closed__3() -> *mut LeanObject {
    let mut v___x_10509_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_10510_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_10511_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_10512_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_10513_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_10514_: *mut LeanObject = core::ptr::null_mut();
    v___x_10509_ = l_Std_Channel_send___redArg___lam__0___closed__2;
    v___x_10510_ = lean_unsigned_to_nat(21);
    v___x_10511_ = lean_unsigned_to_nat(869);
    v___x_10512_ = l_Std_Channel_send___redArg___lam__0___closed__1;
    v___x_10513_ = l_Std_Channel_send___redArg___lam__0___closed__0;
    v___x_10514_ = l_mkPanicMessageWithDecl(
        v___x_10513_,
        v___x_10512_,
        v___x_10511_,
        v___x_10510_,
        v___x_10509_,
    );
    return v___x_10514_;
}
pub unsafe fn l_Std_Channel_send___redArg___lam__0(
    mut v_x_10515_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_10515_) == 0 {
        let mut v___x_10517_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_10518_: *mut LeanObject = core::ptr::null_mut();
        v___x_10517_ = lean_obj_once(
            core::ptr::addr_of_mut!(l_Std_Channel_send___redArg___lam__0___closed__3),
            core::ptr::addr_of_mut!(l_Std_Channel_send___redArg___lam__0___closed__3_once),
            _init_l_Std_Channel_send___redArg___lam__0___closed__3,
        );
        v___x_10518_ = l_panic___at___00Std_Channel_send_spec__0(v___x_10517_);
        return v___x_10518_;
    } else {
        let mut v___x_10519_: *mut LeanObject = core::ptr::null_mut();
        v___x_10519_ = lean_obj_once(
            core::ptr::addr_of_mut!(l_Std_CloseableChannel_forAsync___redArg___lam__0___closed__0),
            core::ptr::addr_of_mut!(
                l_Std_CloseableChannel_forAsync___redArg___lam__0___closed__0_once
            ),
            _init_l_Std_CloseableChannel_forAsync___redArg___lam__0___closed__0,
        );
        return v___x_10519_;
    }
}
pub unsafe fn l_Std_Channel_send___redArg___lam__0___boxed(
    mut v_x_10520_: *mut LeanObject,
    mut v___y_10521_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_10522_: *mut LeanObject = core::ptr::null_mut();
    v_res_10522_ = l_Std_Channel_send___redArg___lam__0(v_x_10520_);
    lean_dec_ref(v_x_10520_);
    return v_res_10522_;
}
pub unsafe fn l_Std_Channel_send___redArg(
    mut v_ch_10524_: *mut LeanObject,
    mut v_v_10525_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_10527_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_10528_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_10529_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_10530_: u8 = 0;
    let mut v___x_10531_: *mut LeanObject = core::ptr::null_mut();
    v___x_10527_ = l_Std_CloseableChannel_send___redArg(v_ch_10524_, v_v_10525_);
    v___f_10528_ = l_Std_Channel_send___redArg___closed__0;
    v___x_10529_ = lean_unsigned_to_nat(0);
    v___x_10530_ = 1;
    v___x_10531_ = lean_io_bind_task(v___x_10527_, v___f_10528_, v___x_10529_, v___x_10530_);
    return v___x_10531_;
}
pub unsafe fn l_Std_Channel_send___redArg___boxed(
    mut v_ch_10532_: *mut LeanObject,
    mut v_v_10533_: *mut LeanObject,
    mut v_a_10534_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_10535_: *mut LeanObject = core::ptr::null_mut();
    v_res_10535_ = l_Std_Channel_send___redArg(v_ch_10532_, v_v_10533_);
    return v_res_10535_;
}
pub unsafe fn l_Std_Channel_send(
    mut v_00_u03b1_10536_: *mut LeanObject,
    mut v_ch_10537_: *mut LeanObject,
    mut v_v_10538_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_10540_: *mut LeanObject = core::ptr::null_mut();
    v___x_10540_ = l_Std_Channel_send___redArg(v_ch_10537_, v_v_10538_);
    return v___x_10540_;
}
pub unsafe fn l_Std_Channel_send___boxed(
    mut v_00_u03b1_10541_: *mut LeanObject,
    mut v_ch_10542_: *mut LeanObject,
    mut v_v_10543_: *mut LeanObject,
    mut v_a_10544_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_10545_: *mut LeanObject = core::ptr::null_mut();
    v_res_10545_ = l_Std_Channel_send(v_00_u03b1_10541_, v_ch_10542_, v_v_10543_);
    return v_res_10545_;
}
pub unsafe fn l_Std_Channel_tryRecv___redArg(mut v_ch_10546_: *mut LeanObject) -> *mut LeanObject {
    let mut v___x_10548_: *mut LeanObject = core::ptr::null_mut();
    v___x_10548_ = l_Std_CloseableChannel_tryRecv___redArg(v_ch_10546_);
    return v___x_10548_;
}
pub unsafe fn l_Std_Channel_tryRecv___redArg___boxed(
    mut v_ch_10549_: *mut LeanObject,
    mut v_a_10550_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_10551_: *mut LeanObject = core::ptr::null_mut();
    v_res_10551_ = l_Std_Channel_tryRecv___redArg(v_ch_10549_);
    return v_res_10551_;
}
pub unsafe fn l_Std_Channel_tryRecv(
    mut v_00_u03b1_10552_: *mut LeanObject,
    mut v_ch_10553_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_10555_: *mut LeanObject = core::ptr::null_mut();
    v___x_10555_ = l_Std_CloseableChannel_tryRecv___redArg(v_ch_10553_);
    return v___x_10555_;
}
pub unsafe fn l_Std_Channel_tryRecv___boxed(
    mut v_00_u03b1_10556_: *mut LeanObject,
    mut v_ch_10557_: *mut LeanObject,
    mut v_a_10558_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_10559_: *mut LeanObject = core::ptr::null_mut();
    v_res_10559_ = l_Std_Channel_tryRecv(v_00_u03b1_10556_, v_ch_10557_);
    return v_res_10559_;
}
pub unsafe fn _init_l_Std_Channel_recv___redArg___lam__0___closed__1() -> *mut LeanObject {
    let mut v___x_10561_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_10562_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_10563_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_10564_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_10565_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_10566_: *mut LeanObject = core::ptr::null_mut();
    v___x_10561_ = l_Std_Channel_send___redArg___lam__0___closed__2;
    v___x_10562_ = lean_unsigned_to_nat(16);
    v___x_10563_ = lean_unsigned_to_nat(880);
    v___x_10564_ = l_Std_Channel_recv___redArg___lam__0___closed__0;
    v___x_10565_ = l_Std_Channel_send___redArg___lam__0___closed__0;
    v___x_10566_ = l_mkPanicMessageWithDecl(
        v___x_10565_,
        v___x_10564_,
        v___x_10563_,
        v___x_10562_,
        v___x_10561_,
    );
    return v___x_10566_;
}
pub unsafe fn l_Std_Channel_recv___redArg___lam__0(
    mut v___x_10567_: *mut LeanObject,
    mut v_x_10568_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_10568_) == 0 {
        let mut v___x_10570_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_140__overap_10571_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_10572_: *mut LeanObject = core::ptr::null_mut();
        v___x_10570_ = lean_obj_once(
            core::ptr::addr_of_mut!(l_Std_Channel_recv___redArg___lam__0___closed__1),
            core::ptr::addr_of_mut!(l_Std_Channel_recv___redArg___lam__0___closed__1_once),
            _init_l_Std_Channel_recv___redArg___lam__0___closed__1,
        );
        v___x_140__overap_10571_ = l_panic___redArg(v___x_10567_, v___x_10570_);
        v___x_10572_ = lean_apply_1(v___x_140__overap_10571_, lean_box(0));
        return v___x_10572_;
    } else {
        let mut v_val_10573_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_10574_: *mut LeanObject = core::ptr::null_mut();
        v_val_10573_ = lean_ctor_get(v_x_10568_, 0);
        lean_inc(v_val_10573_);
        lean_dec_ref_known(v_x_10568_, 1);
        v___x_10574_ = lean_task_pure(v_val_10573_);
        return v___x_10574_;
    }
}
pub unsafe fn l_Std_Channel_recv___redArg___lam__0___boxed(
    mut v___x_10575_: *mut LeanObject,
    mut v_x_10576_: *mut LeanObject,
    mut v___y_10577_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_10578_: *mut LeanObject = core::ptr::null_mut();
    v_res_10578_ = l_Std_Channel_recv___redArg___lam__0(v___x_10575_, v_x_10576_);
    lean_dec_ref(v___x_10575_);
    return v_res_10578_;
}
pub unsafe fn l_Std_Channel_recv___redArg(
    mut v_inst_10579_: *mut LeanObject,
    mut v_ch_10580_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_10582_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_10583_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_10584_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_10585_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_10586_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_10587_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_10588_: u8 = 0;
    let mut v___x_10589_: *mut LeanObject = core::ptr::null_mut();
    v___x_10582_ = l_instMonadBaseIO;
    v___x_10583_ = l_Std_CloseableChannel_recv___redArg(v_ch_10580_);
    v___x_10584_ = lean_task_pure(v_inst_10579_);
    v___x_10585_ = l_instInhabitedOfMonad___redArg(v___x_10582_, v___x_10584_);
    v___f_10586_ = lean_alloc_closure(
        l_Std_Channel_recv___redArg___lam__0___boxed as *mut core::ffi::c_void,
        3,
        1,
    );
    lean_closure_set(v___f_10586_, 0, v___x_10585_);
    v___x_10587_ = lean_unsigned_to_nat(0);
    v___x_10588_ = 1;
    v___x_10589_ = lean_io_bind_task(v___x_10583_, v___f_10586_, v___x_10587_, v___x_10588_);
    return v___x_10589_;
}
pub unsafe fn l_Std_Channel_recv___redArg___boxed(
    mut v_inst_10590_: *mut LeanObject,
    mut v_ch_10591_: *mut LeanObject,
    mut v_a_10592_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_10593_: *mut LeanObject = core::ptr::null_mut();
    v_res_10593_ = l_Std_Channel_recv___redArg(v_inst_10590_, v_ch_10591_);
    return v_res_10593_;
}
pub unsafe fn l_Std_Channel_recv(
    mut v_00_u03b1_10594_: *mut LeanObject,
    mut v_inst_10595_: *mut LeanObject,
    mut v_ch_10596_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_10598_: *mut LeanObject = core::ptr::null_mut();
    v___x_10598_ = l_Std_Channel_recv___redArg(v_inst_10595_, v_ch_10596_);
    return v___x_10598_;
}
pub unsafe fn l_Std_Channel_recv___boxed(
    mut v_00_u03b1_10599_: *mut LeanObject,
    mut v_inst_10600_: *mut LeanObject,
    mut v_ch_10601_: *mut LeanObject,
    mut v_a_10602_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_10603_: *mut LeanObject = core::ptr::null_mut();
    v_res_10603_ = l_Std_Channel_recv(v_00_u03b1_10599_, v_inst_10600_, v_ch_10601_);
    return v_res_10603_;
}
pub unsafe fn l_Std_Channel_recvSelector___redArg___lam__0(
    mut v_ch_10604_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_10606_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_10607_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_10608_: *mut LeanObject = core::ptr::null_mut();
    v___x_10606_ = l_Std_CloseableChannel_tryRecv___redArg(v_ch_10604_);
    v___x_10607_ = lean_alloc_ctor(1, 1, (0) as u32);
    lean_ctor_set(v___x_10607_, 0, v___x_10606_);
    v___x_10608_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_10608_, 0, v___x_10607_);
    return v___x_10608_;
}
pub unsafe fn l_Std_Channel_recvSelector___redArg___lam__0___boxed(
    mut v_ch_10609_: *mut LeanObject,
    mut v___y_10610_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_10611_: *mut LeanObject = core::ptr::null_mut();
    v_res_10611_ = l_Std_Channel_recvSelector___redArg___lam__0(v_ch_10609_);
    return v_res_10611_;
}
pub unsafe fn _init_l_Std_Channel_recvSelector___redArg___lam__1___closed__3() -> *mut LeanObject {
    let mut v___x_10615_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_10616_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_10617_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_10618_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_10619_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_10620_: *mut LeanObject = core::ptr::null_mut();
    v___x_10615_ = l_Std_Channel_recvSelector___redArg___lam__1___closed__2;
    v___x_10616_ = lean_unsigned_to_nat(14);
    v___x_10617_ = lean_unsigned_to_nat(22);
    v___x_10618_ = l_Std_Channel_recvSelector___redArg___lam__1___closed__1;
    v___x_10619_ = l_Std_Channel_recvSelector___redArg___lam__1___closed__0;
    v___x_10620_ = l_mkPanicMessageWithDecl(
        v___x_10619_,
        v___x_10618_,
        v___x_10617_,
        v___x_10616_,
        v___x_10615_,
    );
    return v___x_10620_;
}
pub unsafe fn l_Std_Channel_recvSelector___redArg___lam__1(
    mut v_promise_10621_: *mut LeanObject,
    mut v_inst_10622_: *mut LeanObject,
    mut v_x_10623_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___y_10626_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_10627_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_10628_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_10630_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_10631_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_10632_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_10633_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_10634_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_10635_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_10637_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_10638_: u8 = 0;
    let mut v___x_10640_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_10641_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_10642_: u8 = 0;
    let mut v_a_10643_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_10644_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_10645_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_10646_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_10623_) == 0 {
                    v___x_10632_ = lean_box(0);
                    v___x_10633_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_10633_, 0, v___x_10632_);
                    return v___x_10633_;
                } else {
                    v_val_10634_ = lean_ctor_get(v_x_10623_, 0);
                    lean_inc(v_val_10634_);
                    lean_dec_ref_known(v_x_10623_, 1);
                    if lean_obj_tag(v_val_10634_) == 0 {
                        v_a_10635_ = lean_ctor_get(v_val_10634_, 0);
                        v_isSharedCheck_10642_ = (!lean_is_exclusive(v_val_10634_)) as u8;
                        if v_isSharedCheck_10642_ == 0 {
                            v___x_10637_ = v_val_10634_;
                            v_isShared_10638_ = v_isSharedCheck_10642_;
                            state = 3;
                            continue;
                        } else {
                            lean_inc(v_a_10635_);
                            lean_dec(v_val_10634_);
                            v___x_10637_ = lean_box(0);
                            v_isShared_10638_ = v_isSharedCheck_10642_;
                            state = 3;
                            continue;
                        }
                    } else {
                        v_a_10643_ = lean_ctor_get(v_val_10634_, 0);
                        lean_inc(v_a_10643_);
                        lean_dec_ref_known(v_val_10634_, 1);
                        if lean_obj_tag(v_a_10643_) == 0 {
                            v___x_10644_ = lean_obj_once(
                                core::ptr::addr_of_mut!(
                                    l_Std_Channel_recvSelector___redArg___lam__1___closed__3
                                ),
                                core::ptr::addr_of_mut!(
                                    l_Std_Channel_recvSelector___redArg___lam__1___closed__3_once
                                ),
                                _init_l_Std_Channel_recvSelector___redArg___lam__1___closed__3,
                            );
                            v___x_10645_ = l_panic___redArg(v_inst_10622_, v___x_10644_);
                            v___y_10630_ = v___x_10645_;
                            state = 2;
                            continue;
                        } else {
                            v_val_10646_ = lean_ctor_get(v_a_10643_, 0);
                            lean_inc(v_val_10646_);
                            lean_dec_ref_known(v_a_10643_, 1);
                            v___y_10630_ = v_val_10646_;
                            state = 2;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v___x_10627_ = lean_io_promise_resolve(v___y_10626_, v_promise_10621_);
                v___x_10628_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_10628_, 0, v___x_10627_);
                return v___x_10628_;
            }
            2 => {
                v___x_10631_ = lean_alloc_ctor(1, 1, (0) as u32);
                lean_ctor_set(v___x_10631_, 0, v___y_10630_);
                v___y_10626_ = v___x_10631_;
                state = 1;
                continue;
            }
            3 => {
                if v_isShared_10638_ == 0 {
                    v___x_10640_ = v___x_10637_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_10641_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_10641_, 0, v_a_10635_);
                    v___x_10640_ = v_reuseFailAlloc_10641_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___y_10626_ = v___x_10640_;
                state = 1;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Channel_recvSelector___redArg___lam__1___boxed(
    mut v_promise_10647_: *mut LeanObject,
    mut v_inst_10648_: *mut LeanObject,
    mut v_x_10649_: *mut LeanObject,
    mut v___y_10650_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_10651_: *mut LeanObject = core::ptr::null_mut();
    v_res_10651_ =
        l_Std_Channel_recvSelector___redArg___lam__1(v_promise_10647_, v_inst_10648_, v_x_10649_);
    lean_dec(v_inst_10648_);
    lean_dec(v_promise_10647_);
    return v_res_10651_;
}
pub unsafe fn l_Std_Channel_recvSelector___redArg___lam__2(
    mut v_a_10652_: *mut LeanObject,
    mut v___f_10653_: *mut LeanObject,
    mut v_x_10654_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_val_10657_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_10658_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_10659_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_10661_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_10662_: u8 = 0;
    let mut v___x_10663_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_10664_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_10665_: u8 = 0;
    let mut v___x_10666_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_10667_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_10669_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_10670_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_10671_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_10673_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_10674_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_10675_: u8 = 0;
    let mut v_unused_10676_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_10654_) == 0 {
                    lean_dec_ref(v___f_10653_);
                    v___x_10659_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_10659_, 0, v_x_10654_);
                    return v___x_10659_;
                } else {
                    v_isSharedCheck_10675_ = (!lean_is_exclusive(v_x_10654_)) as u8;
                    if v_isSharedCheck_10675_ == 0 {
                        v_unused_10676_ = lean_ctor_get(v_x_10654_, 0);
                        lean_dec(v_unused_10676_);
                        v___x_10661_ = v_x_10654_;
                        v_isShared_10662_ = v_isSharedCheck_10675_;
                        state = 2;
                        continue;
                    } else {
                        lean_dec(v_x_10654_);
                        v___x_10661_ = lean_box(0);
                        v_isShared_10662_ = v_isSharedCheck_10675_;
                        state = 2;
                        continue;
                    }
                }
            }
            1 => {
                v___x_10658_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_10658_, 0, v_val_10657_);
                return v___x_10658_;
            }
            2 => {
                v___x_10663_ = lean_io_promise_result_opt(v_a_10652_);
                v___x_10664_ = lean_unsigned_to_nat(0);
                v___x_10665_ = 1;
                v___x_10666_ = l_EIO_chainTask___redArg(
                    v___x_10663_,
                    v___f_10653_,
                    v___x_10664_,
                    v___x_10665_,
                );
                if lean_obj_tag(v___x_10666_) == 0 {
                    v_a_10667_ = lean_ctor_get(v___x_10666_, 0);
                    lean_inc(v_a_10667_);
                    lean_dec_ref_known(v___x_10666_, 1);
                    if v_isShared_10662_ == 0 {
                        lean_ctor_set(v___x_10661_, 0, v_a_10667_);
                        v___x_10669_ = v___x_10661_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_10670_ = lean_alloc_ctor(1, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_10670_, 0, v_a_10667_);
                        v___x_10669_ = v_reuseFailAlloc_10670_;
                        state = 3;
                        continue;
                    }
                } else {
                    v_a_10671_ = lean_ctor_get(v___x_10666_, 0);
                    lean_inc(v_a_10671_);
                    lean_dec_ref_known(v___x_10666_, 1);
                    if v_isShared_10662_ == 0 {
                        lean_ctor_set_tag(v___x_10661_, 0);
                        lean_ctor_set(v___x_10661_, 0, v_a_10671_);
                        v___x_10673_ = v___x_10661_;
                        state = 4;
                        continue;
                    } else {
                        v_reuseFailAlloc_10674_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_10674_, 0, v_a_10671_);
                        v___x_10673_ = v_reuseFailAlloc_10674_;
                        state = 4;
                        continue;
                    }
                }
            }
            3 => {
                v_val_10657_ = v___x_10669_;
                state = 1;
                continue;
            }
            4 => {
                v_val_10657_ = v___x_10673_;
                state = 1;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Channel_recvSelector___redArg___lam__2___boxed(
    mut v_a_10677_: *mut LeanObject,
    mut v___f_10678_: *mut LeanObject,
    mut v_x_10679_: *mut LeanObject,
    mut v___y_10680_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_10681_: *mut LeanObject = core::ptr::null_mut();
    v_res_10681_ =
        l_Std_Channel_recvSelector___redArg___lam__2(v_a_10677_, v___f_10678_, v_x_10679_);
    lean_dec(v_a_10677_);
    return v_res_10681_;
}
pub unsafe fn l_Std_Channel_recvSelector___redArg___lam__3(
    mut v_sel_10682_: *mut LeanObject,
    mut v_finished_10683_: *mut LeanObject,
    mut v___f_10684_: *mut LeanObject,
    mut v_x_10685_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_10687_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_10689_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_10690_: u8 = 0;
    let mut v___x_10692_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_10693_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_10694_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_10695_: u8 = 0;
    let mut v_a_10696_: *mut LeanObject = core::ptr::null_mut();
    let mut v_registerFn_10697_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_10698_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_10699_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_10700_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_10701_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_10702_: u8 = 0;
    let mut v___x_10703_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_10685_) == 0 {
                    lean_dec_ref(v___f_10684_);
                    lean_dec(v_finished_10683_);
                    lean_dec_ref(v_sel_10682_);
                    v_a_10687_ = lean_ctor_get(v_x_10685_, 0);
                    v_isSharedCheck_10695_ = (!lean_is_exclusive(v_x_10685_)) as u8;
                    if v_isSharedCheck_10695_ == 0 {
                        v___x_10689_ = v_x_10685_;
                        v_isShared_10690_ = v_isSharedCheck_10695_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_10687_);
                        lean_dec(v_x_10685_);
                        v___x_10689_ = lean_box(0);
                        v_isShared_10690_ = v_isSharedCheck_10695_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_10696_ = lean_ctor_get(v_x_10685_, 0);
                    lean_inc_n(v_a_10696_, 2);
                    lean_dec_ref_known(v_x_10685_, 1);
                    v_registerFn_10697_ = lean_ctor_get(v_sel_10682_, 1);
                    lean_inc_ref(v_registerFn_10697_);
                    lean_dec_ref(v_sel_10682_);
                    v___x_10698_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v___x_10698_, 0, v_finished_10683_);
                    lean_ctor_set(v___x_10698_, 1, v_a_10696_);
                    v___x_10699_ = lean_apply_2(v_registerFn_10697_, v___x_10698_, lean_box(0));
                    v___f_10700_ = lean_alloc_closure(
                        l_Std_Channel_recvSelector___redArg___lam__2___boxed
                            as *mut core::ffi::c_void,
                        4,
                        2,
                    );
                    lean_closure_set(v___f_10700_, 0, v_a_10696_);
                    lean_closure_set(v___f_10700_, 1, v___f_10684_);
                    v___x_10701_ = lean_unsigned_to_nat(0);
                    v___x_10702_ = 0;
                    v___x_10703_ =
                        l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(
                            lean_box(0),
                            lean_box(0),
                            v___x_10701_,
                            v___x_10702_,
                            v___x_10699_,
                            v___f_10700_,
                        );
                    return v___x_10703_;
                }
            }
            1 => {
                if v_isShared_10690_ == 0 {
                    v___x_10692_ = v___x_10689_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_10694_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_10694_, 0, v_a_10687_);
                    v___x_10692_ = v_reuseFailAlloc_10694_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_10693_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_10693_, 0, v___x_10692_);
                return v___x_10693_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Channel_recvSelector___redArg___lam__3___boxed(
    mut v_sel_10704_: *mut LeanObject,
    mut v_finished_10705_: *mut LeanObject,
    mut v___f_10706_: *mut LeanObject,
    mut v_x_10707_: *mut LeanObject,
    mut v___y_10708_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_10709_: *mut LeanObject = core::ptr::null_mut();
    v_res_10709_ = l_Std_Channel_recvSelector___redArg___lam__3(
        v_sel_10704_,
        v_finished_10705_,
        v___f_10706_,
        v_x_10707_,
    );
    return v_res_10709_;
}
pub unsafe fn l_Std_Channel_recvSelector___redArg___lam__4(
    mut v_inst_10710_: *mut LeanObject,
    mut v_sel_10711_: *mut LeanObject,
    mut v_waiter_10712_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_10714_: *mut LeanObject = core::ptr::null_mut();
    let mut v_finished_10715_: *mut LeanObject = core::ptr::null_mut();
    let mut v_promise_10716_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_10717_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_10718_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_10719_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_10720_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_10721_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_10722_: u8 = 0;
    let mut v___x_10723_: *mut LeanObject = core::ptr::null_mut();
    v___x_10714_ = lean_io_promise_new();
    v_finished_10715_ = lean_ctor_get(v_waiter_10712_, 0);
    lean_inc(v_finished_10715_);
    v_promise_10716_ = lean_ctor_get(v_waiter_10712_, 1);
    lean_inc(v_promise_10716_);
    lean_dec_ref(v_waiter_10712_);
    v___f_10717_ = lean_alloc_closure(
        l_Std_Channel_recvSelector___redArg___lam__1___boxed as *mut core::ffi::c_void,
        4,
        2,
    );
    lean_closure_set(v___f_10717_, 0, v_promise_10716_);
    lean_closure_set(v___f_10717_, 1, v_inst_10710_);
    v___f_10718_ = lean_alloc_closure(
        l_Std_Channel_recvSelector___redArg___lam__3___boxed as *mut core::ffi::c_void,
        5,
        3,
    );
    lean_closure_set(v___f_10718_, 0, v_sel_10711_);
    lean_closure_set(v___f_10718_, 1, v_finished_10715_);
    lean_closure_set(v___f_10718_, 2, v___f_10717_);
    v___x_10719_ = lean_alloc_ctor(1, 1, (0) as u32);
    lean_ctor_set(v___x_10719_, 0, v___x_10714_);
    v___x_10720_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_10720_, 0, v___x_10719_);
    v___x_10721_ = lean_unsigned_to_nat(0);
    v___x_10722_ = 0;
    v___x_10723_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(
        lean_box(0),
        lean_box(0),
        v___x_10721_,
        v___x_10722_,
        v___x_10720_,
        v___f_10718_,
    );
    return v___x_10723_;
}
pub unsafe fn l_Std_Channel_recvSelector___redArg___lam__4___boxed(
    mut v_inst_10724_: *mut LeanObject,
    mut v_sel_10725_: *mut LeanObject,
    mut v_waiter_10726_: *mut LeanObject,
    mut v___y_10727_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_10728_: *mut LeanObject = core::ptr::null_mut();
    v_res_10728_ =
        l_Std_Channel_recvSelector___redArg___lam__4(v_inst_10724_, v_sel_10725_, v_waiter_10726_);
    return v_res_10728_;
}
pub unsafe fn l_Std_Channel_recvSelector___redArg(
    mut v_inst_10729_: *mut LeanObject,
    mut v_ch_10730_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sel_10731_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unregisterFn_10732_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_10733_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_10734_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_10735_: *mut LeanObject = core::ptr::null_mut();
    lean_inc_ref(v_ch_10730_);
    v_sel_10731_ = l_Std_CloseableChannel_recvSelector___redArg(v_ch_10730_);
    v_unregisterFn_10732_ = lean_ctor_get(v_sel_10731_, 2);
    lean_inc_ref(v_unregisterFn_10732_);
    v___f_10733_ = lean_alloc_closure(
        l_Std_Channel_recvSelector___redArg___lam__0___boxed as *mut core::ffi::c_void,
        2,
        1,
    );
    lean_closure_set(v___f_10733_, 0, v_ch_10730_);
    v___f_10734_ = lean_alloc_closure(
        l_Std_Channel_recvSelector___redArg___lam__4___boxed as *mut core::ffi::c_void,
        4,
        2,
    );
    lean_closure_set(v___f_10734_, 0, v_inst_10729_);
    lean_closure_set(v___f_10734_, 1, v_sel_10731_);
    v___x_10735_ = lean_alloc_ctor(0, 3, (0) as u32);
    lean_ctor_set(v___x_10735_, 0, v___f_10733_);
    lean_ctor_set(v___x_10735_, 1, v___f_10734_);
    lean_ctor_set(v___x_10735_, 2, v_unregisterFn_10732_);
    return v___x_10735_;
}
pub unsafe fn l_Std_Channel_recvSelector(
    mut v_00_u03b1_10736_: *mut LeanObject,
    mut v_inst_10737_: *mut LeanObject,
    mut v_ch_10738_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_10739_: *mut LeanObject = core::ptr::null_mut();
    v___x_10739_ = l_Std_Channel_recvSelector___redArg(v_inst_10737_, v_ch_10738_);
    return v___x_10739_;
}
pub unsafe fn l_Std_Channel_forAsync___redArg___lam__0___boxed(
    mut v_f_10740_: *mut LeanObject,
    mut v_inst_10741_: *mut LeanObject,
    mut v_ch_10742_: *mut LeanObject,
    mut v_prio_10743_: *mut LeanObject,
    mut v_v_10744_: *mut LeanObject,
    mut v___y_10745_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_10746_: *mut LeanObject = core::ptr::null_mut();
    v_res_10746_ = l_Std_Channel_forAsync___redArg___lam__0(
        v_f_10740_,
        v_inst_10741_,
        v_ch_10742_,
        v_prio_10743_,
        v_v_10744_,
    );
    return v_res_10746_;
}
pub unsafe fn l_Std_Channel_forAsync___redArg(
    mut v_inst_10747_: *mut LeanObject,
    mut v_f_10748_: *mut LeanObject,
    mut v_ch_10749_: *mut LeanObject,
    mut v_prio_10750_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_10752_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_10753_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_10754_: u8 = 0;
    let mut v___x_10755_: *mut LeanObject = core::ptr::null_mut();
    lean_inc_ref(v_ch_10749_);
    lean_inc(v_inst_10747_);
    v___x_10752_ = l_Std_Channel_recv___redArg(v_inst_10747_, v_ch_10749_);
    lean_inc(v_prio_10750_);
    v___f_10753_ = lean_alloc_closure(
        l_Std_Channel_forAsync___redArg___lam__0___boxed as *mut core::ffi::c_void,
        6,
        4,
    );
    lean_closure_set(v___f_10753_, 0, v_f_10748_);
    lean_closure_set(v___f_10753_, 1, v_inst_10747_);
    lean_closure_set(v___f_10753_, 2, v_ch_10749_);
    lean_closure_set(v___f_10753_, 3, v_prio_10750_);
    v___x_10754_ = 0;
    v___x_10755_ = lean_io_bind_task(v___x_10752_, v___f_10753_, v_prio_10750_, v___x_10754_);
    return v___x_10755_;
}
pub unsafe fn l_Std_Channel_forAsync___redArg___lam__0(
    mut v_f_10756_: *mut LeanObject,
    mut v_inst_10757_: *mut LeanObject,
    mut v_ch_10758_: *mut LeanObject,
    mut v_prio_10759_: *mut LeanObject,
    mut v_v_10760_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_10762_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_10763_: *mut LeanObject = core::ptr::null_mut();
    lean_inc_ref(v_f_10756_);
    v___x_10762_ = lean_apply_2(v_f_10756_, v_v_10760_, lean_box(0));
    v___x_10763_ =
        l_Std_Channel_forAsync___redArg(v_inst_10757_, v_f_10756_, v_ch_10758_, v_prio_10759_);
    return v___x_10763_;
}
pub unsafe fn l_Std_Channel_forAsync___redArg___boxed(
    mut v_inst_10764_: *mut LeanObject,
    mut v_f_10765_: *mut LeanObject,
    mut v_ch_10766_: *mut LeanObject,
    mut v_prio_10767_: *mut LeanObject,
    mut v_a_10768_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_10769_: *mut LeanObject = core::ptr::null_mut();
    v_res_10769_ =
        l_Std_Channel_forAsync___redArg(v_inst_10764_, v_f_10765_, v_ch_10766_, v_prio_10767_);
    return v_res_10769_;
}
pub unsafe fn l_Std_Channel_forAsync(
    mut v_00_u03b1_10770_: *mut LeanObject,
    mut v_inst_10771_: *mut LeanObject,
    mut v_f_10772_: *mut LeanObject,
    mut v_ch_10773_: *mut LeanObject,
    mut v_prio_10774_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_10776_: *mut LeanObject = core::ptr::null_mut();
    v___x_10776_ =
        l_Std_Channel_forAsync___redArg(v_inst_10771_, v_f_10772_, v_ch_10773_, v_prio_10774_);
    return v___x_10776_;
}
pub unsafe fn l_Std_Channel_forAsync___boxed(
    mut v_00_u03b1_10777_: *mut LeanObject,
    mut v_inst_10778_: *mut LeanObject,
    mut v_f_10779_: *mut LeanObject,
    mut v_ch_10780_: *mut LeanObject,
    mut v_prio_10781_: *mut LeanObject,
    mut v_a_10782_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_10783_: *mut LeanObject = core::ptr::null_mut();
    v_res_10783_ = l_Std_Channel_forAsync(
        v_00_u03b1_10777_,
        v_inst_10778_,
        v_f_10779_,
        v_ch_10780_,
        v_prio_10781_,
    );
    return v_res_10783_;
}
pub unsafe fn l_Std_Channel_instAsyncStreamOfInhabited___redArg___lam__0(
    mut v_inst_10784_: *mut LeanObject,
    mut v_channel_10785_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_10786_: *mut LeanObject = core::ptr::null_mut();
    v___x_10786_ = l_Std_Channel_recvSelector___redArg(v_inst_10784_, v_channel_10785_);
    return v___x_10786_;
}
pub unsafe fn l_Std_Channel_instAsyncStreamOfInhabited___redArg(
    mut v_inst_10787_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_10788_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_10789_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_10790_: *mut LeanObject = core::ptr::null_mut();
    v___f_10788_ = lean_alloc_closure(
        l_Std_Channel_instAsyncStreamOfInhabited___redArg___lam__0 as *mut core::ffi::c_void,
        2,
        1,
    );
    lean_closure_set(v___f_10788_, 0, v_inst_10787_);
    v___f_10789_ = l_Std_CloseableChannel_instAsyncStreamOptionOfInhabited___closed__1;
    v___x_10790_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_10790_, 0, v___f_10788_);
    lean_ctor_set(v___x_10790_, 1, v___f_10789_);
    return v___x_10790_;
}
pub unsafe fn l_Std_Channel_instAsyncStreamOfInhabited(
    mut v_00_u03b1_10791_: *mut LeanObject,
    mut v_inst_10792_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_10793_: *mut LeanObject = core::ptr::null_mut();
    v___x_10793_ = l_Std_Channel_instAsyncStreamOfInhabited___redArg(v_inst_10792_);
    return v___x_10793_;
}
pub unsafe fn l_Std_Channel_instAsyncReadOfInhabited___redArg___lam__0(
    mut v_a_10794_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_10795_: *mut LeanObject = core::ptr::null_mut();
    v___x_10795_ = lean_alloc_ctor(1, 1, (0) as u32);
    lean_ctor_set(v___x_10795_, 0, v_a_10794_);
    return v___x_10795_;
}
pub unsafe fn l_Std_Channel_instAsyncReadOfInhabited___redArg___lam__1(
    mut v___f_10796_: *mut LeanObject,
    mut v_x_10797_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_10799_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_10801_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_10802_: u8 = 0;
    let mut v___x_10804_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_10805_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_10806_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_10807_: u8 = 0;
    let mut v_a_10808_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_10809_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_10811_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_10812_: u8 = 0;
    let mut v___x_10814_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_10815_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_10816_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_10817_: u8 = 0;
    let mut v_a_10818_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_10819_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_10820_: u8 = 0;
    let mut v___x_10821_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_10822_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_10797_) == 0 {
                    lean_dec_ref(v___f_10796_);
                    v_a_10799_ = lean_ctor_get(v_x_10797_, 0);
                    v_isSharedCheck_10807_ = (!lean_is_exclusive(v_x_10797_)) as u8;
                    if v_isSharedCheck_10807_ == 0 {
                        v___x_10801_ = v_x_10797_;
                        v_isShared_10802_ = v_isSharedCheck_10807_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_10799_);
                        lean_dec(v_x_10797_);
                        v___x_10801_ = lean_box(0);
                        v_isShared_10802_ = v_isSharedCheck_10807_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_10808_ = lean_ctor_get(v_x_10797_, 0);
                    lean_inc(v_a_10808_);
                    lean_dec_ref_known(v_x_10797_, 1);
                    if lean_obj_tag(v_a_10808_) == 0 {
                        lean_dec_ref(v___f_10796_);
                        v_a_10809_ = lean_ctor_get(v_a_10808_, 0);
                        v_isSharedCheck_10817_ = (!lean_is_exclusive(v_a_10808_)) as u8;
                        if v_isSharedCheck_10817_ == 0 {
                            v___x_10811_ = v_a_10808_;
                            v_isShared_10812_ = v_isSharedCheck_10817_;
                            state = 3;
                            continue;
                        } else {
                            lean_inc(v_a_10809_);
                            lean_dec(v_a_10808_);
                            v___x_10811_ = lean_box(0);
                            v_isShared_10812_ = v_isSharedCheck_10817_;
                            state = 3;
                            continue;
                        }
                    } else {
                        v_a_10818_ = lean_ctor_get(v_a_10808_, 0);
                        lean_inc(v_a_10818_);
                        lean_dec_ref_known(v_a_10808_, 1);
                        v___x_10819_ = lean_unsigned_to_nat(0);
                        v___x_10820_ = 0;
                        v___x_10821_ =
                            lean_task_map(v___f_10796_, v_a_10818_, v___x_10819_, v___x_10820_);
                        v___x_10822_ = lean_alloc_ctor(1, 1, (0) as u32);
                        lean_ctor_set(v___x_10822_, 0, v___x_10821_);
                        return v___x_10822_;
                    }
                }
            }
            1 => {
                if v_isShared_10802_ == 0 {
                    v___x_10804_ = v___x_10801_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_10806_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_10806_, 0, v_a_10799_);
                    v___x_10804_ = v_reuseFailAlloc_10806_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_10805_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_10805_, 0, v___x_10804_);
                return v___x_10805_;
            }
            3 => {
                if v_isShared_10812_ == 0 {
                    v___x_10814_ = v___x_10811_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_10816_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_10816_, 0, v_a_10809_);
                    v___x_10814_ = v_reuseFailAlloc_10816_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_10815_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_10815_, 0, v___x_10814_);
                return v___x_10815_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Channel_instAsyncReadOfInhabited___redArg___lam__1___boxed(
    mut v___f_10823_: *mut LeanObject,
    mut v_x_10824_: *mut LeanObject,
    mut v___y_10825_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_10826_: *mut LeanObject = core::ptr::null_mut();
    v_res_10826_ =
        l_Std_Channel_instAsyncReadOfInhabited___redArg___lam__1(v___f_10823_, v_x_10824_);
    return v_res_10826_;
}
pub unsafe fn l_Std_Channel_instAsyncReadOfInhabited___redArg___lam__2(
    mut v_inst_10827_: *mut LeanObject,
    mut v___f_10828_: *mut LeanObject,
    mut v_receiver_10829_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_10831_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_10832_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_10833_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_10834_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_10835_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_10836_: u8 = 0;
    let mut v___x_10837_: *mut LeanObject = core::ptr::null_mut();
    v___x_10831_ = l_Std_Channel_recv___redArg(v_inst_10827_, v_receiver_10829_);
    v___x_10832_ = lean_alloc_ctor(1, 1, (0) as u32);
    lean_ctor_set(v___x_10832_, 0, v___x_10831_);
    v___x_10833_ = lean_alloc_ctor(1, 1, (0) as u32);
    lean_ctor_set(v___x_10833_, 0, v___x_10832_);
    v___x_10834_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_10834_, 0, v___x_10833_);
    v___x_10835_ = lean_unsigned_to_nat(0);
    v___x_10836_ = 0;
    v___x_10837_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(
        lean_box(0),
        lean_box(0),
        v___x_10835_,
        v___x_10836_,
        v___x_10834_,
        v___f_10828_,
    );
    return v___x_10837_;
}
pub unsafe fn l_Std_Channel_instAsyncReadOfInhabited___redArg___lam__2___boxed(
    mut v_inst_10838_: *mut LeanObject,
    mut v___f_10839_: *mut LeanObject,
    mut v_receiver_10840_: *mut LeanObject,
    mut v___y_10841_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_10842_: *mut LeanObject = core::ptr::null_mut();
    v_res_10842_ = l_Std_Channel_instAsyncReadOfInhabited___redArg___lam__2(
        v_inst_10838_,
        v___f_10839_,
        v_receiver_10840_,
    );
    return v_res_10842_;
}
pub unsafe fn l_Std_Channel_instAsyncReadOfInhabited___redArg(
    mut v_inst_10846_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_10847_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_10848_: *mut LeanObject = core::ptr::null_mut();
    v___f_10847_ = l_Std_Channel_instAsyncReadOfInhabited___redArg___closed__1;
    v___f_10848_ = lean_alloc_closure(
        l_Std_Channel_instAsyncReadOfInhabited___redArg___lam__2___boxed as *mut core::ffi::c_void,
        4,
        2,
    );
    lean_closure_set(v___f_10848_, 0, v_inst_10846_);
    lean_closure_set(v___f_10848_, 1, v___f_10847_);
    return v___f_10848_;
}
pub unsafe fn l_Std_Channel_instAsyncReadOfInhabited(
    mut v_00_u03b1_10849_: *mut LeanObject,
    mut v_inst_10850_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_10851_: *mut LeanObject = core::ptr::null_mut();
    v___x_10851_ = l_Std_Channel_instAsyncReadOfInhabited___redArg(v_inst_10850_);
    return v___x_10851_;
}
pub unsafe fn l_Std_Channel_instAsyncWriteOfInhabited___lam__0(
    mut v_a_10852_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_10853_: *mut LeanObject = core::ptr::null_mut();
    v___x_10853_ = lean_alloc_ctor(1, 1, (0) as u32);
    lean_ctor_set(v___x_10853_, 0, v_a_10852_);
    return v___x_10853_;
}
pub unsafe fn l_Std_Channel_instAsyncWriteOfInhabited___lam__1(
    mut v___f_10854_: *mut LeanObject,
    mut v_x_10855_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_10857_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_10859_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_10860_: u8 = 0;
    let mut v___x_10862_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_10863_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_10864_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_10865_: u8 = 0;
    let mut v_a_10866_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_10867_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_10868_: u8 = 0;
    let mut v___x_10869_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_10870_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_10855_) == 0 {
                    lean_dec_ref(v___f_10854_);
                    v_a_10857_ = lean_ctor_get(v_x_10855_, 0);
                    v_isSharedCheck_10865_ = (!lean_is_exclusive(v_x_10855_)) as u8;
                    if v_isSharedCheck_10865_ == 0 {
                        v___x_10859_ = v_x_10855_;
                        v_isShared_10860_ = v_isSharedCheck_10865_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_10857_);
                        lean_dec(v_x_10855_);
                        v___x_10859_ = lean_box(0);
                        v_isShared_10860_ = v_isSharedCheck_10865_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_10866_ = lean_ctor_get(v_x_10855_, 0);
                    lean_inc(v_a_10866_);
                    lean_dec_ref_known(v_x_10855_, 1);
                    v___x_10867_ = lean_unsigned_to_nat(0);
                    v___x_10868_ = 0;
                    v___x_10869_ =
                        lean_task_map(v___f_10854_, v_a_10866_, v___x_10867_, v___x_10868_);
                    v___x_10870_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v___x_10870_, 0, v___x_10869_);
                    return v___x_10870_;
                }
            }
            1 => {
                if v_isShared_10860_ == 0 {
                    v___x_10862_ = v___x_10859_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_10864_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_10864_, 0, v_a_10857_);
                    v___x_10862_ = v_reuseFailAlloc_10864_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_10863_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_10863_, 0, v___x_10862_);
                return v___x_10863_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Channel_instAsyncWriteOfInhabited___lam__1___boxed(
    mut v___f_10871_: *mut LeanObject,
    mut v_x_10872_: *mut LeanObject,
    mut v___y_10873_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_10874_: *mut LeanObject = core::ptr::null_mut();
    v_res_10874_ = l_Std_Channel_instAsyncWriteOfInhabited___lam__1(v___f_10871_, v_x_10872_);
    return v_res_10874_;
}
pub unsafe fn l_Std_Channel_instAsyncWriteOfInhabited___lam__2(
    mut v___f_10875_: *mut LeanObject,
    mut v_receiver_10876_: *mut LeanObject,
    mut v_x_10877_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_10879_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_10880_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_10881_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_10882_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_10883_: u8 = 0;
    let mut v___x_10884_: *mut LeanObject = core::ptr::null_mut();
    v___x_10879_ = l_Std_Channel_send___redArg(v_receiver_10876_, v_x_10877_);
    v___x_10880_ = lean_alloc_ctor(1, 1, (0) as u32);
    lean_ctor_set(v___x_10880_, 0, v___x_10879_);
    v___x_10881_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_10881_, 0, v___x_10880_);
    v___x_10882_ = lean_unsigned_to_nat(0);
    v___x_10883_ = 0;
    v___x_10884_ = l___private_Std_Async_Basic_0__Std_Async_BaseAsync_bind_bindAsyncTask(
        lean_box(0),
        lean_box(0),
        v___x_10882_,
        v___x_10883_,
        v___x_10881_,
        v___f_10875_,
    );
    return v___x_10884_;
}
pub unsafe fn l_Std_Channel_instAsyncWriteOfInhabited___lam__2___boxed(
    mut v___f_10885_: *mut LeanObject,
    mut v_receiver_10886_: *mut LeanObject,
    mut v_x_10887_: *mut LeanObject,
    mut v___y_10888_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_10889_: *mut LeanObject = core::ptr::null_mut();
    v_res_10889_ = l_Std_Channel_instAsyncWriteOfInhabited___lam__2(
        v___f_10885_,
        v_receiver_10886_,
        v_x_10887_,
    );
    return v_res_10889_;
}
pub unsafe fn _init_l_Std_Channel_instAsyncWriteOfInhabited___closed__3() -> *mut LeanObject {
    let mut v___x_10895_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_10896_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_10897_: *mut LeanObject = core::ptr::null_mut();
    v___x_10895_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_CloseableChannel_instAsyncWriteOfInhabited___closed__3),
        core::ptr::addr_of_mut!(l_Std_CloseableChannel_instAsyncWriteOfInhabited___closed__3_once),
        _init_l_Std_CloseableChannel_instAsyncWriteOfInhabited___closed__3,
    );
    v___f_10896_ = l_Std_Channel_instAsyncWriteOfInhabited___closed__2;
    v___f_10897_ = lean_alloc_closure(
        l_Std_CloseableChannel_instAsyncWriteOfInhabited___lam__4___boxed as *mut core::ffi::c_void,
        5,
        2,
    );
    lean_closure_set(v___f_10897_, 0, v___f_10896_);
    lean_closure_set(v___f_10897_, 1, v___x_10895_);
    return v___f_10897_;
}
pub unsafe fn _init_l_Std_Channel_instAsyncWriteOfInhabited___closed__4() -> *mut LeanObject {
    let mut v___f_10898_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_10899_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_10900_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_10901_: *mut LeanObject = core::ptr::null_mut();
    v___f_10898_ = l_Std_CloseableChannel_instAsyncWriteOfInhabited___closed__2;
    v___f_10899_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Channel_instAsyncWriteOfInhabited___closed__3),
        core::ptr::addr_of_mut!(l_Std_Channel_instAsyncWriteOfInhabited___closed__3_once),
        _init_l_Std_Channel_instAsyncWriteOfInhabited___closed__3,
    );
    v___f_10900_ = l_Std_Channel_instAsyncWriteOfInhabited___closed__2;
    v___x_10901_ = lean_alloc_ctor(0, 3, (0) as u32);
    lean_ctor_set(v___x_10901_, 0, v___f_10900_);
    lean_ctor_set(v___x_10901_, 1, v___f_10899_);
    lean_ctor_set(v___x_10901_, 2, v___f_10898_);
    return v___x_10901_;
}
pub unsafe fn l_Std_Channel_instAsyncWriteOfInhabited(
    mut v_00_u03b1_10902_: *mut LeanObject,
    mut v_inst_10903_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_10904_: *mut LeanObject = core::ptr::null_mut();
    v___x_10904_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Channel_instAsyncWriteOfInhabited___closed__4),
        core::ptr::addr_of_mut!(l_Std_Channel_instAsyncWriteOfInhabited___closed__4_once),
        _init_l_Std_Channel_instAsyncWriteOfInhabited___closed__4,
    );
    return v___x_10904_;
}
pub unsafe fn l_Std_Channel_instAsyncWriteOfInhabited___boxed(
    mut v_00_u03b1_10905_: *mut LeanObject,
    mut v_inst_10906_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_10907_: *mut LeanObject = core::ptr::null_mut();
    v_res_10907_ = l_Std_Channel_instAsyncWriteOfInhabited(v_00_u03b1_10905_, v_inst_10906_);
    lean_dec(v_inst_10906_);
    return v_res_10907_;
}
pub unsafe fn l_Std_Channel_sync___redArg(mut v_ch_10908_: *mut LeanObject) -> *mut LeanObject {
    lean_inc_ref(v_ch_10908_);
    return v_ch_10908_;
}
pub unsafe fn l_Std_Channel_sync___redArg___boxed(
    mut v_ch_10909_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_10910_: *mut LeanObject = core::ptr::null_mut();
    v_res_10910_ = l_Std_Channel_sync___redArg(v_ch_10909_);
    lean_dec_ref(v_ch_10909_);
    return v_res_10910_;
}
pub unsafe fn l_Std_Channel_sync(
    mut v_00_u03b1_10911_: *mut LeanObject,
    mut v_ch_10912_: *mut LeanObject,
) -> *mut LeanObject {
    lean_inc_ref(v_ch_10912_);
    return v_ch_10912_;
}
pub unsafe fn l_Std_Channel_sync___boxed(
    mut v_00_u03b1_10913_: *mut LeanObject,
    mut v_ch_10914_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_10915_: *mut LeanObject = core::ptr::null_mut();
    v_res_10915_ = l_Std_Channel_sync(v_00_u03b1_10913_, v_ch_10914_);
    lean_dec_ref(v_ch_10914_);
    return v_res_10915_;
}
pub unsafe fn l_Std_Channel_Sync_new___redArg(
    mut v_capacity_10916_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_10918_: *mut LeanObject = core::ptr::null_mut();
    v___x_10918_ = l_Std_CloseableChannel_new___redArg(v_capacity_10916_);
    return v___x_10918_;
}
pub unsafe fn l_Std_Channel_Sync_new___redArg___boxed(
    mut v_capacity_10919_: *mut LeanObject,
    mut v_a_10920_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_10921_: *mut LeanObject = core::ptr::null_mut();
    v_res_10921_ = l_Std_Channel_Sync_new___redArg(v_capacity_10919_);
    return v_res_10921_;
}
pub unsafe fn l_Std_Channel_Sync_new(
    mut v_00_u03b1_10922_: *mut LeanObject,
    mut v_capacity_10923_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_10925_: *mut LeanObject = core::ptr::null_mut();
    v___x_10925_ = l_Std_CloseableChannel_new___redArg(v_capacity_10923_);
    return v___x_10925_;
}
pub unsafe fn l_Std_Channel_Sync_new___boxed(
    mut v_00_u03b1_10926_: *mut LeanObject,
    mut v_capacity_10927_: *mut LeanObject,
    mut v_a_10928_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_10929_: *mut LeanObject = core::ptr::null_mut();
    v_res_10929_ = l_Std_Channel_Sync_new(v_00_u03b1_10926_, v_capacity_10927_);
    return v_res_10929_;
}
pub unsafe fn l_Std_Channel_Sync_trySend___redArg(
    mut v_ch_10930_: *mut LeanObject,
    mut v_v_10931_: *mut LeanObject,
) -> u8 {
    let mut v___x_10933_: u8 = 0;
    v___x_10933_ = l_Std_CloseableChannel_trySend___redArg(v_ch_10930_, v_v_10931_);
    return v___x_10933_;
}
pub unsafe fn l_Std_Channel_Sync_trySend___redArg___boxed(
    mut v_ch_10934_: *mut LeanObject,
    mut v_v_10935_: *mut LeanObject,
    mut v_a_10936_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_10937_: u8 = 0;
    let mut v_r_10938_: *mut LeanObject = core::ptr::null_mut();
    v_res_10937_ = l_Std_Channel_Sync_trySend___redArg(v_ch_10934_, v_v_10935_);
    v_r_10938_ = lean_box((v_res_10937_) as usize);
    return v_r_10938_;
}
pub unsafe fn l_Std_Channel_Sync_trySend(
    mut v_00_u03b1_10939_: *mut LeanObject,
    mut v_ch_10940_: *mut LeanObject,
    mut v_v_10941_: *mut LeanObject,
) -> u8 {
    let mut v___x_10943_: u8 = 0;
    v___x_10943_ = l_Std_CloseableChannel_trySend___redArg(v_ch_10940_, v_v_10941_);
    return v___x_10943_;
}
pub unsafe fn l_Std_Channel_Sync_trySend___boxed(
    mut v_00_u03b1_10944_: *mut LeanObject,
    mut v_ch_10945_: *mut LeanObject,
    mut v_v_10946_: *mut LeanObject,
    mut v_a_10947_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_10948_: u8 = 0;
    let mut v_r_10949_: *mut LeanObject = core::ptr::null_mut();
    v_res_10948_ = l_Std_Channel_Sync_trySend(v_00_u03b1_10944_, v_ch_10945_, v_v_10946_);
    v_r_10949_ = lean_box((v_res_10948_) as usize);
    return v_r_10949_;
}
pub unsafe fn l_Std_Channel_Sync_send___redArg(
    mut v_ch_10950_: *mut LeanObject,
    mut v_v_10951_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_10953_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_10954_: *mut LeanObject = core::ptr::null_mut();
    v___x_10953_ = l_Std_Channel_send___redArg(v_ch_10950_, v_v_10951_);
    v___x_10954_ = lean_io_wait(v___x_10953_);
    return v___x_10954_;
}
pub unsafe fn l_Std_Channel_Sync_send___redArg___boxed(
    mut v_ch_10955_: *mut LeanObject,
    mut v_v_10956_: *mut LeanObject,
    mut v_a_10957_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_10958_: *mut LeanObject = core::ptr::null_mut();
    v_res_10958_ = l_Std_Channel_Sync_send___redArg(v_ch_10955_, v_v_10956_);
    return v_res_10958_;
}
pub unsafe fn l_Std_Channel_Sync_send(
    mut v_00_u03b1_10959_: *mut LeanObject,
    mut v_ch_10960_: *mut LeanObject,
    mut v_v_10961_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_10963_: *mut LeanObject = core::ptr::null_mut();
    v___x_10963_ = l_Std_Channel_Sync_send___redArg(v_ch_10960_, v_v_10961_);
    return v___x_10963_;
}
pub unsafe fn l_Std_Channel_Sync_send___boxed(
    mut v_00_u03b1_10964_: *mut LeanObject,
    mut v_ch_10965_: *mut LeanObject,
    mut v_v_10966_: *mut LeanObject,
    mut v_a_10967_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_10968_: *mut LeanObject = core::ptr::null_mut();
    v_res_10968_ = l_Std_Channel_Sync_send(v_00_u03b1_10964_, v_ch_10965_, v_v_10966_);
    return v_res_10968_;
}
pub unsafe fn l_Std_Channel_Sync_tryRecv___redArg(
    mut v_ch_10969_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_10971_: *mut LeanObject = core::ptr::null_mut();
    v___x_10971_ = l_Std_CloseableChannel_tryRecv___redArg(v_ch_10969_);
    return v___x_10971_;
}
pub unsafe fn l_Std_Channel_Sync_tryRecv___redArg___boxed(
    mut v_ch_10972_: *mut LeanObject,
    mut v_a_10973_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_10974_: *mut LeanObject = core::ptr::null_mut();
    v_res_10974_ = l_Std_Channel_Sync_tryRecv___redArg(v_ch_10972_);
    return v_res_10974_;
}
pub unsafe fn l_Std_Channel_Sync_tryRecv(
    mut v_00_u03b1_10975_: *mut LeanObject,
    mut v_ch_10976_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_10978_: *mut LeanObject = core::ptr::null_mut();
    v___x_10978_ = l_Std_CloseableChannel_tryRecv___redArg(v_ch_10976_);
    return v___x_10978_;
}
pub unsafe fn l_Std_Channel_Sync_tryRecv___boxed(
    mut v_00_u03b1_10979_: *mut LeanObject,
    mut v_ch_10980_: *mut LeanObject,
    mut v_a_10981_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_10982_: *mut LeanObject = core::ptr::null_mut();
    v_res_10982_ = l_Std_Channel_Sync_tryRecv(v_00_u03b1_10979_, v_ch_10980_);
    return v_res_10982_;
}
pub unsafe fn l_Std_Channel_Sync_recv___redArg(
    mut v_inst_10983_: *mut LeanObject,
    mut v_ch_10984_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_10986_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_10987_: *mut LeanObject = core::ptr::null_mut();
    v___x_10986_ = l_Std_Channel_recv___redArg(v_inst_10983_, v_ch_10984_);
    v___x_10987_ = lean_io_wait(v___x_10986_);
    return v___x_10987_;
}
pub unsafe fn l_Std_Channel_Sync_recv___redArg___boxed(
    mut v_inst_10988_: *mut LeanObject,
    mut v_ch_10989_: *mut LeanObject,
    mut v_a_10990_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_10991_: *mut LeanObject = core::ptr::null_mut();
    v_res_10991_ = l_Std_Channel_Sync_recv___redArg(v_inst_10988_, v_ch_10989_);
    return v_res_10991_;
}
pub unsafe fn l_Std_Channel_Sync_recv(
    mut v_00_u03b1_10992_: *mut LeanObject,
    mut v_inst_10993_: *mut LeanObject,
    mut v_ch_10994_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_10996_: *mut LeanObject = core::ptr::null_mut();
    v___x_10996_ = l_Std_Channel_Sync_recv___redArg(v_inst_10993_, v_ch_10994_);
    return v___x_10996_;
}
pub unsafe fn l_Std_Channel_Sync_recv___boxed(
    mut v_00_u03b1_10997_: *mut LeanObject,
    mut v_inst_10998_: *mut LeanObject,
    mut v_ch_10999_: *mut LeanObject,
    mut v_a_11000_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_11001_: *mut LeanObject = core::ptr::null_mut();
    v_res_11001_ = l_Std_Channel_Sync_recv(v_00_u03b1_10997_, v_inst_10998_, v_ch_10999_);
    return v_res_11001_;
}
pub unsafe fn l___private_Std_Sync_Channel_0__Std_Channel_Sync_forIn___redArg___lam__1(
    mut v_f_11002_: *mut LeanObject,
    mut v_b_11003_: *mut LeanObject,
    mut v_toBind_11004_: *mut LeanObject,
    mut v___f_11005_: *mut LeanObject,
    mut v_a_11006_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_11007_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_11008_: *mut LeanObject = core::ptr::null_mut();
    v___x_11007_ = lean_apply_2(v_f_11002_, v_a_11006_, v_b_11003_);
    v___x_11008_ = lean_apply_4(
        v_toBind_11004_,
        lean_box(0),
        lean_box(0),
        v___x_11007_,
        v___f_11005_,
    );
    return v___x_11008_;
}
pub unsafe fn l___private_Std_Sync_Channel_0__Std_Channel_Sync_forIn___redArg(
    mut v_inst_11009_: *mut LeanObject,
    mut v_inst_11010_: *mut LeanObject,
    mut v_inst_11011_: *mut LeanObject,
    mut v_ch_11012_: *mut LeanObject,
    mut v_f_11013_: *mut LeanObject,
    mut v_b_11014_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toApplicative_11015_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toBind_11016_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toPure_11017_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_11018_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_11019_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_11020_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_11021_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_11022_: *mut LeanObject = core::ptr::null_mut();
    v_toApplicative_11015_ = lean_ctor_get(v_inst_11010_, 0);
    v_toBind_11016_ = lean_ctor_get(v_inst_11010_, 1);
    lean_inc_n(v_toBind_11016_, 2);
    v_toPure_11017_ = lean_ctor_get(v_toApplicative_11015_, 1);
    lean_inc(v_toPure_11017_);
    lean_inc_ref(v_ch_11012_);
    lean_inc(v_inst_11009_);
    v___x_11018_ = lean_alloc_closure(
        l_Std_Channel_Sync_recv___boxed as *mut core::ffi::c_void,
        4,
        3,
    );
    lean_closure_set(v___x_11018_, 0, lean_box(0));
    lean_closure_set(v___x_11018_, 1, v_inst_11009_);
    lean_closure_set(v___x_11018_, 2, v_ch_11012_);
    lean_inc(v_inst_11011_);
    v___x_11019_ = lean_apply_2(v_inst_11011_, lean_box(0), v___x_11018_);
    lean_inc(v_f_11013_);
    v___f_11020_ = lean_alloc_closure(
        l___private_Std_Sync_Channel_0__Std_Channel_Sync_forIn___redArg___lam__0
            as *mut core::ffi::c_void,
        7,
        6,
    );
    lean_closure_set(v___f_11020_, 0, v_toPure_11017_);
    lean_closure_set(v___f_11020_, 1, v_inst_11009_);
    lean_closure_set(v___f_11020_, 2, v_inst_11010_);
    lean_closure_set(v___f_11020_, 3, v_inst_11011_);
    lean_closure_set(v___f_11020_, 4, v_ch_11012_);
    lean_closure_set(v___f_11020_, 5, v_f_11013_);
    v___f_11021_ = lean_alloc_closure(
        l___private_Std_Sync_Channel_0__Std_Channel_Sync_forIn___redArg___lam__1
            as *mut core::ffi::c_void,
        5,
        4,
    );
    lean_closure_set(v___f_11021_, 0, v_f_11013_);
    lean_closure_set(v___f_11021_, 1, v_b_11014_);
    lean_closure_set(v___f_11021_, 2, v_toBind_11016_);
    lean_closure_set(v___f_11021_, 3, v___f_11020_);
    v___x_11022_ = lean_apply_4(
        v_toBind_11016_,
        lean_box(0),
        lean_box(0),
        v___x_11019_,
        v___f_11021_,
    );
    return v___x_11022_;
}
pub unsafe fn l___private_Std_Sync_Channel_0__Std_Channel_Sync_forIn___redArg___lam__0(
    mut v_toPure_11023_: *mut LeanObject,
    mut v_inst_11024_: *mut LeanObject,
    mut v_inst_11025_: *mut LeanObject,
    mut v_inst_11026_: *mut LeanObject,
    mut v_ch_11027_: *mut LeanObject,
    mut v_f_11028_: *mut LeanObject,
    mut v_____do__lift_11029_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_____do__lift_11029_) == 0 {
        let mut v_a_11030_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_11031_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_f_11028_);
        lean_dec_ref(v_ch_11027_);
        lean_dec(v_inst_11026_);
        lean_dec_ref(v_inst_11025_);
        lean_dec(v_inst_11024_);
        v_a_11030_ = lean_ctor_get(v_____do__lift_11029_, 0);
        lean_inc(v_a_11030_);
        lean_dec_ref_known(v_____do__lift_11029_, 1);
        v___x_11031_ = lean_apply_2(v_toPure_11023_, lean_box(0), v_a_11030_);
        return v___x_11031_;
    } else {
        let mut v_a_11032_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_11033_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_toPure_11023_);
        v_a_11032_ = lean_ctor_get(v_____do__lift_11029_, 0);
        lean_inc(v_a_11032_);
        lean_dec_ref_known(v_____do__lift_11029_, 1);
        v___x_11033_ = l___private_Std_Sync_Channel_0__Std_Channel_Sync_forIn___redArg(
            v_inst_11024_,
            v_inst_11025_,
            v_inst_11026_,
            v_ch_11027_,
            v_f_11028_,
            v_a_11032_,
        );
        return v___x_11033_;
    }
}
pub unsafe fn l___private_Std_Sync_Channel_0__Std_Channel_Sync_forIn(
    mut v_00_u03b1_11034_: *mut LeanObject,
    mut v_m_11035_: *mut LeanObject,
    mut v_00_u03b2_11036_: *mut LeanObject,
    mut v_inst_11037_: *mut LeanObject,
    mut v_inst_11038_: *mut LeanObject,
    mut v_inst_11039_: *mut LeanObject,
    mut v_ch_11040_: *mut LeanObject,
    mut v_f_11041_: *mut LeanObject,
    mut v_b_11042_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_11043_: *mut LeanObject = core::ptr::null_mut();
    v___x_11043_ = l___private_Std_Sync_Channel_0__Std_Channel_Sync_forIn___redArg(
        v_inst_11037_,
        v_inst_11038_,
        v_inst_11039_,
        v_ch_11040_,
        v_f_11041_,
        v_b_11042_,
    );
    return v___x_11043_;
}
pub unsafe fn l_Std_Channel_Sync_instForInOfInhabitedOfMonadOfMonadLiftTBaseIO___private__1___redArg(
    mut v_inst_11044_: *mut LeanObject,
    mut v_inst_11045_: *mut LeanObject,
    mut v_inst_11046_: *mut LeanObject,
    mut v_ch_11047_: *mut LeanObject,
    mut v_b_11048_: *mut LeanObject,
    mut v_f_11049_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_11050_: *mut LeanObject = core::ptr::null_mut();
    v___x_11050_ = l___private_Std_Sync_Channel_0__Std_Channel_Sync_forIn___redArg(
        v_inst_11044_,
        v_inst_11045_,
        v_inst_11046_,
        v_ch_11047_,
        v_f_11049_,
        v_b_11048_,
    );
    return v___x_11050_;
}
pub unsafe fn l_Std_Channel_Sync_instForInOfInhabitedOfMonadOfMonadLiftTBaseIO___private__1(
    mut v_00_u03b1_11051_: *mut LeanObject,
    mut v_m_11052_: *mut LeanObject,
    mut v_inst_11053_: *mut LeanObject,
    mut v_inst_11054_: *mut LeanObject,
    mut v_inst_11055_: *mut LeanObject,
    mut v_00_u03b2_11056_: *mut LeanObject,
    mut v_ch_11057_: *mut LeanObject,
    mut v_b_11058_: *mut LeanObject,
    mut v_f_11059_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_11060_: *mut LeanObject = core::ptr::null_mut();
    v___x_11060_ = l___private_Std_Sync_Channel_0__Std_Channel_Sync_forIn___redArg(
        v_inst_11053_,
        v_inst_11054_,
        v_inst_11055_,
        v_ch_11057_,
        v_f_11059_,
        v_b_11058_,
    );
    return v___x_11060_;
}
pub unsafe fn l_Std_Channel_Sync_instForInOfInhabitedOfMonadOfMonadLiftTBaseIO___redArg___lam__0(
    mut v_inst_11061_: *mut LeanObject,
    mut v_inst_11062_: *mut LeanObject,
    mut v_inst_11063_: *mut LeanObject,
    mut v_00_u03b2_11064_: *mut LeanObject,
    mut v_ch_11065_: *mut LeanObject,
    mut v_b_11066_: *mut LeanObject,
    mut v_f_11067_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_11068_: *mut LeanObject = core::ptr::null_mut();
    v___x_11068_ = l___private_Std_Sync_Channel_0__Std_Channel_Sync_forIn___redArg(
        v_inst_11061_,
        v_inst_11062_,
        v_inst_11063_,
        v_ch_11065_,
        v_f_11067_,
        v_b_11066_,
    );
    return v___x_11068_;
}
pub unsafe fn l_Std_Channel_Sync_instForInOfInhabitedOfMonadOfMonadLiftTBaseIO___redArg(
    mut v_inst_11069_: *mut LeanObject,
    mut v_inst_11070_: *mut LeanObject,
    mut v_inst_11071_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_11072_: *mut LeanObject = core::ptr::null_mut();
    v___f_11072_ = lean_alloc_closure(
        l_Std_Channel_Sync_instForInOfInhabitedOfMonadOfMonadLiftTBaseIO___redArg___lam__0
            as *mut core::ffi::c_void,
        7,
        3,
    );
    lean_closure_set(v___f_11072_, 0, v_inst_11069_);
    lean_closure_set(v___f_11072_, 1, v_inst_11070_);
    lean_closure_set(v___f_11072_, 2, v_inst_11071_);
    return v___f_11072_;
}
pub unsafe fn l_Std_Channel_Sync_instForInOfInhabitedOfMonadOfMonadLiftTBaseIO(
    mut v_00_u03b1_11073_: *mut LeanObject,
    mut v_m_11074_: *mut LeanObject,
    mut v_inst_11075_: *mut LeanObject,
    mut v_inst_11076_: *mut LeanObject,
    mut v_inst_11077_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_11078_: *mut LeanObject = core::ptr::null_mut();
    v___f_11078_ = lean_alloc_closure(
        l_Std_Channel_Sync_instForInOfInhabitedOfMonadOfMonadLiftTBaseIO___redArg___lam__0
            as *mut core::ffi::c_void,
        7,
        3,
    );
    lean_closure_set(v___f_11078_, 0, v_inst_11075_);
    lean_closure_set(v___f_11078_, 1, v_inst_11076_);
    lean_closure_set(v___f_11078_, 2, v_inst_11077_);
    return v___f_11078_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Std_Sync_Channel(builtin: u8) -> *mut LeanObject {
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
    res = runtime_initialize_Std_Async_IO(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Vector_Basic(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Option_BasicAux(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Omega(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Std_Sync_Channel(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_meta_initialized = true;
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Std_Sync_Channel(builtin: u8) -> *mut LeanObject {
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
    res = initialize_Std_Async_IO(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Data_Vector_Basic(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Data_Option_BasicAux(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Omega(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Std_Sync_Channel(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Std_Sync_Channel(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Std_Sync_Channel(builtin);
}
